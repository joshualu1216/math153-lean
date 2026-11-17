---
module: 6
title: Week 8 In-class Practice
week: 8
audience: students
---

# Week 8 In-class Practice

The exercises we do in class: Exercise 1, Exercise 3, Exercise 5 and Exercise 6. The rest are in the [Week 8 Homework](06-Week-8-Homework.md). Each exercise names the section of the [Week 8 Student Handout](06-Week-8-Student-Handout.md) it practises.

For Exercises 1 and 3, write the proof in words first, then the Lean. For Exercises 5 and 6, write only the proof in words. Proofs in words may be in Chinese or English; write them one step per line.

Hand in one `.md` file. Label each answer with its number (`1`, `3`, `5`, `6`). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: Knights and knaves

*Handout section: 1. The `simp` family*

On an island, knights always tell the truth and knaves always lie. A says "B is a knave". B says "C is a knave". C says "A and B are both knaves". Prove: A is a knave, B is a knight, and C is a knave. Write the proof in words first, then the Lean.

先分成兩種情況，A和非A，然後再依次往後推理，發現A成立的前提矛盾。在非A的情況下，推倒發現他會是對的。
- In Lean, `A` means "A is a knight". What A says is true exactly when A is a knight, so A's statement becomes `hA : A ↔ ¬ B`.
- Hint: first split on A (`by_cases`). Then use `simp [ha] at hA` to substitute what you know into the other hypotheses, one at a time.
- Also try plain `simp_all` and see what happens.

```lean
example (A B C : Prop) (hA : A ↔ ¬ B) (hB : B ↔ ¬ C) (hC : C ↔ (¬ A ∧ ¬ B)) :
    ¬ A ∧ B ∧ ¬ C := by
    by_cases ha : A
    · simp [ha] at hA
      simp [hA] at hB
      simp [hB] at hC
      obtain ⟨CA, CB⟩ := hC
      by_contra h
      exact CA ha
    · simp [ha] at hA
      simp [hA] at hB
      simp [hB] at hC
      exact ⟨ha, hA, hB⟩
```

---

## Exercise 3: A geometric sum

*Handout section: 2. Induction*

Let $G_0=1$ and $G_{n+1}=G_n+2^{n+1}$, so $G_n=1+2+4+\cdots+2^n$. Prove: $G_n+1=2^{n+1}$. Write the proof in words first, then the Lean.


用G_n表示G_(n+1)，然後整理出G_(n+1)= 2 ^ (n+2)
- Hint: the target of the step is $G_{k+1}+1=2^{k+2}$. First rearrange the left side so that $G_k+1$ appears; only then can you use the inductive hypothesis.

```lean
example (n : ℕ) : G n + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero =>
    simp [G]
  | succ n ih =>
    simp [G, ih]
    calc
      G (n + 1) +1 = G n + 2 ^ (n + 1) + 1:= by rw [G]
     _= G n + 1 + 2 ^ (n + 1) := by ring
      _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
      _ = 2 * 2 ^ (n + 1) := by ring
      _ = 2 ^ (n + 2) := by ring
```

---

## Exercise 5: Stamps of 3 and 5

*Handout section: 3. Strong induction*

There are only 3-stamps and 5-stamps. The code below proves that every amount of at least 8 can be paid. Read it, then write its proof in words, in your own words.

If 8 ≤ n < 11, 
if n = 8, n = 3 * 1 + 5 * 1
if n = 9, n = 3 * 3 + 5 * 0
if n = 10, n = 3 * 0 + 5 * 2

if n ≥ 11 and n - 3 = 3 * a + 5 * b
than n = 3 * (a+1) + 5 * b

- `interval_cases n` splits $8\le n\le 10$ into the cases $n=8,9,10$.

```lean
theorem stamps (n : ℕ) : 8 ≤ n → ∃ a b, n = 3 * a + 5 * b := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    by_cases h : n ≤ 10
    · interval_cases n
      · exact ⟨1, 1, rfl⟩
      · exact ⟨3, 0, rfl⟩
      · exact ⟨0, 2, rfl⟩
    · have h11 : 11 ≤ n := not_le.mp h
      have hlt : n - 3 < n := Nat.sub_lt (lt_of_lt_of_le (by norm_num) h11) (by norm_num)
      have h8 : 8 ≤ n - 3 := Nat.le_sub_of_add_le h11
      obtain ⟨a, b, hab⟩ := IH (n - 3) hlt h8
      have h3 : n - 3 + 3 = n := Nat.sub_add_cancel (le_trans (by norm_num) h11)
      exact ⟨a + 1, b, by rw [← h3, hab]; ring⟩
```

---

## Exercise 6: Division by 5

*Handout section: 3. Strong induction*

The code below proves that every natural number $n$ can be written as $n=5q+r$ with $0\le r<5$ (the quotient and remainder when dividing by 5). Read it, then write its proof in words, in your own words.

如果n < 5, n = 1, 2, 3, 4, 5，r = 1, 2, 3, 4, 5，respectively.
如果n ≥ 5 :
if n = 5q + r
than n + 5 = 5(q+1) +r

```lean
theorem div5 (n : ℕ) : ∃ q r, r < 5 ∧ n = 5 * q + r := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    by_cases h : n < 5
    · exact ⟨0, n, h, by ring⟩
    · have h5 : 5 ≤ n := not_lt.mp h
      have hlt : n - 5 < n := Nat.sub_lt (lt_of_lt_of_le (by norm_num) h5) (by norm_num)
      obtain ⟨q, r, hr, hqr⟩ := IH (n - 5) hlt
      have h5' : n - 5 + 5 = n := Nat.sub_add_cancel h5
      exact ⟨q + 1, r, hr, by rw [← h5', hqr]; ring⟩
```


