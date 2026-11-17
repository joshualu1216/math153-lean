---
module: 6
title: Week 8 Homework
week: 8
audience: students
---

# Week 8 Homework

The Week 8 exercises that we do not do in class. Exercises 1, 3, 5 and 6 are in the [Week 8 In-class Practice](06-Week-8-In-class-Practice.md). Each exercise names the section of the [Week 8 Student Handout](06-Week-8-Student-Handout.md) it practises.

Each exercise asks for a **proof in words** and a **Lean proof**. Write the proof in words first, one step per line. It may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`2.1`, `2.2`, `4`). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 2: Week 7 again, with `simp`

*Handout section: 1. The `simp` family*

Prove both statements from Week 7 again, this time with the `simp` family.

**2.1** If it is not true that $P(x)$ holds for every $x$, then there is an $x$ for which $P(x)$ fails. (Hint: `simp at h`.)

  因為不是對於所有都成立，所以一定存在一個不成立。

**2.2** At least one of "if $P$ then $Q$" and "if $Q$ then $P$" holds. (Hint: first split on whether $Q$ holds.)

一兆Q是否成立分兩種。如果Q成立，則若P則Q成立。如果Q不成立，若Q則P成立。

```lean
example {α : Type} (P : α → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  simp at h
  exact h

example (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  by_cases hQ : Q
  · simp [hQ]
  · simp [hQ]
```

- Then replace `simp` by `simp?` and look at the lemmas it reports. Pick one lemma and explain in one sentence what it says. If it is one of the negation rules from Week 7, say which one.

---

## Exercise 4: Powers of 4

*Handout section: 2. Induction*

Prove: for every natural number $n$, $4^n$ leaves remainder $1$ when divided by $3$; that is, there is an $m$ with $4^n=3m+1$. Write the proof in words first, then the Lean.

- Hint: $P(n)$ is an "exists". In the step, `obtain` the $m$ with $4^k=3m+1$, then `use` the number that works for $4^{k+1}$.


對n做數學歸納。
n=0: 取m=0，4^0=1=3*0+1。
假設 P(k): 取出m使4^k=3m+1。
則 P(k+1): 4^{k+1}=4*4^k=4(3m+1)=12m+4=3(4m+1)+1。
取 m'=4m+1，4^{k+1}=3m'+1

```lean
example (n : ℕ) : ∃ m, 4 ^ n = 3 * m + 1 := by
  induction n with
  | zero => exact ⟨0, by norm_num⟩                     -- base case: m = 0
  | succ k IH =>                                       -- IH : ∃ m, 4 ^ k = 3 * m + 1
    obtain ⟨m, hm⟩ := IH                               -- hm : 4 ^ k = 3 * m + 1
    use 4 * m + 1                                      -- the number that works for 4^(k+1)
    calc 4 ^ (k + 1) = 4 * 4 ^ k := by ring
      _ = 4 * (3 * m + 1) := by rw [hm]                -- by the inductive hypothesis
      _ = 3 * (4 * m + 1) + 1 := by ring
```
