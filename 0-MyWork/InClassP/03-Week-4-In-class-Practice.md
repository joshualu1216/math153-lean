---
module: 3
title: Week 4 In-class Practice
week: 4
audience: students
---

# Week 4 In-class Practice

The three exercises we do in class: Exercise 3, Exercise 5.1 and Exercise 6.1. The rest are in the [Week 4 Homework](03-Week-4-Homework.md). Each exercise names the section of the [Week 4 Student Handout](03-Week-4-Student-Handout.md) it practises.

For each exercise, write the proof in words first, then the Lean. The proof in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`3.1`, `5.1`, `6.1`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 3: Odd squares

*Handout section: 2. Divisibility and parity*

Recall: `Odd n` means there is `k` with `n = 2 * k + 1`, and `Even n` means there is `r` with `n = r + r`. The lemma `Int.even_or_odd k : Even k ∨ Odd k` says every integer is even or odd.

Prove: if $n$ is odd, then $8\mid n^2-1$.

**3.1** Write the proof in words. Hint: when $n=2k+1$, $n^2-1=4k(k+1)$. To get one more factor of $2$, split into cases on whether $k$ is even or odd.

**3.2** Write it in Lean.

```lean
example {n : ℤ} : Odd n → 8 ∣ n ^ 2 - 1 := by
  sorry
```

---

## Exercise 5.1: Congruences can be multiplied

*Handout section: 3. Congruence*

Recall: to work with a congruence, first turn it into divisibility with `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`. You can rewrite hypotheses and the goal together: `rw [Int.modEq_iff_dvd] at h1 h2 ⊢`.

Prove: if $a\equiv b$ and $c\equiv d\pmod n$, then $ac\equiv bd\pmod n$. Do not use `Int.ModEq.mul`.

- Write the proof in words, then the Lean.
- Hint: write $bd-ac$ as $b(\ldots)+c(\ldots)$, where the two brackets are $d-c$ and $b-a$.

```lean
example {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  sorry
```

---

## Exercise 6.1: Cancelling with Bézout

*Handout section: 4. Coprimality and Bézout*

Prove: if $11\mid 3n$, then $11\mid n$.

- First find integers $x$, $y$ with $3x+11y=1$.
- Then write the proof in words and the Lean.

```lean
example {n : ℤ} : 11 ∣ 3 * n → 11 ∣ n := by
  sorry
```
