---
module: 3
title: Week 4 Homework
week: 4
audience: students
---

# Week 4 Homework

The Week 4 exercises that we do not do in class. Exercises 3, 5.1 and 6.1 are in the [Week 4 In-class Practice](03-Week-4-In-class-Practice.md). Each exercise names the section of the [Week 4 Student Handout](03-Week-4-Student-Handout.md) it practises.

Most exercises ask for a **proof in words** and a **Lean proof**. Write the proof in words first: decide the shape, then translate it. The proof in words may be in Chinese or English. Every lemma you need is named in the exercise or in the handout section it refers to.

Hand in one `.md` file. Label each answer with its number (`1.1`, `2.2`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: If … then …

*Handout section: 0. If … then …*

**1.1** Prove: if (if $P$ then $Q$) and (if $Q$ then $R$), then (if $P$ then $R$). Write the proof in words first, then the Lean.

```lean
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  sorry
```

**1.2** Prove: if (if $P$ and $Q$, then $R$), then (if $P$, then (if $Q$ then $R$)). Write the proof in words first, then the Lean.

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → Q → R) := by
  sorry
```

---

## Exercise 2: Witnesses that are expressions

*Handout section: 1. Definitions: even, divides, congruent*

Recall the Lean definitions: `Odd n` means there is `k` with `n = 2 * k + 1`; `Even n` means there is `r` with `n = r + r`; `a ∣ b` means there is `c` with `b = a * c`. A congruence must first be turned into divisibility with `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`.

**2.1** Prove each of the following three statements, in words and in Lean. A witness need not be a number; it can be an expression.

- Every integer divides $0$.
- If $n$ is odd, then $3n+2$ is odd.
- The two sides of a congruence can be swapped: if $a\equiv b\pmod n$, then $b\equiv a\pmod n$. Hint: turn both the hypothesis and the goal into divisibility first (`at h ⊢`); the goal contains `a - b`, so first use `calc` to write it as `-(b - a)` before you substitute the hypothesis.

```lean
example (a : ℤ) : a ∣ 0 := by
  sorry

example {n : ℤ} : Odd n → Odd (3 * n + 2) := by
  sorry

example {a b n : ℤ} : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] := by
  sorry
```

**2.2** First write each of the two sentences below as a Lean statement (replace the `sorry` after the colon by the statement; write congruence with `[ZMOD 5]`). Then prove them, in words and in Lean.

- If the integers $a$ and $b$ are both odd, then $a+b$ is even.
- If the integers $a$ and $b$ are congruent modulo $5$, then $a^2$ and $b^2$ are congruent modulo $5$. Hint: $b^2-a^2=(b-a)(b+a)$.

```lean
-- first sentence
example {a b : ℤ} : sorry := by
  sorry

-- second sentence
example {a b : ℤ} : sorry := by
  sorry
```

---

## Exercise 4: A divisor is not larger than the number

*Handout section: 2. Divisibility and parity*

Let $a$ and $b$ be natural numbers.

**4.1** Prove: if $b>0$ and $a\mid b$, then $a\le b$. Write the proof in words first, then the Lean.

- Hint: after taking out the witness $k$, split into the cases $k=0$ and $k>0$; the case $k=0$ contradicts $b>0$.
- Lemmas you need: `Nat.eq_zero_or_pos k : k = 0 ∨ k > 0`; `Nat.mul_le_mul_left c : a ≤ b → c * a ≤ c * b` (hand over `c` first, then the proof: `Nat.mul_le_mul_left c h`).
- For natural numbers, `0 < k` is `1 ≤ k`, so you can use it directly as `1 ≤ k`.
- In one of the cases the goal is `a ≤ b`, not `False`. But if a hypothesis works out to be false, `norm_num at` still finishes the case: a contradictory case cannot happen, so there is nothing left to prove.

```lean
example {a b : ℕ} (hb : 0 < b) : a ∣ b → a ≤ b := by
  sorry
```

**4.2** Without the condition $b>0$, the conclusion is false. Give a counterexample $a$, $b$, and prove in Lean that "$a\mid b$" holds and that "$a\le b$" is impossible.

```lean
-- replace each sorry by the statement for your counterexample, then prove it
example : sorry := by
  sorry

example : sorry := by
  sorry
```

---

## Exercise 5.2 and 5.3: Squares modulo 4

*Handout section: 3. Congruence*

Recall: `mod_cases hx : x % 4` splits into four cases, with `hx : x ≡ 0 [ZMOD 4]`, …, `x ≡ 3`. `Int.ModEq.pow m : a ≡ b [ZMOD n] → a ^ m ≡ b ^ m [ZMOD n]`. When both sides are specific numbers, `by rfl` checks a congruence.

**5.2** Prove: for every integer $x$, $x^2\equiv 0$ or $x^2\equiv 1\pmod 4$. Write the proof in words first, then the Lean. In each case, first work out the remainder of $x^2$, then decide which side of the "or" to prove.

```lean
example {x : ℤ} : x ^ 2 ≡ 0 [ZMOD 4] ∨ x ^ 2 ≡ 1 [ZMOD 4] := by
  sorry
```

**5.3** Use 5.2 to explain why no integer that leaves remainder $3$ when divided by $4$ (for example $3$, $7$, $11$) is a sum of two squares (Week 3, Exercise 7). Answer in two or three sentences; no Lean needed.

---

## Exercise 6.2: Combining with Bézout

*Handout section: 4. Coprimality and Bézout*

Prove: if $13\mid 2m$ and $5\mid m$, then $65\mid m$.

- First use the Euclidean algorithm to find one pair of integers $x$, $y$ with $13x+5y=1$. Show every step.
- Note that the hypothesis is $13\mid 2m$. Either route works: first derive $13\mid m$ and then combine; or ask whether your $x$, $y$ can be used directly, and if not, choose another pair (there is more than one).
- Then write the proof in words and the Lean.

```lean
example {m : ℤ} : 13 ∣ 2 * m → 5 ∣ m → 65 ∣ m := by
  sorry
```
