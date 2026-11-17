---
module: 4
title: Week 5 In-class Practice
week: 5
audience: students
---

# Week 5 In-class Practice

The exercises we do in class: Exercise 2.1, Exercise 3.1, Exercise 4.1 and Exercise 5. The rest are in the [Week 5 Homework](04-Week-5-Homework.md). Each exercise names the section of the [Week 5 Student Handout](04-Week-5-Student-Handout.md) it practises.

For each exercise, write the proof in words first, then the Lean. The proof in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`2.1`, `3.1 (a)`, `5.2`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 2.1: A limit

*Handout section: 1. For all, "Order of quantifiers: the definition of a limit"*

Recall the definition:

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
```

Prove: if $f(x)=5-2x$ for every real $x$, then $\displaystyle\lim_{x\to 3}f(x)=-1$.

- First write the idea and work out $\delta$. Then write the proof in words and the Lean.
- Lemmas you need:
  - `div_pos : 0 < a → 0 < b → 0 < a / b`
  - `abs_mul a b : |a * b| = |a| * |b|`
  - `mul_lt_mul_of_pos_left : b < c → 0 < a → a * b < a * c`
- To replace the expression inside an absolute value by an equal one, use `congrArg abs (by ring)`.

```lean
example {f : ℝ → ℝ} (hf : ∀ x, f x = 5 - 2 * x) : Limit f 3 (-1) := by
  sorry
```

---

## Exercise 3.1: Negation and quantifiers

*Handout section: 2. Not, "Negation meets quantifiers"*

Let `P` be a property of the elements of a type `α` (`P : α → Prop`). Prove the following two statements of pure logic. Write the proof in words first, then the Lean.

- (a) If there is an $x$ for which $P(x)$ fails, then it is not true that $P(x)$ holds for all $x$.
- (b) If there is no $x$ with $P(x)$, then $P(x)$ fails for every $x$.

```lean
example {α : Type} (P : α → Prop) : (∃ x, ¬ P x) → ¬ ∀ x, P x := by
  sorry

example {α : Type} (P : α → Prop) : (¬ ∃ x, P x) → ∀ x, ¬ P x := by
  sorry
```

- The converse of (a) (from "not for all" to "some fails") is also true, but it needs proof by contradiction twice. It comes next week, in Module 5.

---

## Exercise 4.1: A chain of "if and only if"

*Handout section: 3. If and only if, "Chaining 'if and only if': `calc`"*

Use `calc` to chain: $|x-2|<1$ if and only if $-1<x-2<1$, if and only if $1<x<3$. Write the proof in words first, then the Lean.

- Lemmas you need:
  - `abs_lt : |a| < b ↔ -b < a ∧ a < b`
  - `add_lt_add_left : b < c → ∀ a, b + a < c + a`
  - `sub_lt_sub_right : a < b → ∀ c, a - c < b - c`

```lean
example (x : ℝ) : |x - 2| < 1 ↔ 1 < x ∧ x < 3 := by
  calc
    |x - 2| < 1 ↔ -1 < x - 2 ∧ x - 2 < 1 := by
      sorry
    _ ↔ 1 < x ∧ x < 3 := by
      sorry
```

---

## Exercise 5: Unique existence

*Handout section: 4. Unique existence*

Let `P` be a property of the elements of a type `α` (`P : α → Prop`).

**5.1** Using only `∃`, `∀`, `→`, `∧` and `=`, write the meaning of `∃! x, P x` as a Lean statement.

**5.2** Prove: if there is exactly one $x$ with $P(x)$, then there are no $y\ne z$ that both satisfy $P$. Write the proof in words first, then the Lean.

- Hint: `obtain ⟨x, hx, hu⟩ := h` splits `h` into three things: the witness, its property, and uniqueness. The Infoview will show expressions like `(fun x => P x) y`; this just means `P y`.
- `y ≠ z` is `¬ (y = z)`, so it is an "if … then …".

```lean
example {α : Type} (P : α → Prop) (h : ∃! x, P x) :
    ¬ ∃ y z, P y ∧ P z ∧ y ≠ z := by
  sorry
```
