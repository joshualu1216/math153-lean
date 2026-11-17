---
module: 5
title: Week 7 In-class Practice
week: 7
audience: students
---

# Week 7 In-class Practice

The exercises we do in class: Exercise 1, Exercise 3 and Exercise 5. The rest are in the [Week 7 Homework](05-Week-7-Homework.md). Each exercise names the section of the [Week 7 Student Handout](05-Week-7-Student-Handout.md) it practises.

For each exercise, write the proof in words first, then the Lean. The proof in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`1`, `3`, `5.1`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: The derivative of $x^2$

*Handout section: 1. How to prove and use each shape, "Example: the limit of a sum"*

Recall the definition of a limit:

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
```

In calculus, $f$ has derivative $L$ at $a$ when $\displaystyle\lim_{t\to 0}\frac{f(a+t)-f(a)}{t}=L$. With `Limit` this reads:

```lean
def HasDeriv (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Limit (fun t => (f (a + t) - f a) / t) 0 L
```

Prove: if $f(x)=x^2$ for every real $x$, then $f$ has derivative $2a$ at $a$. First write the idea and work out $\delta$. Then write the proof in words and the Lean.

- Hint: simplifying the difference quotient to $2a+t$ needs $t\ne 0$. The condition $0<|t-0|$ is finally useful here. $t\ne 0$ is a negation: prove it as the table says.
- Lemmas you need:
  - `div_eq_iff : c ≠ 0 → (a / c = b ↔ a = b * c)`
  - `congrArg abs : a = b → |a| = |b|` (use it as `congrArg abs (by ring)`)

```lean
example {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2) (a : ℝ) : HasDeriv f a (2 * a) := by
  sorry
```

---

## Exercise 3: From "not for all" to "some fails"

*Handout section: 2. Excluded middle*

Let `P` be a property of the elements of a type `α` (`P : α → Prop`). Prove: if it is not true that $P(x)$ holds for every $x$, then there is an $x$ for which $P(x)$ fails. Write the proof in words first, then the Lean.

- Week 5, Exercise 3.1 proved the other direction. Hint: use proof by contradiction twice. First assume the conclusion fails, then prove that $P(x)$ holds for every $x$.

```lean
example {α : Type} (P : α → Prop) (h : ¬ ∀ x, P x) : ∃ x, ¬ P x := by
  sorry
```

---

## Exercise 5: Disproof

*Handout section: 3. Negation and disproof*

Write the proof in words first (start by writing out, by hand, the negation you are going to prove), then the Lean.

**5.1** Prove: there is no $y>0$ such that $y<x$ for every $x>0$.

```lean
example : ¬ ∃ y : ℝ, y > 0 ∧ ∀ x : ℝ, x > 0 → y < x := by
  sorry
```

**5.2** Suppose $f(x)=0$ for every $x<0$. Prove: $\displaystyle\lim_{x\to 0}f(x)=1$ is false.

- Lemmas you need:
  - `half_pos : 0 < a → 0 < a / 2`
  - `half_lt_self : 0 < a → a / 2 < a`
  - `abs_of_pos : 0 < a → |a| = a`
  - `abs_neg : |-a| = |a|`
  - `sub_zero : a - 0 = a`
  - `neg_lt_zero : -a < 0 ↔ 0 < a`

```lean
example {f : ℝ → ℝ} (hneg : ∀ x, x < 0 → f x = 0) : ¬ Limit f 0 1 := by
  sorry
```
