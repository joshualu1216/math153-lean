---
module: 4
title: Week 5 Homework
week: 5
audience: students
---

# Week 5 Homework

The Week 5 exercises that we do not do in class. Exercises 2.1, 3.1, 4.1 and 5 are in the [Week 5 In-class Practice](04-Week-5-In-class-Practice.md). Each exercise names the section of the [Week 5 Student Handout](04-Week-5-Student-Handout.md) it practises.

Each exercise asks for a **proof in words** and a **Lean proof**. Write the proof in words first: decide the shape, then translate it. The proof in words may be in Chinese or English. Every lemma you need is named in the exercise or in the handout section it refers to.

Hand in one `.md` file. Label each answer with its number (`1`, `2.2`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: An estimate

*Handout section: 1. For all*

Prove: for every real $x$, if $|x|\le 2$, then $|x^2-4|\le 4|x-2|$.

- Hint: $x^2-4=(x-2)(x+2)$. From $|x|\le 2$, derive $|x+2|\le 4$.
- Lemmas you need:
  - `abs_le : |a| ≤ b ↔ -b ≤ a ∧ a ≤ b`
  - `add_le_add_left : b ≤ c → ∀ a, b + a ≤ c + a`
  - `abs_mul a b : |a * b| = |a| * |b|`
  - `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c`
  - `abs_nonneg a : 0 ≤ |a|`
- To replace the expression inside an absolute value by an equal one, use `congrArg abs (by ring)`.

```lean
example : ∀ x : ℝ, |x| ≤ 2 → |x ^ 2 - 4| ≤ 4 * |x - 2| := by
  sorry
```

---

## Exercise 2.2: The limit of $x^2$

*Handout section: 1. For all, "Order of quantifiers: the definition of a limit"*

Recall the definition:

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
```

Prove: if $f(x)=x^2$ for every real $x$, then $\displaystyle\lim_{x\to 2}f(x)=4$. Write the proof in words first, then the Lean.

- Idea: $|x^2-4|=|x-2|\,|x+2|$. If $|x-2|<1$, then $|x+2|<5$ (Week 3, Exercise 6.2), and so $|x^2-4|<5|x-2|$. So we need both $|x-2|<1$ and $|x-2|<\varepsilon/5$: take $\delta=\min(1,\varepsilon/5)$.
- Lemmas you need:
  - `lt_min : a < b → a < c → a < min b c`
  - `min_le_left a b : min a b ≤ a`, `min_le_right a b : min a b ≤ b`
  - `lt_of_lt_of_le : a < b → b ≤ c → a < c`
  - `abs_lt : |a| < b ↔ -b < a ∧ a < b`
  - `add_lt_add_left : b < c → ∀ a, b + a < c + a`
  - `abs_mul a b : |a * b| = |a| * |b|`, `abs_nonneg a : 0 ≤ |a|`
  - `mul_le_mul_of_nonneg_left : b ≤ c → 0 ≤ a → a * b ≤ a * c`
  - `mul_lt_mul_of_pos_right : b < c → 0 < a → b * a < c * a`
  - `le_of_lt : a < b → a ≤ b`
  - `div_pos : 0 < a → 0 < b → 0 < a / b`

```lean
example {f : ℝ → ℝ} (hf : ∀ x, f x = x ^ 2) : Limit f 2 4 := by
  sorry
```

---

## Exercise 3.2: Smaller than every positive number

*Handout section: 2. Not, "Three ways to use a contradiction"*

Prove: if $|a|<\varepsilon$ for every $\varepsilon>0$, then $a=0$. Write the proof in words first, then the Lean.

- Hint: use proof by contradiction. If $a\ne 0$, which $\varepsilon$ should you plug in?
- Lemma you need: `abs_pos : 0 < |a| ↔ a ≠ 0`

```lean
example {a : ℝ} (h : ∀ ε > 0, |a| < ε) : a = 0 := by
  sorry
```

---

## Exercise 4.2: The barber paradox

*Handout section: 3. If and only if*

In a village, the barber $b$ shaves a person if and only if that person does not shave himself. Prove that no such barber can exist: given such a barber $b$, reach a contradiction. Write the proof in words first, then the Lean.

- Hint: apply the assumption to the barber himself ($x=b$). First prove "$b$ does not shave himself", then see what that leads to.

```lean
example {Man : Type} (shaves : Man → Man → Prop) (b : Man)
    (h : ∀ x, shaves b x ↔ ¬ shaves x x) : False := by
  sorry
```
