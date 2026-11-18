---
module: 2
title: Week 3 In-class Practice
week: 3
audience: students
---

# Week 3 In-class Practice

The three exercises we do in class: Exercise 2, Exercise 4.3 and Exercise 7 of the [Week 3 Student Handout](02-Week-3-Student-Handout.md). All numbering follows the handout.

For each exercise, write the proof in words first, then the Lean. The proof in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`2.1`, `4.3`, `7.2`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 2: Additive functions and negatives

*Handout section: [1. Intermediate facts and rules](02-Week-3-Student-Handout.md#1-intermediate-facts-and-rules)*

A function $f:\mathbb{R}\to\mathbb{R}$ is **additive** if $f(x+y)=f(x)+f(y)$ for all $x$, $y$. In the handout we proved that an additive $f$ has $f(0)=0$.

Prove: if $f$ is additive and $f(0)=0$, then $f(-x)=-f(x)$ for every real $x$.

**2.1** Write the proof in words.

**2.2** Write it in Lean. The lemma you need: `add_neg_cancel : a + -a = 0`. Write the last step ("move a term over") with `calc`, as in the handout's proof of $f(0)=0$.

```lean
example {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) (hz : f 0 = 0) (x : ℝ) :
    f (-x) = -f x := by
  sorry
```

---

## Exercise 4.3: Factor, split into cases, no "or" at the end

*Handout section: [Exercise 4](02-Week-3-Student-Handout.md#exercise-4-factor-then-split-into-cases-the-lecture-example)*

In the handout, Exercise 4 proves "if $x^2-3x+2=0$, then $x=1$ or $x=2$" by factoring and splitting into cases. The lemma it uses:

- `eq_zero_or_eq_zero_of_mul_eq_zero : a * b = 0 → a = 0 ∨ b = 0`: if a product is 0, one of the factors is 0.

**4.3** With the same factoring and case split, prove: if a real number $x$ satisfies $x^2-5x+6=0$, then $x\ge 2$.

- Write the proof in words.
- Write it in Lean.
- This time the conclusion is not an "or". Does each branch still need `left` / `right`? Answer in one sentence.

```lean
example {x : ℝ} (hx : x ^ 2 - 5 * x + 6 = 0) : x ≥ 2 := by
  sorry
```

---

## Exercise 7: Take out the old witnesses, hand over a new one

*Handout section: [4. There exists: hand over a witness](02-Week-3-Student-Handout.md#4-there-exists-hand-over-a-witness)*

"$n$ is a sum of two squares" means: there are integers $a$, $b$ with $n=a^2+b^2$. For example, $13=2^2+3^2$.

```lean
def IsSumOfTwoSquares (n : ℤ) : Prop := ∃ a b :＝ ℤ, n = a ^ 2 + b ^ 2
```

Prove: the product of two sums of two squares is again a sum of two squares.

```lean
example {m n : ℤ} (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  sorry
```

**7.1** What do you get by **using** `hm`, and what by using `hn`? Write down the new variables and the equations.

**7.2** What you have to **prove** is a "there exists". Which witnesses do you hand over? Hint: expand $(ac-bd)^2+(ad+bc)^2$.

**7.3** Write the full proof in words, then the Lean. Put the `def` line above your `example` so that the file compiles.
