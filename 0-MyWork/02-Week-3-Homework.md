---
module: 2
title: Week 3 Homework
week: 3
audience: students
---

# Week 3 Homework

These are the exercises from the [Week 3 Student Handout](02-Week-3-Student-Handout.md) that we did not do in class.

Exercises 2, 4.3 and 7 were done in class and handed out separately: [Week 3 In-class Practice](02-Week-3-In-class-Practice.md). All numbering follows the handout.

Most exercises ask for a **proof in words** and a **Lean proof**. Write the proof in words first: decide the shape, then translate it. The proof in words may be in Chinese or English. Every lemma you need is named in the exercise or in the example right above it in the handout.

Exercise 8 is a bonus exercise.

Hand in one `.md` file. Label each answer with its number (`1.1`, `6.2`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: For every $M$, an $x$ of its own

*Handout section: [0. How to write a proof in words](02-Week-3-Student-Handout.md#0-how-to-write-a-proof-in-words)*

Prove: for every real $M$, there exists a **positive** real $x$ with $x^2>M$.

**1.1** Write the proof in words. After taking $x$, check two things: $x>0$, and $x^2>M$. Hint: $M$ may be negative.

**1.2** Could your $x$ be chosen before "let $M$ be arbitrary"? Answer "yes" or "no", then give your reason in one or two sentences.

No Lean for this exercise.

---

## Exercise 3: $x$ lies between $-|x|$ and $|x|$

*Handout section: [Using an "or" hypothesis: split into cases](02-Week-3-Student-Handout.md#using-an-or-hypothesis-split-into-cases)*

Prove: for every real $x$, $x\le |x|$, and also $-|x|\le x$.

**3.1** Write the proof in words. Split into two cases. In each case, prove both inequalities.

**3.2** Write it in Lean, one `example` per inequality. You need:

- `le_total 0 x : 0 ≤ x ∨ x ≤ 0` for the case split;
- `abs_of_nonneg : 0 ≤ a → |a| = a` and `abs_of_nonpos : a ≤ 0 → |a| = -a` to replace $|x|$ in each case.

```lean
example (x : ℝ) : x ≤ |x| := by
  sorry

example (x : ℝ) : -|x| ≤ x := by
  sorry
```

---

## Exercise 4: Factor, then split into cases (4.1 and 4.2)

*Handout section: [Exercise 4](02-Week-3-Student-Handout.md#exercise-4-factor-then-split-into-cases-the-lecture-example)*

> **Claim.** If a real number $x$ satisfies $x^2-3x+2=0$, then $x=1$ or $x=2$.
>
> **Proof.** Assume $x^2-3x+2=0$. Factoring gives $(x-1)(x-2)=0$. A product is 0, so $x-1=0$ or $x-2=0$. There are two cases. If $x-1=0$, then $x=1$, and the left side of the conclusion holds. If $x-2=0$, then $x=2$, and the right side of the conclusion holds. ∎

```lean
example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) = 0 := by
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0                                 := by rw [hx]
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1  -- two cases, both with goal x = 1 ∨ x = 2
  · left   -- goal is now just x = 1
    linarith
  · right  -- goal is now just x = 2
    linarith
```

**4.1** Follow how the goal changes in the comments. Which line **uses** an "or", and which lines **prove** an "or"? Which sentence of the proof in words does each correspond to? Write down the line and the matching sentence.

**4.2** Change `right` in the second branch to `left` and run it. Which line does Lean report an error on? What is the goal at that point, and which hypothesis do you have? Say in one sentence why it cannot be proved.

---

## Exercise 5: Take apart, split, pick, pair

*Handout section: [3. And: a pair of facts](02-Week-3-Student-Handout.md#3-and-a-pair-of-facts)*

Prove: if $P$ and ($Q$ or $R$), then ($P$ and $Q$) or ($P$ and $R$).

**5.1** Write the proof in words. Which one do you take apart first? Which one do you split into cases? In each case, which side do you pick, and which pair do you hand over?

**5.2** Write it in Lean:

```lean
example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

---

## Exercise 6: Absolute-value inequalities

*Handout section: [3. And: a pair of facts](02-Week-3-Student-Handout.md#3-and-a-pair-of-facts), the part "An absolute-value inequality is an 'and'"*

The lemma you need for both parts: `abs_lt : |a| < b ↔ -b < a ∧ a < b`. `rw [abs_lt]` turns the absolute value into an "and"; `rw [abs_lt] at h` does the same inside a hypothesis `h`.

**6.1** Prove: for every real $x$, if $|x-2|<1$, then $1<x$ and $x<3$. Conversely, if $1<x$ and $x<3$, then $|x-2|<1$. Write both the proof in words and the Lean.

```lean
example (x : ℝ) (h : |x - 2| < 1) : 1 < x ∧ x < 3 := by
  sorry

example (x : ℝ) (h1 : 1 < x) (h2 : x < 3) : |x - 2| < 1 := by
  sorry
```

**6.2** Prove: for every real $x$, if $0<|x-2|<1$, then $|x+2|<5$.

- To prove $\lim_{x\to 2}x^2=4$, you have to handle $|x^2-4|=|x-2|\,|x+2|$. Restricting to $|x-2|<1$ first lets you bound $|x+2|$ by $5$. This exercise is that step.
- $0<|x-2|<1$ is an "and" of two inequalities, so in Lean it is written `0 < |x - 2| ∧ |x - 2| < 1`.
- Write the proof in words first, then the Lean. The hypothesis and the goal each contain an absolute value. Turn both into an "and".
- Answer in one sentence: is the hypothesis $0<|x-2|$ used in this exercise? What is it for in the definition of a limit?

```lean
example (x : ℝ) (h : 0 < |x - 2| ∧ |x - 2| < 1) : |x + 2| < 5 := by
  sorry
```

---

## Exercise 8 [Bonus]: Cancellation in a vector space

*Handout section: [5. Packaging things: `structure`](02-Week-3-Student-Handout.md#5-packaging-things-structure)*

The `structure` below lists only what this exercise needs from the definition of a vector space: addition, the zero vector, negatives, and three axioms.

```lean
structure VectorSpaceAxioms (V : Type) where
  add : V → V → V
  zero : V
  neg : V → V
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  zero_add : ∀ v, add zero v = v
  neg_add : ∀ v, add (neg v) v = zero
```

- `S.add u v` is $u+v$, `S.zero` is the zero vector, and `S.neg u` is $-u$.
- All three axioms are "for all" rules. You use them like the additive-function rule in §1 of the handout: put in specific vectors.
- Take an axiom out with `S.` followed by the field name, for example `S.zero_add`. Inside `calc`, rewrite with `rw [S.zero_add]`.

Prove the **cancellation law**: if $u+v=u+w$, then $v=w$.

**8.1** Write the proof in words: start from $v$ and write a chain of equalities, each step using a single axiom or the hypothesis. Next to each equals sign, note which axiom or hypothesis it uses. Hint: $v=0+v=((-u)+u)+v=\ldots$

**8.2** Write it in Lean. Each equals sign in your proof in words becomes one line of `calc`. Put the `structure` above your `example` so that the file compiles.

```lean
example {V : Type} (S : VectorSpaceAxioms V) (u v w : V)
    (h : S.add u v = S.add u w) : v = w := by
  sorry
```
