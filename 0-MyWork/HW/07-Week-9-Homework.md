---
module: 7
title: Week 9 Homework
week: 9
audience: students
---

# Week 9 Homework

The Week 9 exercises that we do not do in class. Exercises 1, 3 and 5 are in the [Week 9 In-class Practice](07-Week-9-In-class-Practice.md). Each exercise names the section of the [Week 9 Student Handout](07-Week-9-Student-Handout.md) it practises.

Write the proof in words first, one step per line, then the Lean (Exercise 4 asks only for the proof in words). Proofs in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`2`, `4`, `6`). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 2: One collision means collisions everywhere

*Handout section: 1. Injective and surjective, "Example: when is an additive function injective?"*

Let $f:\mathbb{R}\to\mathbb{R}$ be additive and not injective. Prove: there is an $x\ne 0$ with $f(y+x)=f(y)$ for every $y$. Write the proof in words first, then the Lean.

- In other words: once an additive function has one collision, it has collisions everywhere.
- Hint: use the criterion `inj_iff_ker` from the handout, then negate as in Week 7.
- Lemmas you need:
  - `inj_iff_ker` (the handout example; copy it into your file)
  - `add_zero : a + 0 = a`

```lean
example {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) (h : ¬ Function.Injective f) :
    ∃ x, x ≠ 0 ∧ ∀ y, f (y + x) = f y := by
  sorry
```

---

## Exercise 4: A right inverse from surjectivity

*Handout section: 2. Composition and inverses*

The code below proves: if $f:A\to B$ is surjective, there is a $g:B\to A$ with $f(g(y))=y$ for every $y$ ($g$ is a right inverse of $f$). Read it, then write its proof in words, in your own words.

- `choose g hg using hf`: `hf` says every $y$ has some $x$ with $f(x)=y$. `choose` picks one such $x$ for each $y$ and calls it $g(y)$; `hg` records that $f(g(y))=y$.

```lean
theorem right_inv {α β : Type} {f : α → β} (hf : Function.Surjective f) :
    ∃ g : β → α, ∀ y, f (g y) = y := by
  choose g hg using hf
  exact ⟨g, hg⟩
```

- Also answer: why need this $g$ not be a left inverse ($g(f(x))=x$ may fail)? Give an example using down from Exercise 1 of the In-class Practice.

---

## Exercise 6: Injective functions respect intersections

*Handout section: 3. Images and preimages*

Let $f$ be injective. Prove: $f(A\cap B)=f(A)\cap f(B)$. Write the proof in words first, then the Lean.

- Hint: $\subseteq$ is In-class Exercise 5.1. For $\supseteq$: $y\in f(A)$ gives some $a\in A$, and $y\in f(B)$ gives some $b\in B$; they need not be the same element. Where do you use injectivity?

```lean
example {α β : Type} (f : α → β) (hf : Function.Injective f) (A B : Set α) :
    f '' (A ∩ B) = f '' A ∩ f '' B := by
  ext y
  constructor
  · sorry
  · sorry
```
