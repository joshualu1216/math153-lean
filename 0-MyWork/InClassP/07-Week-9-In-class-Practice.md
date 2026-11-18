---
module: 7
title: Week 9 In-class Practice
week: 9
audience: students
---

# Week 9 In-class Practice

The exercises we do in class: Exercise 1, Exercise 3 and Exercise 5. The rest are in the [Week 9 Homework](07-Week-9-Homework.md). Each exercise names the section of the [Week 9 Student Handout](07-Week-9-Student-Handout.md) it practises.

For each exercise, write the proof in words first, then the Lean (Exercise 5.2 asks only for the proof in words). Proofs in words may be in Chinese or English; write them one step per line.

Hand in one `.md` file. Label each answer with its number (`1.1`, `3.2`, `5.1`, and so on). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 1: Hilbert's hotel

*Handout section: 1. Injective and surjective*

Rooms are numbered $0,1,2,\ldots$. Let $\mathrm{up}(n)=n+1$ (every guest moves one room up) and $\mathrm{down}(n)=n-1$ (every guest moves one room down; room 0 stays at 0, since subtraction of natural numbers never goes below 0). Prove the four statements below. Write the proof in words first, then the Lean.

**1.1** up is injective. **1.2** up is not surjective. **1.3** down is surjective. **1.4** down is not injective.

- A function from a finite set to itself is injective exactly when it is surjective. On an infinite set this can fail, and this exercise is an example.

```lean
def up : ℕ → ℕ := fun n => n + 1
def down : ℕ → ℕ := fun n => n - 1

example : Function.Injective up := by
  sorry

example : ¬ Function.Surjective up := by
  sorry

example : Function.Surjective down := by
  sorry

example : ¬ Function.Injective down := by
  sorry
```

---

## Exercise 3: What does an injective composition tell you?

*Handout section: 2. Composition and inverses*

Suppose $g\circ f$ is injective. Decide whether each statement is true. If it is true, prove it; if it is false, give a counterexample. Write the proof in words first, then the Lean.

**3.1** $f$ must be injective.

**3.2** $g$ must be injective.

- Hint: for 3.2, look at the hotel in Exercise 1.

```lean
example {α β γ : Type} {f : α → β} {g : β → γ} (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
  sorry

example : ¬ ∀ f g : ℕ → ℕ, Function.Injective (g ∘ f) → Function.Injective g := by
  sorry
```

---

## Exercise 5: Images of intersections

*Handout section: 3. Images and preimages*

**5.1** Prove: $f(A\cap B)\subseteq f(A)\cap f(B)$. Write the proof in words first, then the Lean.

```lean
example {α β : Type} (f : α → β) (A B : Set α) : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
  sorry
```

**5.2** The reverse inclusion can fail. The code below proves this with $\mathrm{square}(x)=x^2$, $A=\{-1\}$ and $B=\{1\}$. Read it, then write its proof in words, in your own words.

```lean
def square : ℝ → ℝ := fun x => x ^ 2

example : square '' ({-1} ∩ {1}) ≠ square '' {-1} ∩ square '' {1} := by
  intro h
  have h1 : (1 : ℝ) ∈ square '' {-1} ∩ square '' {1} := by
    simp [square]
  rw [← h] at h1
  simp [square] at h1         -- h1 : -1 = 1
  norm_num at h1
```
