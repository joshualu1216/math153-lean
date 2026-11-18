---
module: 7
title: Week 9 Student Handout
week: 9
audience: students
---

# Week 9 Student Handout: Functions

- Section 1, injective and surjective: how to prove them and how to refute them.
- Section 2, composition and inverses.
- Section 3, images and preimages: our first use of sets in Lean.
- The exercises are handed out separately: the In-class Practice (done in class) and the Homework. Each exercise names the section of this handout it practises.
- Write proofs in words one step per line.

## 1. Injective and surjective

- $f:A\to B$ is **injective**: different inputs never give the same output. $f(x_1)=f(x_2)\Rightarrow x_1=x_2$.
- $f:A\to B$ is **surjective**: every element of $B$ is hit. $\forall y\in B,\ \exists x\in A,\ f(x)=y$.
- Lean: `Function.Injective f`, `Function.Surjective f`.

| Task | First step in words | First step in Lean |
|---|---|---|
| Prove injective | "Suppose $f(x_1)=f(x_2)$." Goal: $x_1=x_2$ | `intro x₁ x₂ h` |
| Prove surjective | "Let $y\in B$. Take $x=\ldots$." Check $f(x)=y$ | `intro y`, `use …` |
| Refute injective | Find $x_1\ne x_2$ with $f(x_1)=f(x_2)$ (a collision) | `intro h`, feed the collision to `h` |
| Refute surjective | Find $y$ and show no $x$ has $f(x)=y$ (a missed output) | `intro h`, `obtain ⟨x, hx⟩ := h y` |

- To use an injectivity hypothesis `hinj`, feed it an equation. With `h2 : g 0 = g 1`, `hinj h2 : 0 = 1`.
- Do not write `hinj 0 1`. The two inputs of injectivity are implicit, and Lean reports `numerals are data in Lean, but the expected type is a proposition`. Lean reads the inputs off the equation.
- For a function defined with `def`, use `simp [name]` to unfold it.

### Example: when is an additive function injective?

- The additive functions from Week 3: $f(x+y)=f(x)+f(y)$. Every linear transformation from linear algebra is additive.
- Linear algebra has a theorem: a linear transformation is injective exactly when its kernel is only 0. Additive functions behave the same way.

> **Claim.** Let $f:\mathbb{R}\to\mathbb{R}$ be additive. Then $f$ is injective if and only if $f(x)=0$ only for $x=0$.

- Idea: additivity first gives $f(0)=0$. ($\Rightarrow$) is a direct use of injectivity. ($\Leftarrow$) turns a collision $f(x_1)=f(x_2)$ into $f(x_1-x_2)=0$.

> **Proof.** $f(0)=f(0+0)=f(0)+f(0)$, so $f(0)=0$.\
> ($\Rightarrow$) Suppose $f$ is injective and $f(x)=0$.\
> Then $f(x)=f(0)$, so $x=0$ by injectivity.\
> ($\Leftarrow$) Suppose $f(x)=0$ only for $x=0$. Suppose $f(x_1)=f(x_2)$.\
> $f(x_2)+f(x_1-x_2)=f(x_2+(x_1-x_2))=f(x_1)=f(x_2)$.\
> So $f(x_1-x_2)=0$, hence $x_1-x_2=0$ by assumption, that is, $x_1=x_2$. ∎

```lean
theorem inj_iff_ker {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) :
    Function.Injective f ↔ ∀ x, f x = 0 → x = 0 := by
  have h0 : f 0 = 0 := by
    have h := hadd 0 0          -- f (0 + 0) = f 0 + f 0
    simp at h                   -- h : f 0 = 0
    exact h
  constructor
  · intro hinj x hx             -- (⇒) suppose f is injective and f x = 0
    exact hinj (by rw [hx, h0]) -- f x = f 0, so x = 0 by injectivity
  · intro hker x₁ x₂ heq        -- (⇐) suppose f x₁ = f x₂
    have h1 : f x₂ + f (x₁ - x₂) = f x₂ := by
      calc f x₂ + f (x₁ - x₂) = f (x₂ + (x₁ - x₂)) := (hadd x₂ (x₁ - x₂)).symm
        _ = f x₁ := by simp
        _ = f x₂ := heq
    have h2 : f (x₁ - x₂) = 0 := by simpa using h1
    have h3 : x₁ - x₂ = 0 := hker (x₁ - x₂) h2
    exact sub_eq_zero.mp h3
```

- `hinj (by rw [hx, h0])`: we feed injectivity the equation `f x = f 0` and get `x = 0`.
- `simpa using h1`: tidy up `h1` with `simp`, then use it to prove the goal.

## 2. Composition and inverses

- $g\circ f$: first $f$, then $g$. $(g\circ f)(x)=g(f(x))$.
- Lean: `g ∘ f`; `(g ∘ f) x` is `g (f x)`.
- Two functions are equal when every input gives the same output. Lean: `ext x` takes an arbitrary $x$; then prove `u x = v x`.

> **Claim.** If $f:A\to B$ and $g:B\to C$ are both injective, then $g\circ f$ is injective.

> **Proof.** Suppose $g(f(a))=g(f(b))$.\
> Since $g$ is injective, $f(a)=f(b)$.\
> Since $f$ is injective, $a=b$. ∎

```lean
example {α β γ : Type} {f : α → β} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro a b h                 -- h : (g ∘ f) a = (g ∘ f) b
  exact hf (hg h)             -- first use that g is injective, then that f is
```

- The proof peels from the outside in: first remove $g$, then $f$.

## 3. Images and preimages

| Notation | Meaning |
|---|---|
| `A : Set α` | $A$ is a subset of `α` |
| `x ∈ A` | $x$ belongs to $A$ |
| `A ∪ B`, `A ∩ B` | $x\in A$ or $x\in B$; $x\in A$ and $x\in B$ |
| `A ⊆ B` | every $x\in A$ belongs to $B$; to prove it: `intro x hx` |
| `f '' A` | image $f(A)$: `y ∈ f '' A` means "there is $x\in A$ with $f(x)=y$" |
| `f ⁻¹' B` | preimage $f^{-1}(B)$: `x ∈ f ⁻¹' B` means "$f(x)\in B$" |

- Two sets are equal when every element "belongs to the left side ⟺ belongs to the right side". Lean: `ext y`, the same idea as `ext x` for functions.
- `y ∈ f '' A` is an "exists": take it apart with `obtain ⟨x, hx, hfx⟩`, or build it with `⟨x, hx, hfx⟩` or `use x`.

> **Claim.** $f(A\cup B)=f(A)\cup f(B)$.

> **Proof.** ($\subseteq$) Suppose $y\in f(A\cup B)$.\
> Then there is $x\in A\cup B$ with $f(x)=y$.\
> If $x\in A$, then $y\in f(A)$; if $x\in B$, then $y\in f(B)$.\
> ($\supseteq$) Suppose $y\in f(A)$: there is $x\in A$ with $f(x)=y$.\
> $x\in A\cup B$, so $y\in f(A\cup B)$. The case $y\in f(B)$ is the same. ∎

```lean
example {α β : Type} (f : α → β) (A B : Set α) : f '' (A ∪ B) = f '' A ∪ f '' B := by
  ext y
  simp only [Set.mem_image, Set.mem_union]
  -- goal: (∃ x, (x ∈ A ∨ x ∈ B) ∧ f x = y) ↔ (∃ x ∈ A, f x = y) ∨ ∃ x ∈ B, f x = y
  constructor
  · intro h
    obtain ⟨x, hx, hfx⟩ := h
    obtain hA | hB := hx
    · left
      exact ⟨x, hA, hfx⟩
    · right
      exact ⟨x, hB, hfx⟩
  · intro h
    obtain ⟨x, hA, hfx⟩ | ⟨x, hB, hfx⟩ := h
    · exact ⟨x, Or.inl hA, hfx⟩
    · exact ⟨x, Or.inr hB, hfx⟩
```

- `simp only [Set.mem_image, Set.mem_union]` translates "belongs to" into logic. What is left is the "or" and "exists" from Week 7.
- After `ext y`, the single line `simp [or_and_right, exists_or]` also finishes the proof: `simp` distributes the "exists" over the "or" by itself.

## Summary

- Prove injective: suppose $f(x_1)=f(x_2)$. Prove surjective: let $y$ be arbitrary and hand over an $x$. Refute: find a collision, or a missed output.
- Use an injectivity hypothesis by feeding it an equation: `hinj h2`.
- Additive functions: injective ⟺ only 0 goes to 0.
- On an infinite set, a function can be injective without being surjective, or the other way round.
- If $g\circ f$ is injective, then $f$ is injective, but $g$ need not be.
- Prove set equality with `ext`; `y ∈ f '' A` is an "exists".

**Next week**: sets.
