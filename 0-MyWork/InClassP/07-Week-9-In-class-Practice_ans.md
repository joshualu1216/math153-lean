
## Exercise 1: Hilbert's hotel



**1.1** up is injective. 
	始x_1 + 1 = x_2 + 1，會得出x_1 = x_2
**1.2** up is not surjective. 
	0並不在裡面
**1.3** down is surjective. 
	對於每一個輸y，都可以找到一個 x = y + 1，使得down x = y.
**1.4** down is not injective.
	down(1) = down (0) = 0.

```lean
def up : ℕ → ℕ := fun n => n + 1
def down : ℕ → ℕ := fun n => n - 1
example : Function.Injective up := by
	intro x1 x2 h
	simpa [up] using h

  

example : ¬ Function.Surjective up := by
	intro h
	obtain ⟨x, hx⟩ := h 0
	simp [up] at hx

  

example : Function.Surjective down := by
	intro x
	use x + 1
	simp [down]


example : ¬ Function.Injective down := by
	intro h
	have h1 : down 0 = down 1 := by simp [down]
	have h2 : 0 = 1 := by
		apply h
		exact h1
	exact Nat.noConfusion h2
```

---

## Exercise 3: What does an injective composition tell you?


Suppose $g\circ f$ is injective. Decide whether each statement is true. If it is true, prove it; if it is false, give a counterexample. Write the proof in words first, then the Lean.

**3.1** $f$ must be injective.
	If g(f(x)) is injective, which imply that if g(f(x_1)) = g(f(x_2)), then x_1 = x_2
	Assume f(x_1) = f(x_2)
	then g(f(x_1)) = g(f(x_2))
	since g(f(x)) is injective, then x_1 = x_2.
	Hence, f is injective (since f(x_1) = f(x_2) imply to x_1 = x_2)
	
**3.2** $g$ must be injective.
	that f(x) = x + 1, g(x) = x - 1
	then g(f(x)) = x, which is injective.
	but g(x) ins't injective.

- Hint: for 3.2, look at the hotel in Exercise 1.

```lean
example {α β γ : Type} {f : α → β} {g : β → γ} (h : Function.Injective (g ∘ f)) :

	Function.Injective f := by
	intro x y hxy
	have hgx : g (f x) = g (f y) := by
		rw [hxy]
	exact h hgx

example : ¬ ∀ f g : ℕ → ℕ, Function.Injective (g ∘ f) → Function.Injective g := by
  sorry
```

---

## Exercise 5: Images of intersections

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
