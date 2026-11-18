import Mathlib
---Exercise 1
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

---Exercise 3
example {α β γ : Type} {f : α → β} {g : β → γ} (h : Function.Injective (g ∘ f)) :
    Function.Injective f := by
    intro x y hxy
    have hgx : g (f x) = g (f y) := by
      rw [hxy]
    exact h hgx

example : ¬ ∀ f g : ℕ → ℕ, Function.Injective (g ∘ f) → Function.Injective g := by
  push Not
  use up, down
  constructor
  · intro x y hxy
    simpa
  · intro h
    have h1 : down 0 = down 1 := by simp [down]
    have h2 : 0 = 1 := by
      apply h
      exact h1
    exact Nat.noConfusion h2



---Exercise5
example {α β : Type} (f : α → β) (A B : Set α) : f '' (A ∩ B) ⊆ f '' A ∩ f '' B := by
  sorry


def square : ℝ → ℝ := fun x => x ^ 2

example : square '' ({-1} ∩ {1}) ≠ square '' {-1} ∩ square '' {1} := by
  intro h
  have h1 : (1 : ℝ) ∈ square '' {-1} ∩ square '' {1} := by
    simp [square]
  rw [← h] at h1
  simp [square] at h1         -- h1 : -1 = 1
  norm_num at h1
