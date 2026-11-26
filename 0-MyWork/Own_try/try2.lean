import Mathlib

example {a b : ℝ} (h1 : a - 5 * b = 4)
    (h2 : b + 2 = 3) : a = 9 := by
  have hb : b = 1 := by linarith [h2]
  calc
    a = a - 5 * b + 5 * b := by ring
    _ = 4 + 5 * 1 := by rw[h1, hb]
    _ = 9 := by ring

example {x y : ℤ} (h : y = x + 1) (hy : y ≤ 5) : x + 1 ≤ 5 := by
  rw[← h]
  exact hy

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt
  calc
    x = 3 * x / 3 := by linarith
    _ = 2/ 3 := by rw[hx]
    _ < 1 := by linarith
