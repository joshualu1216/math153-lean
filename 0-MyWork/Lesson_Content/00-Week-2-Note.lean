import Mathlib

---Problem 1
---Given total = 12:
---   total - 4 = 12 - 4    (given)
---             = 8         (compute)
example {total : ℤ } (h : total = 12):
    total - 4 = 8           := by
  calc  total - 4 = 12 - 4  := by rw [h]
  _               = 8       := by norm_num --which means 12 - 4 = 8

---Problem 2
---We know x + 4 = 2  =>  prove x = -2


---Problem 3


---Problem 4
example {r : ℤ} {s : ℤ} (k : s = 3) (j : r + 2 * s = -1):
    r = -7                      := by
  calc r = (r + 2 * s) - 2 * s  := by ring
  _      = -1 - 2 * s           := by rw [j]
  _      = -1 - 2 * 3           := by rw [k]
  _      = -1 - 6               := by norm_num
  _      = -7                   := by norm_num
