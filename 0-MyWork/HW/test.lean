import Mathlib

--Problem 1
example (a b : ℕ) (ha : a = 2) (hb : b = 5) : b = 5 := by
  exact hb

--Problem 2
#check 10
#check (10 : ℚ)
#check fun n : ℕ => n + 1
#check (10 : ℤ) < 20


--Problem 3
#eval 3 - 10
#eval 10 - 3
#eval (3 : ℤ) - 10
#check √2


--Problem 4
def shift (k : ℕ) (n : ℕ) : ℕ :=
  n + k

#check shift
#check shift 4
#eval shift 4 10

example (x : ℕ) (h : x = 4) : x = 4 := by
  exact h
