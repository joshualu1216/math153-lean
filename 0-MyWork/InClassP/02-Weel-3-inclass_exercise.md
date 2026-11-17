# Week 3 In-class Practice
Written by MU-NE, Lu. Student ID: 115021121.
## **Exercise 2**: Additive functions and negatives
**2.1** Notice that: $f(x-x) = f(0) = 0 = f(x) + f(-x). $
Hence, we found $f(-x) = - f(x)$

**2.2**
```lean
example {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) (hz : f 0 = 0) (x : ℝ) :
    f (-x) = -f x := by 
    calc
    f (-x) =( f x + f (-x) ) - f x := by ring
    _      = f ( x + (-x)) - f x := by rw[h]
    _      = f (0) - f x := by rw [add_neg_cancel]
    _      = 0 - f x := by rw [hz]
    _      = - f x := by ring
```
## **Exercise 4.3**: Factor, split into cases, no "or" at the end

**4.3** With the same factoring and case split, prove: if a real number $x$ satisfies $x^2-5x+6=0$, then $x\ge 2$.

- In this equation, we can find that x can be 2 or 3. Hence, $x\ge 2$.
- In lean
```lean
example {x : ℝ} (hx : x ^ 2 - 5 * x + 6 = 0) : x ≥ 2 := by
  have h1: (x - 2) * (x - 3) = 0 := by
    calc
       (x - 2) * (x - 3) = x ^ 2 - 5 * x + 6 := by ring
      _                 = 0 := by rw [hx]
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  · linarith
  · linarith
```
- No, since I don't have anything in left side or right side.

## **Exercise 7**: Take out the old witnesses, hand over a new one
### **7.1** What do you get by **using** `hm`, and what by using `hn`?
* By using `hm`, we get two integer variables **`a`** and **`b`**, and the equation **`hm_eq : m = a ^ 2 + b ^ 2`**.
* By using `hn`, we get two integer variables **`c`** and **`d`**, and the equation **`hn_eq : n = c ^ 2 + d ^ 2`**.

---

### **7.2** Which witnesses do you hand over?
Based on the identity (ac-bd)² + (ad+bc)² = (a²+b²)(c²+d²), the two witnesses we hand over are:
1. **`a * c - b * d`**
2. **`a * d + b * c`**

---

### **7.3** Full proof in words, then the Lean

#### **Proof in words:**
Suppose m and n are sums of two squares. 
By definition, there exist integers a, b such that m = a² + b², and integers c, d such that n = c² + d². 
We want to show that m ⋅ n is a sum of two squares, meaning we need to find two integers X, Y such that m ⋅ n = X² + Y².

Let X = ac - bd and Y = ad + bc. 
Multiplying m and n gives:
\[m \cdot n = (a^2 + b^2)(c^2 + d^2)\]
Expanding this product yields a²c² + a²d² + b²c² + b²d². 

On the other hand, expanding X² + Y² gives:
\[(ac - bd)^2 + (ad + bc)^2 = (a^2c^2 - 2abcd + b^2d^2) + (a^2d^2 + 2abcd + b^2c^2)\]
The -2abcd and +2abcd terms cancel out, leaving a²c² + b²d² + a²d² + b²c², which perfectly matches m ⋅ n.
Thus, m ⋅ n = (ac - bd)² + (ad + bc)², proving that m ⋅ n is a sum of two squares. \(\blacksquare\)

#### **Lean 4 Code:**
```lean
def IsSumOfTwoSquares (n : ℤ) : Prop := ∃ a b : ℤ, n = a ^ 2 + b ^ 2

example {m n : ℤ} (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  -- 1. Take out the old witnesses
  obtain ⟨a, b, hm_eq⟩ := hm
  obtain ⟨c, d, hn_eq⟩ := hn
  
  -- 2. Hand over the new witnesses
  use a * c - b * d, a * d + b * c
  
  -- 3. Substitute equations and check the identity
  rw [hm_eq, hn_eq]
  ring
```