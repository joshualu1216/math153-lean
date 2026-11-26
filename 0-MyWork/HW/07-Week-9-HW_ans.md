# Week 9 HW ans

## 2

Proof:由加性函數的判準：f是單射 $\iff$ 對每個 x，若 f(x)=0 則 x=0。\
f 不是單射，所以並非「對每個 x，若 f(x)=0 則 x=0」。\
否定：存在 x 使 f(x)=0 且 $x\ne0$。\
取這個 x。\
令 y 為任意實數。\
f(y+x)=f(y)+f(x)(加性）。\
f(y)+f(x)=f(y)+0=f(y)（。\
所以 f(y+x)=f(y)。 ∎
 
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
 
example {f : ℝ → ℝ} (hadd : ∀ x y, f (x + y) = f x + f y) (h : ¬ Function.Injective f) :
    ∃ x, x ≠ 0 ∧ ∀ y, f (y + x) = f y := by
  rw [inj_iff_ker hadd] at h      -- h : ¬ ∀ x, f x = 0 → x = 0
  push Not at h                   -- h : ∃ x, f x = 0 ∧ x ≠ 0
  obtain ⟨x, hx0, hx⟩ := h        -- hx0 : f x = 0, hx : x ≠ 0
  refine ⟨x, hx, ?_⟩
  intro y
  rw [hadd y x, hx0, add_zero]    -- f (y + x) = f y + f x = f y + 0 = f y
```
 ---
 
## 4

**Proof（用自己的話讀這段程式）。** 因為 f$是滿射，所以對每個 y 
$\in$ B，存在 x $ \in $ A 使 f(x)=y。\
對每一個 $y$，從這些 $x$ 裡挑出一個，把它記為 g(y)。\
這樣就定義了函數 g:B\to A。\
由挑選的方式，f(g(y))=y 對每個 y 成立。\
所以 g 是 f 的右反函數。 ∎
 

**為什麼這個 $g$ 不一定是左反函數？**

- f(0)=f(1)=0（down 不是單射），g 只能把 0 送回其中一個，沒辦法同時還原 0 和 1。左反函數要求 f 是單射。
---
 
## 6
 Proof.($\subseteq$) 令 $y\in f(A\cap B)$。\
則存在 $x\in A\cap B$ 使 $f(x)=y$。\
$x\in A$，所以 $y\in f(A)$；$x\in B$，所以 $y\in f(B)$。\
故 $y\in f(A)\cap f(B)$。\
($\supseteq$) 令 $y\in f(A)\cap f(B)$。\
由 $y\in f(A)$，存在 $a\in A$ 使 $f(a)=y$。\ 由 $y\in f(B)$，存在 $b\in B$ 使 $f(b)=y$。\
則 $f(a)=y=f(b)$。\
因為 $f$ 是單射，$a=b$。（這裡用到單射。）\
所以 $a=b\in B$，加上 $a\in A$，得 $a\in A\cap B$。\
又 $f(a)=y$，所以 $y\in f(A\cap B)$。 ∎
 

```lean
example {α β : Type} (f : α → β) (hf : Function.Injective f) (A B : Set α) :
    f '' (A ∩ B) = f '' A ∩ f '' B := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hfx⟩ := hy                          -- hx : x ∈ A ∩ B, hfx : f x = y
    exact ⟨⟨x, hx.1, hfx⟩, ⟨x, hx.2, hfx⟩⟩             -- y ∈ f '' A and y ∈ f '' B
  · intro hy
    obtain ⟨⟨a, ha, hfa⟩, ⟨b, hb, hfb⟩⟩ := hy          -- f a = y, f b = y
    have hab : a = b := hf (hfa.trans hfb.symm)        -- f a = f b, so a = b by injectivity
    refine ⟨a, ⟨ha, ?_⟩, hfa⟩                          -- a ∈ A ∩ B and f a = y; left: a ∈ B
    rw [hab]
    exact hb
```
 