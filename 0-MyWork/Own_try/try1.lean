import Mathlib

-- Exercise 2
example (x y : ℝ) (h : x = y) : x + 3 = y + 3 := by
  nth_rw 1 [h]

example (f : ℝ → ℝ) (x y : ℝ) (h : x = y) : f x = f y := by
  nth_rw 1 [h]

example {m n : ℤ} (h : n = m - 1) (hn : n ≥ 0) : m - 1 ≥ 0 := by
  rw [←h]
  exact hn

example (a b : ℝ) (h : a = b) : a * a = a * b := by
  rw [h]

-- Exercise 4
example {a b c : ℝ} (h : a ≤ b) (k : b < c) : a < c := by
  calc
    a ≤ b := h
    _ < c := k

example {a b c : ℝ} (h : a ≥ b) (k : b > c) : a > c := by
  calc
    a ≥ b := h
    _ > c := k

-- example {a b c : ℝ} (h : a ≥ b) (k : b ≤ c) : a < c := by
-- 反證法


example {a b c : ℝ} (h : a < b) (k : b ≤ c) : a < c := by
  calc
    a < b := h
    _ ≤ c := k

example {a b c : ℕ } (h : a ∣ b) (k : b ∣ c) : a ∣ c := by
  calc
    a ∣ b := h
    _ ∣ c := k

example {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) (hz : f 0 = 0) (x : ℝ) :
    f (-x) = -f x := by
    calc
    f (-x) =( f x + f (-x) ) - f x := by ring
    _      = f ( x + (-x)) - f x := by rw[h]
    _      = f (0) - f x := by rw [add_neg_cancel]
    _      = 0 - f x := by rw [hz]
    _      = - f x := by ring

example {x : ℝ} (hx : x ^ 2 - 5 * x + 6 = 0) : x ≥ 2 := by
  have h1: (x - 2) * (x - 3) = 0 := by
    calc
       (x - 2) * (x - 3) = x ^ 2 - 5 * x + 6 := by ring
      _                 = 0 := by rw [hx]
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1
  · linarith
  · linarith

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


-- 定義什麼是奇數 (Odd)
def IsOdd (n : ℤ) : Prop := ∃ k : ℤ, n = 2 * k + 1

example {m n : ℤ} (hm : IsOdd m) (hn : IsOdd n)
    : IsOdd (m * n) := by
  obtain ⟨a, hm_eq⟩ := hm
  obtain ⟨b, hn_eq⟩ := hn
  use 2 * a * b + a + b
  rw [hm_eq, hn_eq]
  ring


-- 定義什麼是整除 (Dvd)
def MyDvd (a b : ℤ) : Prop := ∃ k : ℤ, b = a * k

example {a b c : ℤ} (hab : MyDvd a b) (hbc : MyDvd b c) :
  MyDvd a c := by
  obtain ⟨x, hab_eq⟩ := hab
  obtain ⟨y, hbc_eq⟩ := hbc
  use x * y
  rw [hbc_eq, hab_eq]
  ring


example {a b c : ℤ} (hab : MyDvd a b) :
  MyDvd a (b * c) := by
  obtain ⟨k, hab_eq⟩ := hab
  use k * c
  rw [hab_eq]
  ring


-- 定義偶數 (Even) 與 奇數 (Odd)
def IsEven (x : ℤ) : Prop := ∃ k : ℤ, x = 2 * k

-- 挑戰題：若 m 是偶數，則 m * n 也是偶數
example {m n : ℤ} (hm : IsEven m) :
  IsEven (m * n) := by
  obtain ⟨k, hm_eq⟩ := hm
  use n * k
  rw [hm_eq]
  ring


example : ¬ (∃ m : ℤ, ∀ n : ℤ, n ≤ m) := by
  -- 使用反證法！
  -- 假設這件事是假的（也就是去掉否定符號 ¬，假設存在這樣的大整數），並把這個假設命名為 h
  by_contra h

  -- 此時你的目標（Goal）會變成 False
  -- 而你的環境中多了一個武器：h : ∃ m : ℤ, ∀ n : ℤ, n ≤ m

  -- 看到 h 裡面有 ∃ 了對吧？用你最擅長的 obtain 拆開他！
  obtain ⟨m, hm⟩ := h  -- hm : ∀ n : ℤ, n ≤ m (m 比任何整數 n 都大)

  -- 因為 hm 對於「所有」的 n 都成立，那我們把 n 填入「m + 1」試試看
  have h_contradiction := hm (m + 1)  -- h_contradiction : m + 1 ≤ m

  -- 顯然 m + 1 ≤ m 是不可能的，交給 linarith 抓出矛盾、結束證明！
  linarith


-- 為了好證，我們引入一個已知的數學事實：整數如果不是偶數，就一定是奇數
axiom odd_of_not_even {x : ℤ} (h : ¬ IsEven x) : IsOdd x

example {x : ℤ} (h_sq : IsEven (x ^ 2)) :
IsEven x := by
  -- 1. 起手式：使用反證法！
  -- 假設結論是假的（即 x 不是偶數），命名為 h_not_even
  by_contra h_not_even

  -- 2. 利用上面的事實，既然 x 不是偶數，那 x 就是奇數
  have h_x_odd := odd_of_not_even h_not_even  -- h_x_odd : IsOdd x

  -- 3. 接下來交給你了！
  -- 提示：
  -- (a) 用 obtain 拆開 h_x_odd，得到一個整數 k 和 x = 2 * k + 1
  -- (b) 在計算紙上算算看：如果 x = 2k + 1，那 x^2 展開會是多少？
  --     x^2 = (2k + 1)^2 = 4k^2 + 4k + 1 = 2(2k^2 + 2k) + 1
  --     這代表 x^2 其實是一個「奇數」！
  -- (c) 用 obtain 拆開已知條件 h_sq (x^2 是偶數)，得到另一個整數和方程式
  -- (d) 把這兩個互相矛盾的 x^2 方程式連立起來，交給 linarith 或 ring 抓出矛盾！
  obtain ⟨k, h⟩ := h_x_odd
  obtain ⟨w, hw⟩ := h_sq
  have h_sq : x ^ 2 = 2 * (2 * k ^ 2 + 2 * k) + 1 := by
    rw [h]
    ring
  rw [hw] at h_sq
  omega

-- 引入一個已知事實：整數如果不是奇數，就一定是偶數
axiom even_of_not_odd {x : ℤ} (h : ¬ IsOdd x) : IsEven x

example {n : ℤ} (h_sq : IsOdd (n ^ 2)) : IsOdd n := by
  -- 1. 起手式：使用反證法！
  -- 假設結論是假的（即 n 不是奇數），命名為 h_not_odd
  by_contra h_not_odd

  -- 2. 利用上面的事實，既然 n 不是奇數，那 n 就是偶數
  have h_n_even := even_of_not_odd h_not_odd  -- h_n_even : IsEven n

  -- 3. 接下來交給你了！
  -- 提示：
  -- (a) 用 obtain 拆開 h_n_even，得到一個整數 k 和 n = 2 * k
  -- (b) 用 obtain 拆開已知條件 h_sq (n^2 是奇數)，得到另一個整數 w 和 n^2 = 2 * w + 1
  -- (c) 用 have 建立一個小計算，把 n = 2 * k 代入到 n^2 裡面並用 ring 展開 (會得到 n^2 = 4 * k^2 = 2 * (2 * k^2))
  -- (d) 用 rw [...] at ... 把已知條件代入，最後呼叫專治整數矛盾的 omega 結束這回合！
  obtain ⟨a, ha⟩ := h_n_even
  obtain ⟨b, hb⟩ := h_sq
  have h : n ^ 2 = 2 * (2 * a ^ 2) := by
    rw [ha]
    ring
  rw [hb] at h
  omega


example (x : ℝ) : x ≤ |x| := by
  obtain h | h := le_total 0 x
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    linarith

-- 講義第 5 頁：第二個不等式
example (x : ℝ) : -|x| ≤ x := by
  obtain h | h := le_total 0 x
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_nonpos h]
    linarith

example {x : ℝ} (hx : x ^ 2 - 3 * x + 2 = 0) : x = 1 ∨ x = 2 := by
  have h1 : (x - 1) * (x - 2) = 0 := by
    calc
      (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      _ = 0                                 := by rw [hx]
  obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1  -- two cases, both with goal x = 1 ∨ x = 2
  · left   -- goal is now just x = 1
    linarith
  · right  -- goal is now just x = 2
    linarith


example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  -- 1. 拆解 "and" 假設，拿出 P 以及 (Q ∨ R)
  obtain ⟨hp, hq_or_hr⟩ := h

  -- 2. 針對 (Q ∨ R) 進行分案討論
  obtain hq | hr := hq_or_hr
  · -- Case 1: Q 成立
    left            -- 選擇證明左邊的目標 (P ∧ Q)
    exact ⟨hp, hq⟩  -- 交付這對組合
  · -- Case 2: R 成立
    right           -- 選擇證明右邊的目標 (P ∧ R)
    exact ⟨hp, hr⟩  -- 交付這對組合



-- 正向蘊含：從絕對值推導到 1 < x ∧ x < 3
example (x : ℝ) (h : |x - 2| < 1) : 1 < x ∧ x < 3 := by
  -- 1. 根據講義提示，使用 rw [abs_lt] at h 將假設中的絕對值展開為 "and"
  rw [abs_lt] at h
  -- 2. 根據講義第 6 頁，使用 obtain 拆解 "and" 假設
  obtain ⟨h1, h2⟩ := h
  -- 3. 根據講義第 6 頁，目標是 "and"，需要交付一對組合 ⟨by …, by …⟩
  exact ⟨by linarith, by linarith⟩

-- 逆向蘊含：從 1 < x 和 x < 3 推導回絕對值
example (x : ℝ) (h1 : 1 < x) (h2 : x < 3) : |x - 2| < 1 := by
  -- 1. 根據講義提示，使用 rw [abs_lt] 將目標中的絕對值轉化為 "and" 目標
  rw [abs_lt]
  -- 2. 目標現在是 -1 < x - 2 ∧ x - 2 < 1，交付一對由 linarith 證出的組合
  exact ⟨by linarith, by linarith⟩


-- 正向蘊含：從絕對值推導到 1 < x ∧ x < 3


example (x : ℝ) (h : 0 < |x - 2| ∧ |x - 2| < 1) : |x + 2| < 5 := by
  -- 1. 拆解整體的 "and" 假設，拿到左邊的 h0 和右邊的 h_abs
  obtain ⟨h0, h_abs⟩ := h
  -- 2. 將 h_abs 裡面的絕對值用 rw [abs_lt] at 展開為 "and"
  rw [abs_lt] at h_abs
  -- 3. 再次拆解 "and" 假設，得到兩個實數不等式
  obtain ⟨h1, h2⟩ := h_abs
  -- 4. 將目標的絕對值用 rw [abs_lt] 展開為 "and" 目標
  rw [abs_lt]
  -- 5. 分別用 linarith 計算並交付這一對不等式結果
  exact ⟨by linarith, by linarith⟩

structure VectorSpaceAxioms (V : Type) where
  add : V → V → V
  zero : V
  neg : V → V
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  zero_add : ∀ v, add zero v = v
  neg_add : ∀ v, add (neg v) v = zero

example {V : Type} (S : VectorSpaceAxioms V) (u v w : V)
    (h : S.add u v = S.add u w) : v = w := by
  calc
    v = S.add S.zero v             := by rw [S.zero_add]
    _ = S.add (S.add (S.neg u) u) v := by rw [S.neg_add]
    _ = S.add (S.neg u) (S.add u v) := by rw [S.add_assoc]
    _ = S.add (S.neg u) (S.add u w) := by rw [h]
    _ = S.add (S.add (S.neg u) u) w := by rw [S.add_assoc]
    _ = S.add S.zero w             := by rw [S.neg_add]
    _ = w                          := by rw [S.zero_add]




example {n : ℤ} : Odd n → 8 ∣ n ^ 2 - 1 := by
  -- 1. 根據講義 §0，目標是 "If P, then Q"，使用 intro 引入假設
  intro h
  -- 2. 根據講義 §1，Odd 是一個 "there exists" 假設，使用 obtain 拿出證人 k
  obtain ⟨k, hk⟩ := h      -- hk : n = 2 * k + 1
  -- 3. 根據講義 §2，利用 Int.even_or_odd k 針對 k 是偶數或奇數分案討論
  obtain hk_even | hk_odd := Int.even_or_odd k
  · -- Case 1: k 是偶數 (Even k)
    -- 根據講義 §1，Even k 在 Lean 裡面是 k = x + x，拿出證人 x
    obtain ⟨x, hx⟩ := hk_even
    -- 交付我們算好的新證人：x * (2 * x + 1)
    use x * (2 * x + 1)
    -- 透過代數重寫與簡化完成此分支
    rw [hk, hx]
    ring
  · -- Case 2: k 是奇數 (Odd k)
    -- 根據講義 §1，Odd k 在 Lean 裡面是 k = 2 * x + 1，拿出證人 x
    obtain ⟨x, hx⟩ := hk_odd
    -- 交付我們算好的新證人：(2 * x + 1) * (x + 1)
    use (2 * x + 1) * (x + 1)
    -- 透過代數重寫與簡化完成此分支
    rw [hk, hx]
    ring


example {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  -- 1. 根據講義提示，同時將假設與目標轉換為整除（divisibility）形式
  rw [Int.modEq_iff_dvd] at h1 h2 ⊢

  -- 2. 根據講義總結表格，拆解 "divides" 假設，取出證人與等式
  obtain ⟨x, hx⟩ := h1                -- hx : b - a = n * x
  obtain ⟨y, hy⟩ := h2                -- hy : d - c = n * y

  -- 3. 根據講義總結表格，目標是整除，需要交付一個算好的新證人
  use b * y + c * x

  -- 4. 依照講義第 5 頁範例模式，用 calc 進行代數接龍
  calc
    b * d - a * c = b * (d - c) + c * (b - a) := by ring
    _ = b * (n * y) + c * (n * x)             := by rw [hx, hy]
    _ = n * (b * y + c * x)                   := by ring



example {n : ℤ} : 11 ∣ 3 * n → 11 ∣ n := by
  -- 1. 根據講義總結表格，目標是 "If P, then Q"，使用 intro 引入假設
  intro h

  -- 2. 根據講義總結表格，拆解 "divides" 假設，取出證人與等式
  obtain ⟨a, ha⟩ := h          -- ha : 3 * n = 11 * a

  -- 3. 根據講義第 8 頁模式，使用 let 給予新證人表達式一個名字
  let w := 4 * a - n

  -- 4. 交付算好的新證人
  use w

  -- 5. 遵照講義 §4 範例，用 calc 進行代數變換接龍
  calc
    n = 4 * (3 * n) - 11 * n := by ring
    _ = 4 * (11 * a) - 11 * n := by rw [ha]   -- 將 3 * n 替換為 11 * a
    _ = 11 * w               := by ring

example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  have hq : Q := hpq hp
  exact hqr hq

example (a : ℤ) : a ∣ 0 := by
  use 0
  ring

example {n : ℤ} : Odd n → Odd (3 * n + 2) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 3 * k + 2
  rw [hk]
  ring

  -- first sentence
example {a b : ℤ} : Odd a ∧ Odd b → Even (a + b) := by
  intro h
  obtain ⟨ha, hb⟩ := h
  obtain ⟨k, hk⟩ := ha
  obtain ⟨m, hm⟩ := hb
  use k + m + 1
  rw [hk, hm]
  ring

-- second sentence
example {a b : ℤ} : a ≡ b [ZMOD 5] → a ^ 2 ≡ b ^ 2 [ZMOD 5] := by
  intro h
  rw [Int.modEq_iff_dvd] at h ⊢
  obtain ⟨c, hc⟩ := h
  use c * (b + a)
  calc
    b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
    _ = (5 * c) * (b + a)             := by rw [hc]
    _ = 5 * (c * (b + a))             := by ring
