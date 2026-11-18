# Week 4 Homework
## Exercise 1: If … then …

*Handout section: 0. If … then …*

**1.1** Prove: if (if $P$ then $Q$) and (if $Q$ then $R$), then (if $P$ then $R$). Write the proof in words first, then the Lean.

因為P成立，我們得到Q；因為Q成立，我們得到R。

```lean
example (P Q R : Prop) : (P → Q) → (Q → R) → (P → R) := by
  intro hpq hqr hp
  have hq : Q := hpq hp
  exact hqr hq

```

**1.2** Prove: if (if $P$ and $Q$, then $R$), then (if $P$, then (if $Q$ then $R$)). Write the proof in words first, then the Lean.

已知(P and Q -> R)
依序假設P成立和Q成立（=>發現這著前提下會滿足P and Q成立）
因此R成立。

```lean
example (P Q R : Prop) : (P ∧ Q → R) → (P → Q → R) := by
  intro hpqr hp hq
  have hpq : P ∧ Q := And.intro hp hq
  exact hpqr hpq
```

## Exercise 2: Witnesses that are expressions

*Handout section: 1. Definitions: even, divides, congruent*

Recall the Lean definitions: `Odd n` means there is `k` with `n = 2 * k + 1`; `Even n` means there is `r` with `n = r + r`; `a ∣ b` means there is `c` with `b = a * c`. A congruence must first be turned into divisibility with `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`.

**2.1** Prove each of the following three statements, in words and in Lean. A witness need not be a number; it can be an expression.

- Every integer divides $0$.

對任意整數a，存在已個整數c使得a*c=0。取c=0。恆成立。
- If $n$ is odd, then $3n+2$ is odd.

史n=2k+1, k是整數。3n+2=6k+5=2(3k+2)+1是奇數。
- The two sides of a congruence can be swapped: if $a\equiv b\pmod n$, then $b\equiv a\pmod n$. Hint: turn both the hypothesis and the goal into divisibility first (`at h ⊢`); the goal contains `a - b`, so first use `calc` to write it as `-(b - a)` before you substitute the hypothesis.

$a\equiv b\pmod n$ <=> b-a=cn, c是整數。=>a-b=(-c)n，-c也是整數。因此 $b\equiv a\pmod n$

```lean
example (a : ℤ) : a ∣ 0 := by
  use 0
  ring

example {n : ℤ} : Odd n → Odd (3 * n + 2) := by
  intro h
  obtain ⟨k, hk⟩ := h
  use 3 * k + 2
  rw [hk]
  ring

example {a b n : ℤ} : a ≡ b [ZMOD n] → b ≡ a [ZMOD n] := by
  intro h
  rw [Int.modEq_iff_dvd] at h ⊢
  obtain ⟨c, hc⟩ := h
  use -c
  calc
    a - b = -(b - a) := by ring
    _ = -(n * c)     := by rw [hc]
    _ = n * -c       := by ring

```

**2.2** First write each of the two sentences below as a Lean statement (replace the `sorry` after the colon by the statement; write congruence with `[ZMOD 5]`). Then prove them, in words and in Lean.

- If the integers $a$ and $b$ are both odd, then $a+b$ is even.

a=2k+1, b=2m+1，k, m都是整數。a+b=2(k+m+1)
- If the integers $a$ and $b$ are congruent modulo $5$, then $a^2$ and $b^2$ are congruent modulo $5$. Hint: $b^2-a^2=(b-a)(b+a)$.

b-a=5n, n是整數。b^2 - a^2 = (b+a)(b-a)=(b+a)*5n，因為b+a是整數。因此b^2 - a^2 是5的倍數。

```lean
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
```

## Exercise 4: A divisor is not larger than the number

*Handout section: 2. Divisibility and parity*

Let $a$ and $b$ be natural numbers.

**4.1** Prove: if $b>0$ and $a\mid b$, then $a\le b$. Write the proof in words first, then the Lean.

- Hint: after taking out the witness $k$, split into the cases $k=0$ and $k>0$; the case $k=0$ contradicts $b>0$.
- Lemmas you need: `Nat.eq_zero_or_pos k : k = 0 ∨ k > 0`; `Nat.mul_le_mul_left c : a ≤ b → c * a ≤ c * b` (hand over `c` first, then the proof: `Nat.mul_le_mul_left c h`).
- For natural numbers, `0 < k` is `1 ≤ k`, so you can use it directly as `1 ≤ k`.
- In one of the cases the goal is `a ≤ b`, not `False`. But if a hypothesis works out to be false, `norm_num at` still finishes the case: a contradictory case cannot happen, so there is nothing left to prove.

已知b>0，因為 $b>0$ and $a\mid b$ 等價於b =ak，k是正整數。分成k>0和k=0：

當k＝0，b=ak=0，矛盾。
當k>0，因為k是正整數，k≥1，因此b ≥ b/k = a。故得證。

```lean
example {a b : ℕ} (hb : 0 < b) : a ∣ b → a ≤ b := by
  intro h
  obtain ⟨k, hk⟩ := h
  obtain hk0 | hk0 := Nat.eq_zero_or_pos k
  · rw [hk0] at hk

    rw [hk] at hb
    norm_num at hb
  · have hk1 : 1 ≤ k := hk0
    have h_le := Nat.mul_le_mul_left a hk1

    calc
      a = a * 1 := by ring
      _ ≤ a * k := h_le
      _ = b     := hk.symm

```

**4.2** Without the condition $b>0$, the conclusion is false. Give a counterexample $a$, $b$, and prove in Lean that "$a\mid b$" holds and that "$a\le b$" is impossible.

舉反例。5整除於零但是5大於零。（5不小於且不等於零）
```lean
-- 第一個句子：證明 a 確實能整除 b (例如 5 ∣ 0)
example : (5 : ℕ) ∣ 0 := by
  use 0
  ring

-- 第二個句子：證明 a ≤ b 是不可能的 (例如 5 ≤ 0 → False)
example : (5 : ℕ) ≤ 0 → False := by
  intro h
  norm_num at h

```