## Exercise 3: Odd squares

*Handout section: 2. Divisibility and parity*

Recall: `Odd n` means there is `k` with `n = 2 * k + 1`, and `Even n` means there is `r` with `n = r + r`. The lemma `Int.even_or_odd k : Even k ∨ Odd k` says every integer is even or odd.

Prove: if $n$ is odd, then $8\mid n^2-1$.

**3.1** Write the proof in words. Hint: when $n=2k+1$, $n^2-1=4k(k+1)$. To get one more factor of $2$, split into cases on whether $k$ is even or odd.

    Let n = 2k + 1 for k is a integer. Then n ^ 2 - 1 = 4k(k + 1).
    We slip into two cases based on whether k is odd or even:
    - k is odd:
        let k = 2x + 1 for x is a integer.
        Then, n^2 - 1 = 4(2x + 1)(2x + 2) = 8(2x + 1)(x + 1).
        Since (2x + 1)(x + 1) is also a integrr, it follows 8 | n^2 - 1.
    - k is even:
        let k = 2x for x is a integer.
        Then, n^2 - 1 = 4 * 2x * (2x + 1) = 8x(2x + 1)
        Since x(2x + 1) is also a integrr, it follows 8 | n^2 - 1.

**3.2** Write it in Lean.

```lean
example {n : ℤ} : Odd n → 8 ∣ n ^ 2 - 1 := by
  intro h
  obtain ⟨k, hk⟩ := h
  obtain hk_even | hk_odd := Int.even_or_odd k
  · obtain ⟨x, hx⟩ := hk_even
    use x * (2 * x + 1)
    rw [hk, hx]
    ring
  · obtain ⟨x, hx⟩ := hk_odd
    use (2 * x + 1) * (x + 1)
    rw [hk, hx]
    ring
```


## Exercise 5.1: Congruences can be multiplied

*Handout section: 3. Congruence*

Recall: to work with a congruence, first turn it into divisibility with `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`. You can rewrite hypotheses and the goal together: `rw [Int.modEq_iff_dvd] at h1 h2 ⊢`.

Prove: if $a\equiv b$ and $c\equiv d\pmod n$, then $ac\equiv bd\pmod n$. Do not use `Int.ModEq.mul`.

- Write the proof in words, then the Lean.
- Hint: write $bd-ac$ as $b(\ldots)+c(\ldots)$, where the two brackets are $d-c$ and $b-a$.

Ans:
    
    We have n | b - a and n | d - c.
    Let b - a = xn, d - c = yn, for x and y are both integers.
    Notice that, bd - ac = bd - ad + ad - ac = d(b - a) + a (d - c) = d * xn + a * yn = n *(dx + ay), which is a multiple of n.
    Thus, n | bd - ac


```lean
example {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a * c ≡ b * d [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h1 h2 ⊢

  obtain ⟨x, hx⟩ := h1
  obtain ⟨y, hy⟩ := h2
  use b * y + c * x
  calc
    b * d - a * c = b * (d - c) + c * (b - a) := by ring
    _ = b * (n * y) + c * (n * x)             := by rw [hx, hy]
    _ = n * (b * y + c * x)                   := by ring
```

## Exercise 6.1: Cancelling with Bézout

*Handout section: 4. Coprimality and Bézout*

Prove: if $11\mid 3n$, then $11\mid n$.

- First find integers $x$, $y$ with $3x+11y=1$.
- Then write the proof in words and the Lean.

Ans: 

    (1) x = 4 and y = -1
    (2) We have the equition 3 * 4 + 11 * (-1) = 1
        Multiply both side by n: n = 4 (3n) + 11 (-n) = n.
        Let w = 4a - n. Subsituting 3n = 11a. We have:
        n = 4 (11a) - 11n = 11 (4a-n) = 11w


```lean
example {n : ℤ} : 11 ∣ 3 * n → 11 ∣ n := by
  intro h
  
  obtain ⟨a, ha⟩ := h          
  let w := 4 * a - n
  use w
  calc
    n = 4 * (3 * n) - 11 * n := by ring
    _ = 4 * (11 * a) - 11 * n := by rw [ha]   
    _ = 11 * w               := by ring
```