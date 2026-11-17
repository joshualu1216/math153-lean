---
module: 3
title: Week 4 Student Handout
week: 4
audience: students
---

# Week 4 Student Handout: Divisibility, Congruence and Bézout

- Last week we learned how to use and prove "and", "or" and "there exists". This week adds "if … then …".
- Then we turn to number theory. Even numbers, divisibility and congruence can all be turned into "there exists", so last week's witness technique will be used all the time.
- The exercises are handed out separately: the In-class Practice (done in class) and the Homework. Each exercise names the section of this handout it practises.

## 0. If … then …

- "If $P$, then $Q$" is written `P → Q` in Lean. Most lemmas have this shape, for example `abs_of_nonneg : 0 ≤ a → |a| = a`.

### Using an "if … then …" hypothesis: feed it a proof

- In words: "Since $P$, by (the lemma or hypothesis) we get $Q$."
- In Lean: if you have `h : P → Q` and `hp : P`, then `h hp` is a proof of $Q$. Last week's `abs_of_nonneg h` was doing exactly this.
- Example:

```lean
example (P Q : Prop) (h : P → Q) (hp : P) : Q := h hp
```

### Proving an "if … then …" goal: `intro`

- In words: "Assume $P$." Then prove $Q$.
- In Lean: `intro hp`. $P$ becomes a hypothesis `hp` that you hold, and the goal is just $Q$.
- Example: if $x=2$, then $x^2=4$.

```lean
example (x : ℝ) : x = 2 → x ^ 2 = 4 := by
  intro h    -- assume x = 2; the goal is now just x ^ 2 = 4
  rw [h]
  norm_num
```

- `P → Q → R` means "if $P$, then (if $Q$, then $R$)": when both hypotheses hold, $R$ holds. `intro hp hq` takes out both hypotheses at once.

### A special conclusion: `False`

- `False` is a statement that is never true. `P → False` reads "$P$ cannot be true".
- To prove `P → False`: first `intro` to assume $P$, then derive a false fact, such as $2=3$.
- `norm_num at h` works out the numbers in hypothesis `h`. If the result is false, this case cannot happen, and the goal is proved at once.
- How `at` works:
  - `rw` and `norm_num` change the goal by default; add `at h` to change hypothesis `h` instead; `at h1 h2 ⊢` changes several at once, where `⊢` stands for the goal.
  - There is also `at *` (change everything), but then a reader cannot tell what was changed. We always list them.

> **Claim.** If $x=2$ and $x=3$, we have a contradiction.
>
> **Proof.** Assume $x=2$ and $x=3$. Substituting $x=2$ into $x=3$ gives $2=3$, a contradiction. ∎

```lean
example (x : ℝ) : x = 2 ∧ x = 3 → False := by
  intro h
  obtain ⟨h1, h2⟩ := h
  rw [h1] at h2    -- h2 becomes 2 = 3
  norm_num at h2   -- 2 = 3 is false
```

## 1. Definitions: even, divides, congruent

| Concept | Definition in words | Lean |
|---|---|---|
| $n$ is even | there is an integer $r$ with $n=2r$ | `Even n`: there is `r` with `n = r + r` |
| $n$ is odd | there is an integer $k$ with $n=2k+1$ | `Odd n`: there is `k` with `n = 2 * k + 1` |
| $a$ divides $b$ | there is an integer $c$ with $b=ac$ | `a ∣ b`: there is `c` with `b = a * c` |
| $a\equiv b\pmod n$ | $n$ divides $a-b$ | `a ≡ b [ZMOD n]`: `a % n = b % n` |

- In Lean, the first three are "there exists": to **use** such a hypothesis, take out the witness with `obtain`; to **prove** such a goal, hand over a witness.
- Lean defines congruence as "same remainder"; `a % n` is the remainder of $a$ divided by $n$. When you need to take out or hand over a witness, first turn it into divisibility with `Int.modEq_iff_dvd : a ≡ b [ZMOD n] ↔ n ∣ b - a`. If you apply `obtain` or `use` to a congruence directly, Lean reports an error that is hard to read.
- Order of subtraction: $n\mid a-b$ and $n\mid b-a$ say the same thing; the witnesses differ by a sign (you will prove this in Exercise 2.1). Lean uses $b-a$, so the proofs in words below use $b-a$ too.
- Direction of divisibility: $a\mid b$ means "$a$ divides $b$", that is, $b$ is a multiple of $a$. $3\mid 12$ is true, $12\mid 3$ is false.
- Typing: `∣` is `\mid`, and it is not the straight bar `|` on your keyboard; `≡` is `\equiv`; type `[ZMOD n]` as it is.
- In Lean, `Even n` is `n = r + r`, not `n = 2 * r`: the witness is the same, but the equation to check looks different. In words, keep writing $n=2r$.

> **Claim.** $-3$ is odd; $-2\mid 6$; $11\equiv 3\pmod 4$.

- Idea: solve $-3=2k+1$ to get $k=-2$; solve $6=-2c$ to get $c=-3$; solve $3-11=4c$ to get $c=-2$.

> **Proof.** Take $k=-2$: then $2\cdot(-2)+1=-3$. Take $c=-3$: then $(-2)\cdot(-3)=6$. Also $3-11=-8=4\cdot(-2)$, so $4\mid 3-11$. ∎

```lean
example : Odd (-3 : ℤ) := ⟨-2, by norm_num⟩

example : (-2 : ℤ) ∣ 6 := ⟨-3, by norm_num⟩

example : (11 : ℤ) ≡ 3 [ZMOD 4] := by
  rw [Int.modEq_iff_dvd]    -- the goal becomes 4 ∣ 3 - 11
  exact ⟨-2, by norm_num⟩
```

- A witness can be negative. That is why $-2\mid 6$ only makes sense for integers: among natural numbers, neither $-2$ nor $-3$ exists.

## 2. Divisibility and parity: hand over a witness, split into cases, reach a contradiction

### Handing over a witness

- To prove that $a$ divides an expression, write the expression as $a\cdot(\ldots)$; what is in the brackets is the witness.
- Divisibility in the hypotheses gives you witnesses; combine them into a new witness. This is the pattern of last week's Exercise 7.

> **Claim.** If $a\mid b$, then $a\mid b^2+2b$.
>
> **Proof.** Assume $a\mid b$. Then there is an integer $k$ with $b=ak$. So $b^2+2b=(ak)^2+2ak=a\cdot k(ak+2)$, and therefore $a\mid b^2+2b$. ∎

```lean
example {a b : ℤ} : a ∣ b → a ∣ b ^ 2 + 2 * b := by
  intro h
  obtain ⟨k, hk⟩ := h        -- hk : b = a * k
  use k * (a * k + 2)        -- goal: b ^ 2 + 2 * b = a * (k * (a * k + 2))
  rw [hk]
  ring
```

### Splitting into cases: every integer is even or odd

- Every integer is even or odd. The Mathlib lemma is `Int.even_or_odd n : Even n ∨ Odd n`. This is an "or", so split into cases with last week's `obtain h1 | h2`.
- A lemma's name is usually its statement: `Int` (about integers) + `even_or_odd`. Other common words: `of` ("from … we get"), `iff` ("if and only if"), `le` ($\le$), `lt` ($<$), `dvd` (divides).
- When you are not sure what a lemma says, use `#check Int.even_or_odd` to see its statement.

> **Claim.** For every integer $n$, $n^2+n+4$ is even.
>
> **Proof.** Let $n$ be an arbitrary integer. There are two cases. If $n=2x$, then $n^2+n+4=4x^2+2x+4=2(2x^2+x+2)$. If $n=2x+1$, then $n^2+n+4=4x^2+6x+6=2(2x^2+3x+3)$. In both cases it is even. ∎

```lean
example (n : ℤ) : Even (n ^ 2 + n + 4) := by
  obtain hn | hn := Int.even_or_odd n
  · obtain ⟨x, hx⟩ := hn      -- hx : n = x + x
    use 2 * x ^ 2 + x + 2
    rw [hx]
    ring
  · obtain ⟨x, hx⟩ := hn      -- hx : n = 2 * x + 1
    use 2 * x ^ 2 + 3 * x + 3
    rw [hx]
    ring
```

### Reaching a contradiction: "does not divide"

- "$5$ does not divide $12$" is written $5\nmid 12$. It means there is no integer $k$ with $12=5k$.
- There is no witness to hand over, so we use the method of §0: assume $5\mid 12$ and reach a contradiction. In Lean this is `(5 : ℤ) ∣ 12 → False`.

> **Claim.** $5\nmid 12$.
>
> **Proof.** Assume $5\mid 12$. Then there is an integer $k$ with $12=5k$. There are two cases. If $k\le 2$, then $12=5k\le 10$, a contradiction. If $k>2$, then $k\ge 3$ because $k$ is an integer, so $12=5k\ge 15$, a contradiction. ∎

```lean
example : (5 : ℤ) ∣ 12 → False := by
  intro h
  obtain ⟨k, hk⟩ := h                  -- hk : 12 = 5 * k
  obtain h1 | h1 := le_or_gt k 2       -- k ≤ 2 or 2 < k
  · have h2 : (12 : ℤ) ≤ 10 := by
      calc
        (12 : ℤ) = 5 * k := hk
        _ ≤ 5 * 2        := Int.mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 10           := by norm_num
    norm_num at h2                     -- 12 ≤ 10 is false
  · have h3 : 3 ≤ k := h1              -- for integers, 2 < k is 3 ≤ k
    have h2 : (15 : ℤ) ≤ 12 := by
      calc
        (15 : ℤ) = 5 * 3 := by norm_num
        _ ≤ 5 * k        := Int.mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ = 12           := hk.symm
    norm_num at h2
```

- **Where we use that $k$ is an integer**: `have h3 : 3 ≤ k := h1`. For integers, $2<k$ and $3\le k$ are the same thing; that is how Lean defines $<$ on integers. With rational numbers, $k=\frac{12}{5}$ lies between $2$ and $3$, and this proof breaks down.
- Lemmas used:
  - `le_or_gt a b : a ≤ b ∨ b < a`.
  - `Int.mul_le_mul_of_nonneg_left : a ≤ b → 0 ≤ c → c * a ≤ c * b`: multiplying both sides by a non-negative number keeps the direction. `0 ≤ 5` is handed over with `by norm_num`.
- `hk.symm`: swaps the two sides of `hk : 12 = 5 * k`.

## 3. Congruence

- $a\equiv b\pmod n$ is equivalent to "$a$ and $b$ have the same remainder when divided by $n$". For example, a clock does arithmetic modulo $12$: $5$ hours after $9$ o'clock it is $2$ o'clock, and $9+5=14\equiv 2\pmod{12}$.
- You can calculate with congruences as with equations: add them, multiply them, raise them to powers. We prove addition first.

> **Claim.** If $a\equiv b$ and $c\equiv d\pmod n$, then $a+c\equiv b+d\pmod n$.
>
> **Proof.** By assumption there are integers $x$, $y$ with $b-a=nx$ and $d-c=ny$. Then $(b+d)-(a+c)=(b-a)+(d-c)=nx+ny=n(x+y)$, so $a+c\equiv b+d\pmod n$. ∎

```lean
example {n a b c d : ℤ} (h1 : a ≡ b [ZMOD n]) (h2 : c ≡ d [ZMOD n]) :
    a + c ≡ b + d [ZMOD n] := by
  rw [Int.modEq_iff_dvd] at h1 h2 ⊢   -- turn both hypotheses and the goal into divisibility
  obtain ⟨x, hx⟩ := h1                -- hx : b - a = n * x
  obtain ⟨y, hy⟩ := h2                -- hy : d - c = n * y
  use x + y
  calc
    b + d - (a + c) = (b - a) + (d - c) := by ring
    _ = n * x + n * y                   := by rw [hx, hy]
    _ = n * (x + y)                     := by ring
```

- Its Mathlib name is `Int.ModEq.add : a ≡ b [ZMOD n] → c ≡ d [ZMOD n] → a + c ≡ b + d [ZMOD n]`. The proof above is the reason behind it.
- Multiplication is Exercise 5.1 in the In-class Practice. Once multiplication works, powers work too: `Int.ModEq.pow m : a ≡ b [ZMOD n] → a ^ m ≡ b ^ m [ZMOD n]`.

### Substitution: calculating as with equations

- Inside a polynomial, $x$ can be replaced by a number congruent to it.

> **Claim.** If $x\equiv 2\pmod 5$, then $x^2+1\equiv 0\pmod 5$.
>
> **Proof.** Since $x\equiv 2$, we have $x^2\equiv 2^2$. Adding $1$ to both sides gives $x^2+1\equiv 2^2+1=5\equiv 0\pmod 5$. ∎

```lean
example {x : ℤ} (hx : x ≡ 2 [ZMOD 5]) : x ^ 2 + 1 ≡ 0 [ZMOD 5] := by
  calc
    x ^ 2 + 1 ≡ 2 ^ 2 + 1 [ZMOD 5] := Int.ModEq.add (Int.ModEq.pow 2 hx) rfl
    _ ≡ 0 [ZMOD 5]                 := by rfl
```

- Read the first line from the inside out: `Int.ModEq.pow 2 hx` is $x^2\equiv 2^2$; `rfl` is $1\equiv 1$; `Int.ModEq.add` adds the two congruences.
- `by rfl`: congruence is defined as "same remainder" (§1). When both sides are specific numbers, Lean computes both remainders and compares them.

### Splitting by remainder: `mod_cases`

- Every integer leaves remainder $0$, $1$ or $2$ when divided by $3$. So a statement about all integers can be split into three cases, and each case is a substitution calculation. Splitting by parity is the same idea: the remainder when divided by $2$.
- In Lean: `mod_cases hx : x % 3` produces three cases, with hypotheses `hx : x ≡ 0 [ZMOD 3]`, `x ≡ 1` and `x ≡ 2`.

> **Claim.** For every integer $x$, $x^3\equiv x\pmod 3$.
>
> **Proof.** Let $x$ be an arbitrary integer, and split into three cases by the remainder of $x$ divided by $3$. If $x\equiv 0$, then $x^3\equiv 0^3=0\equiv x$. If $x\equiv 1$, then $x^3\equiv 1^3=1\equiv x$. If $x\equiv 2$, then $x^3\equiv 2^3=8\equiv 2\equiv x$. ∎

```lean
example {x : ℤ} : x ^ 3 ≡ x [ZMOD 3] := by
  mod_cases hx : x % 3
  · calc
      x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 hx
      _ ≡ 0 [ZMOD 3]         := by rfl
      _ ≡ x [ZMOD 3]         := hx.symm
  · calc
      x ^ 3 ≡ 1 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 hx
      _ ≡ 1 [ZMOD 3]         := by rfl
      _ ≡ x [ZMOD 3]         := hx.symm
  · calc
      x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 hx
      _ ≡ 2 [ZMOD 3]         := by rfl
      _ ≡ x [ZMOD 3]         := hx.symm
```

- `hx.symm`: swaps the two sides of `hx : x ≡ 2 [ZMOD 3]`, giving `2 ≡ x [ZMOD 3]`.
- Why one representative is enough: when $x\equiv 2$, $x$ might be $5$, and $5^3=125$ is not $8$; but $125\equiv 8\equiv 2\pmod 3$. We are proving a congruence, not an equality.

## 4. Coprimality and Bézout

### When can we cancel?

- Multiplication can be cancelled: $5n=5m$ gives $n=m$. What about divisibility? If $a\mid bc$, does it follow that $a\mid c$?
- Not always: $4\mid 2\cdot 6$, but $4\nmid 6$. The trouble is that $4$ and $2$ have the common factor $2$.
- If $a$ and $b$ are **coprime** (their greatest common divisor is $1$), we can cancel. The key is the following equation.

### Bézout's identity

- **Bézout's identity**: if $a$ and $b$ are coprime, there are integers $x$, $y$ with $ax+by=1$. Examples: $8\cdot 2+5\cdot(-3)=1$; $3\cdot(-2)+7\cdot 1=1$.
- There are two ways to find $x$ and $y$.

**Method 1: list multiples** (for small numbers)

- List the multiples of $5$: $5,10,15,\ldots$, and look for one that is $1$ away from a multiple of $8$: $15=16-1$. So $8\cdot 2-5\cdot 3=1$.

**Method 2: the Euclidean algorithm, then work backwards** (for larger numbers)

- Take $17$ and $5$. First run the Euclidean algorithm until the remainder is $1$:
  - $17=3\cdot 5+2$
  - $5=2\cdot 2+1$
- Then work backwards from the last line, replacing the remainders one at a time:
  - $1=5-2\cdot 2$
  - $\phantom{1}=5-2\cdot(17-3\cdot 5)$ (replace $2$ by $17-3\cdot 5$)
  - $\phantom{1}=7\cdot 5-2\cdot 17$
- Check: $35-34=1$. So $x=-2$, $y=7$ give $17x+5y=1$.

**Why coprime numbers always work**

- Method 2 is in fact the proof. Every remainder in the Euclidean algorithm can be written as $a\cdot(\text{integer})+b\cdot(\text{integer})$:
  - $a$ and $b$ themselves can: $a=a\cdot 1+b\cdot 0$, $b=a\cdot 0+b\cdot 1$.
  - Each new remainder is "the one before last minus the quotient times the last one": $r_{\text{new}}=r_{\text{before last}}-q\cdot r_{\text{last}}$. If both can be written this way, so can their difference.
- The common divisors do not change from step to step: $d$ divides both $r_{\text{before last}}$ and $r_{\text{last}}$ if and only if $d$ divides both $r_{\text{last}}$ and $r_{\text{new}}$. So the last non-zero remainder is the greatest common divisor of $a$ and $b$.
- When $a$ and $b$ are coprime, this last remainder is $1$, so $1$ can be written as $ax+by$.

### Cancelling with Bézout

- Idea: $n=n\cdot 1=n(ax+by)$, then replace the $bn$ in the expression by a multiple you already know.

> **Claim.** If $8\mid 5n$, then $8\mid n$.

- Idea: $8\cdot 2+5\cdot(-3)=1$; multiplying by $n$ gives $n=16n-3\cdot(5n)$. The first term is a multiple of $8$; the $5n$ in the second term is a multiple of $8$ by assumption.

> **Proof.** Assume $5n=8a$. Let $w=2n-3a$. Then $n=16n-3\cdot(5n)=16n-3\cdot 8a=8w$, so $8\mid n$. ∎

```lean
example {n : ℤ} : 8 ∣ 5 * n → 8 ∣ n := by
  intro h
  obtain ⟨a, ha⟩ := h          -- ha : 5 * n = 8 * a
  let w := 2 * n - 3 * a       -- let w = 2n - 3a
  use w
  calc
    n = 16 * n - 3 * (5 * n) := by ring
    _ = 16 * n - 3 * (8 * a) := by rw [ha]
    _ = 8 * w                := by ring
```

- The `ring` on the first line only checks $16n-15n=n$. Writing $n$ as $16n-3\cdot(5n)$ is decided by Bézout's identity; `ring` will not think of it for you.

**`let`: giving a name to a thing**

- Last week we saw that one source of variables is "your choice", written "let $w=\ldots$" in words. In Lean it is `let w := …`.
- `let` and `have` both give names; the difference is **whether the value is remembered**:
  - `have h : P := …` names a **fact**. Afterwards you only need to know that $P$ holds.
  - `let w := …` names a **thing** (a number, an expression, a set) and remembers what it equals.
- So use `let` for numbers and expressions. If you change the line above to `have w : ℤ := 2 * n - 3 * a`, Lean only knows that `w` is some integer, and the `ring` on the last line cannot finish.
- You may also skip the name and write `use 2 * n - 3 * a` directly. A name helps when the witness is long or used again later.

### Combining two divisibility conditions with Bézout

> **Claim.** If $8\mid m$ and $5\mid m$, then $40\mid m$.

- Idea: $m=16m-15m$. Replace the $m$ in the first term by $5b$ and the $m$ in the second term by $8a$; then both terms are multiples of $40$.

> **Proof.** Assume $m=8a$ and $m=5b$. Then $m=16m-15m=16\cdot 5b-15\cdot 8a=40(2b-3a)$, so $40\mid m$. ∎

```lean
example {m : ℤ} : 8 ∣ m → 5 ∣ m → 40 ∣ m := by
  intro h1 h2
  obtain ⟨a, ha⟩ := h1        -- ha : m = 8 * a
  obtain ⟨b, hb⟩ := h2        -- hb : m = 5 * b
  use 2 * b - 3 * a
  calc
    m = 16 * m - 15 * m             := by ring
    _ = 16 * (5 * b) - 15 * (8 * a) := by rw [← hb, ← ha]
    _ = 40 * (2 * b - 3 * a)        := by ring
```

- The second line rewrites backwards: `rw [← hb]` turns `5 * b` back into `m`, and `rw [← ha]` turns `8 * a` back into `m`. After that both sides are the same, and the line is done.
- Coprimality matters: $4\mid 12$ and $6\mid 12$, but $24\nmid 12$. $4$ and $6$ are not coprime, and there is no $4x+6y=1$.

## Summary

- Even, odd and divides are "there exists"; so is congruence, once turned into divisibility. To use one, take out the witness; to prove one, hand over a witness.
- To prove that $a$ divides an expression, write it as $a\cdot(\ldots)$.

| Shape | What to do | In Lean |
|---|---|---|
| Hypothesis `P → Q` | Feed it a proof of $P$ to get $Q$ | `h hp` |
| Goal `P → Q` | Assume $P$, prove $Q$ | `intro hp` |
| Goal `P → False` | Assume $P$, derive a false fact | `intro hp`, derive e.g. `2 = 3`, finish with `norm_num at` |
| Hypothesis `Even n`, `a ∣ b`, `a ≡ b [ZMOD n]` | Take out the witness | `obtain ⟨k, hk⟩ := h` (congruence: first `rw [Int.modEq_iff_dvd] at h`) |
| Goal `Even n`, `a ∣ b`, `a ≡ b [ZMOD n]` | Hand over a witness | `use k` (congruence: first `rw [Int.modEq_iff_dvd]`) |
| For all integers, split by parity | Handle each of the two cases | `obtain h \| h := Int.even_or_odd n` |
| For all integers, split by remainder | Handle each remainder | `mod_cases hx : x % 3` |

- Naming: facts with `have`, numbers and expressions with `let`.
- Rewrite a hypothesis with `at h`; several at once with `at h1 h2 ⊢`.
- Integers: for integers, $2<k$ is $3\le k$.
- Congruences can be added, multiplied and raised to powers, so you can substitute in them as with equations.
- Two coprime numbers can make $1$: $ax+by=1$. Find $x$, $y$ with the Euclidean algorithm; use them to cancel a factor or to combine divisibility conditions.

**Next week**: a common shorthand for "if … then …", and how to prove "for all" in Lean.
