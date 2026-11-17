---
module: 6
title: Week 8 Student Handout
week: 8
audience: students
---

# Week 8 Student Handout: simp and Induction

- Section 1, `simp`: let Lean tidy up expressions automatically.
- Section 2, induction: ordinary induction, and induction from a starting point.
- Section 3, strong induction: read only. You get the Lean code and write the proof in words.
- The exercises are handed out separately: the In-class Practice (done in class) and the Homework. Each exercise names the section of this handout it practises.
- From this week on, write proofs in words the way you would on a blackboard or an exam: one step per line.

## 1. The `simp` family

- `simp` has a large set of "replace the left side by the right side" lemmas. It rewrites again and again until nothing changes. If the goal becomes `True`, the proof is done.
- It can rewrite underneath ∀ and ∃; `rw` cannot.

| Command | What it does |
|---|---|
| `simp` | tidy up the goal with the built-in lemmas |
| `simp [h₁, h₂]` | the built-in lemmas, plus the ones you give |
| `simp only [h₁, h₂]` | only the ones you give |
| `simp at h` | tidy up the hypothesis `h` |
| `simp_all` | tidy up all hypotheses and the goal together |
| `simp?` | do the same, and print which lemmas were used |

- `norm_num` and `push Not` belong to the same family: simp plus arithmetic on numbers, and simp plus the negation rules.
- `simp` may produce a form you did not expect: `0 < |x - 0|` becomes `¬x = 0`. Always look at the Infoview afterwards.
- `simp` often stops halfway. Finish the rest with another command.

### Example: the limit is not 0

> **Claim.** Suppose $f(x)=1$ for every $x>0$. Then $\displaystyle\lim_{x\to 0}f(x)=0$ is false.

- Idea: the example from Week 7, Section 3. Negate first: there is $\varepsilon>0$ such that for every $\delta>0$ there is an $x$ with $0<|x|<\delta$ and $|f(x)|\ge\varepsilon$.

> **Proof.** Take $\varepsilon=\tfrac12$.\
> Let $\delta>0$.\
> Take $x=\delta/2$.\
> Then $0<|x|=\delta/2<\delta$, and $|f(x)-0|=1\ge\tfrac12$. ∎

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε

example {f : ℝ → ℝ} (hpos : ∀ x, x > 0 → f x = 1) : ¬ Limit f 0 0 := by
  simp only [Limit]           -- unfold the definition
  push Not                    -- goal: ∃ ε > 0, ∀ δ > 0, ∃ x, (0 < |x - 0| ∧ |x - 0| < δ) ∧ ε ≤ |f x - 0|
  use 1 / 2                   -- take ε = 1/2
  constructor
  · norm_num
  · intro δ hδ                -- let δ > 0
    have hd : 0 < δ / 2 := half_pos hδ
    have h1 : |δ / 2| = δ / 2 := abs_of_pos hd
    have h2 : f (δ / 2) = 1 := hpos (δ / 2) hd
    have h3 : δ / 2 < δ := half_lt_self hδ
    use δ / 2                 -- take x = δ/2
    simp [h1, h2, h3]         -- what is left: 0 < δ ∧ 2⁻¹ ≤ 1
    norm_num [hδ]
```

- In Week 7 we rewrote the absolute values step by step. Here we hand the three facts `h1`, `h2`, `h3` to `simp`, and it removes the `- 0`, substitutes and simplifies by itself.

## 2. Induction

### Write down three things

- To prove "every natural number $n$ has $P(n)$":
  - **Base case**: prove $P(0)$.
  - **Inductive step**: let $k$ be arbitrary, assume $P(k)$, and prove $P(k+1)$.
- Before you start, write down: the statement $P(n)$, the hypothesis $P(k)$, and the target $P(k+1)$. Then look for $P(k)$ inside $P(k+1)$.
- Why this is enough: $P(0)$ gives $P(1)$, which gives $P(2)$, … Every number is reached.
- Lean: `induction n with`, split into `| zero =>` and `| succ k IH =>` (`IH` is $P(k)$).
- A recursive sequence is defined with `def`, one case per line. `rw [S]` or `simp [S]` unfolds one step.

> **Claim.** Let $S_0=0$ and $S_{n+1}=S_n+(2n+1)$ (the sum of the first $n$ odd numbers). Then $S_n=n^2$.

> **Proof.** By induction on $n$.\
> Base case: $S_0=0=0^2$.\
> Inductive step: assume $S_k=k^2$.\
> Then $S_{k+1}=S_k+(2k+1)=k^2+2k+1=(k+1)^2$. ∎

```lean
def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + (2 * n + 1)

example (n : ℕ) : S n = n ^ 2 := by
  induction n with
  | zero => simp [S]                                  -- base case
  | succ k IH =>                                      -- IH : S k = k ^ 2
    calc S (k + 1) = S k + (2 * k + 1) := by rw [S]   -- by the definition
      _ = k ^ 2 + (2 * k + 1) := by rw [IH]           -- by the inductive hypothesis
      _ = (k + 1) ^ 2 := by ring
```

### Starting from another number

- The base case becomes $P(m)$; the step becomes "let $k\ge m$; if $P(k)$ then $P(k+1)$".
- Find the starting point by trying small values first. For $2^n\le n!$: it fails at $n=2,3$ ($4>2$, $8>6$) and holds from $n=4$ on.
- Lean: with `hn : 4 ≤ n`, write `induction n, hn using Nat.le_induction with`, split into `| base =>` and `| succ k hk IH =>`.
- `gcongr`: "multiply or add the same thing on both sides" for inequalities. It turns `2 * a ≤ 2 * b` into `a ≤ b`, then looks for a proof among your hypotheses.

> **Claim.** For every $n\ge 4$, $2^n\le n!$.

> **Proof.** By induction on $n\ge 4$.\
> Base case: $2^4=16\le 24=4!$.\
> Inductive step: let $k\ge 4$ and assume $2^k\le k!$.\
> Then $2\le k+1$, so $2^{k+1}=2\cdot2^k\le(k+1)\cdot2^k\le(k+1)\cdot k!=(k+1)!$. ∎

```lean
example (n : ℕ) (hn : 4 ≤ n) : 2 ^ n ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => simp [Nat.factorial]                      -- 2 ^ 4 ≤ 4!
  | succ k hk IH =>                                   -- hk : 4 ≤ k, IH : 2 ^ k ≤ k!
    have h2 : 2 ≤ k + 1 := by
      calc 2 ≤ 4 + 1 := by norm_num
        _ ≤ k + 1 := by gcongr                        -- uses hk
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≤ (k + 1) * 2 ^ k := by gcongr                -- uses h2
      _ ≤ (k + 1) * k.factorial := by gcongr          -- uses IH
      _ = (k + 1).factorial := by rw [Nat.factorial_succ]
```

## 3. Strong induction

- To prove that every $n$ has $P(n)$: let $n$ be arbitrary, assume $P(m)$ for every $m<n$, and prove $P(n)$.
- The difference from ordinary induction: you may use any number smaller than $n$, not only $n-1$.
- Why it works: if there were a counterexample, take the smallest one, $q$. Every number below $q$ satisfies $P$, so the step gives $P(q)$, a contradiction.

### One way to write it

This is one possible layout, not the only one:

> By strong induction. Let $n$ be arbitrary.\
> If $n$ is (a small case), prove $P(n)$ directly.\
> Otherwise, take $m=\ldots$.\
> $m<n$, and $m$ is in the range of the hypothesis.\
> By the inductive hypothesis, $P(m)$: … (give new letters to what you get).\
> So … $P(n)$. ∎

- Say first that you use strong induction.
- Handle the small cases, where the hypothesis cannot be used, directly. They play the role of the base case.
- Before you use the hypothesis, check two things: $m$ is smaller than $n$, and $m$ is in the range the hypothesis covers (for example, $m\ge 1$).
- Give new letters to the variables you get from the hypothesis, separate from the ones you hand over.

### Reading strong induction in Lean

- Lean: `induction n using Nat.strong_induction_on with | _ n IH =>`. Use it as `IH m hm`, where `hm : m < n`.
- In this section you only read: understand the code, then write its proof in your own words. While reading, ask yourself four questions (no need to hand them in):
  1. What is $P(n)$? Look at the first line.
  2. Which cases does the proof split into?
  3. Which line uses the inductive hypothesis, and at which number?
  4. Why is that number smaller than $n$, and in the range?
- Once you can answer these, you can write the proof.

### Example: a power of 2 times an odd number

> **Claim.** Every $n\ge 1$ can be written as $n=2^a\cdot m$ with $m$ odd.

```lean
theorem two_pow_mul_odd (n : ℕ) : 1 ≤ n → ∃ a m, Odd m ∧ n = 2 ^ a * m := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd     -- n = k + k, or n is odd
    · have hk1 : 1 ≤ k := by
        by_contra h0
        simp_all
      have hlt : k < n := by
        rw [hk]
        exact Nat.lt_add_of_pos_right hk1
      obtain ⟨a, m, hm, hkm⟩ := IH k hlt hk1         -- the hypothesis is used at k
      exact ⟨a + 1, m, hm, by rw [hk, hkm]; ring⟩
    · exact ⟨0, n, hodd, by ring⟩
```

- (1) $P(n)$: if $n\ge 1$, then $n=2^a\cdot m$ with $m$ odd.
- (2) The cases: $n$ odd, and $n$ even ($n=k+k$).
- (3) `IH k hlt hk1`, at $k=n/2$.
- (4) `hlt : k < n`; `hk1 : 1 ≤ k` says that $k$ is in the range.

> **Proof.** By strong induction. Let $n\ge 1$.\
> If $n$ is odd, take $a=0$: $n=2^0\cdot n$.\
> Otherwise $n$ is even, $n=2k$.\
> $k<n$; and since $n\ge 1$, $k\ge 1$.\
> By the inductive hypothesis, $k=2^{a_0}\cdot m_0$ with $m_0$ odd.\
> Take $a=a_0+1$ and $m=m_0$. Then $n=2k=2^{a}\cdot m$. ∎

- $k=n/2$ is not $n-1$, so we need strong induction.

## Summary

- `simp` rewrites again and again, also underneath quantifiers; `simp only` uses only what you give it. Always look at the Infoview afterwards.
- Induction: write down $P(n)$, the hypothesis $P(k)$, and the target $P(k+1)$.
- The starting point need not be 0. Find it by trying small values.
- Use `gcongr` for the steps of an inequality.
- Strong induction: handle the small cases first; before using the hypothesis, check "smaller than $n$, and in the range".
- Write proofs in words one step per line.

**Next week**: functions.
