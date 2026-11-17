---
module: 4
title: Week 5 Student Handout
week: 5
audience: students
---

# Week 5 Student Handout: For All, Not, If and Only If

- Last week we learned "if … then …": prove it with `intro`, use it by feeding it a proof.
- This week adds three more shapes: "for all", "not" and "if and only if". With them, we can write the definition of a limit from calculus in Lean, in full.
- The exercises are handed out separately: the In-class Practice (done in class) and the Homework. Each exercise names the section of this handout it practises.

## 1. For all (∀)

### Using a "for all" hypothesis: plug in a value

- In words: "By assumption, taking $x=a$, we get …"
- In Lean: if you have `h : ∀ x, P x`, then `h a` is a proof of `P a`. You did this in Week 3: for the additive-function rule `h`, `h 0 0` was "put in $x=y=0$".
- Most "for all" statements in mathematics carry a condition: `∀ x, P x → Q x`. To use one, hand over **two** things: the value, and a proof of the condition. `h a ha` is `Q a`; `h a` alone is only `P a → Q a`.
- `∀ ε > 0, …` is short for `∀ ε, ε > 0 → …`. For example, from `h : ∀ ε > 0, x < y + ε`, the term `h 1 (by norm_num)` is a proof of `x < y + 1`.

### Proving a "for all" goal: `intro`

- In words: "Let $x$ be arbitrary." Then prove $P(x)$.
- In Lean: `intro x`. It is the same command that proved "if … then …" last week.
- Why the same command? Both say "give me something first, and I will give you a proof":
  - `P → Q`: give me a proof of $P$, and I give you a proof of $Q$.
  - `∀ x, P x`: give me an $x$, and I give you a proof of `P x`.
- For a "for all" with a condition, `intro x hx` takes out the value and the condition at once.

> **Claim.** Let $x$, $y$ be real numbers. If $x\le y$, then $x<y+\varepsilon$ for every $\varepsilon>0$.
>
> **Proof.** Assume $x\le y$. Let $\varepsilon>0$ be arbitrary. Since $x\le y$ and $\varepsilon>0$, we get $x=x+0<y+\varepsilon$. ∎

```lean
example {x y : ℝ} (h : x ≤ y) : ∀ ε > 0, x < y + ε := by
  intro ε hε                         -- let ε be arbitrary, assume hε : ε > 0
  exact lt_add_of_le_of_pos h hε
```

- `lt_add_of_le_of_pos : b ≤ c → 0 < a → b < c + a`.
- The converse is also true: if $x<y+\varepsilon$ for every $\varepsilon>0$, then $x\le y$. Analysis uses this all the time to compare two numbers: "they differ by less than any positive number". The converse needs proof by contradiction; see §2.

### Order of quantifiers: the definition of a limit

- In calculus, $\displaystyle\lim_{x\to a}f(x)=L$ means: for every $\varepsilon>0$ there is a $\delta>0$ such that for every $x$, if $0<|x-a|<\delta$, then $|f(x)-L|<\varepsilon$.
- That is four layers: "for all, there exists, for all, if … then …". Work from the outside in: let $\varepsilon$ be arbitrary, choose $\delta$, let $x$ be arbitrary, assume the condition.
- $\delta$ may be written in terms of $\varepsilon$, because $\varepsilon$ comes first; $\delta$ may not depend on $x$, because $x$ comes later.

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
```

- `∃ δ > 0, …` is short for `∃ δ, δ > 0 ∧ …`. So after `use δ` you must prove an "and"; split it into two goals with `constructor` (§3 explains it properly).

> **Claim.** If $f(x)=x+1$ for every real $x$, then $\displaystyle\lim_{x\to 2}f(x)=3$.

- Idea: $|f(x)-3|=|x-2|$. For this to be less than $\varepsilon$, it is enough that $|x-2|<\varepsilon$. Take $\delta=\varepsilon$.

> **Proof.** Let $\varepsilon>0$ be arbitrary. Take $\delta=\varepsilon$. Let $x$ be arbitrary and assume $0<|x-2|<\delta$. Then $|f(x)-3|=|x+1-3|=|x-2|<\varepsilon$. ∎

```lean
example {f : ℝ → ℝ} (hf : ∀ x, f x = x + 1) : Limit f 2 3 := by
  intro ε hε                -- let ε be arbitrary, assume hε : ε > 0
  use ε                     -- take δ = ε
  constructor
  · exact hε                -- δ > 0
  · intro x hx              -- let x be arbitrary, assume 0 < |x - 2| ∧ |x - 2| < ε
    obtain ⟨h0, h1⟩ := hx
    rw [hf x]
    calc
      |x + 1 - 3| = |x - 2| := congrArg abs (by ring)
      _ < ε                 := h1
```

- `congrArg abs (by ring)`: the expressions inside the absolute values are equal (by `ring`), so the absolute values are equal. This is Week 2's `congrArg`.

> **Claim.** If $f(x)=3x+1$ for every real $x$, then $\displaystyle\lim_{x\to 2}f(x)=7$.

- Idea: $|f(x)-7|=3|x-2|$. For this to be less than $\varepsilon$, it is enough that $|x-2|<\varepsilon/3$. Take $\delta=\varepsilon/3$.

> **Proof.** Let $\varepsilon>0$ be arbitrary. Take $\delta=\varepsilon/3>0$. Let $x$ be arbitrary and assume $0<|x-2|<\delta$. Then $|f(x)-7|=|3x+1-7|=|3(x-2)|=3|x-2|<3\cdot\frac{\varepsilon}{3}=\varepsilon$. ∎

```lean
example {f : ℝ → ℝ} (hf : ∀ x, f x = 3 * x + 1) : Limit f 2 7 := by
  intro ε hε
  use ε / 3
  constructor
  · exact div_pos hε (by norm_num)
  · intro x hx
    obtain ⟨h0, h1⟩ := hx
    rw [hf x]
    calc
      |3 * x + 1 - 7| = |3 * (x - 2)| := congrArg abs (by ring)
      _ = |3| * |x - 2|               := abs_mul 3 (x - 2)
      _ = 3 * |x - 2|                 := by norm_num
      _ < 3 * (ε / 3)                 := mul_lt_mul_of_pos_left h1 (by norm_num)
      _ = ε                           := by ring
```

- Lemmas used:
  - `div_pos : 0 < a → 0 < b → 0 < a / b`
  - `abs_mul a b : |a * b| = |a| * |b|`
  - `mul_lt_mul_of_pos_left : b < c → 0 < a → a * b < a * c`
- In both examples the condition $0<|x-2|$ is never used: it only excludes the point $x=2$ itself (as in Week 3, Exercise 6.2).

## 2. Not (¬)

### `¬P` is `P → False`

- The `P → False` we wrote all last week has a short name in Lean: `¬P`, read "not $P$". They are exactly the same statement.
- **Prove** `¬P`: as last week, `intro h` to assume $P$, then reach a contradiction.
- **Use** `hn : ¬P`: it is an "if … then …", so feeding it a proof of $P$ gives `False`. When you hold both `hp : P` and `hn : ¬P`, `hn hp` is a contradiction.
- `a ≠ b` is short for `¬(a = b)`.

### Three ways to use a contradiction

1. **The hypotheses contradict each other**: they lead to a false fact (such as $2=3$), and then any goal is proved. This is last week's `norm_num at h`.
2. **Proving a negation `¬P`**: assume $P$ and reach a contradiction. This is just what `¬` means.
3. **Proving a positive statement $P$**: assume `¬P` and reach a contradiction; therefore $P$ holds. This is **proof by contradiction**. In Lean, `by_contra h` assumes `h : ¬P` and changes the goal to `False`.
   - Ways 2 and 3 are different: in way 2 the goal already is a negation; in way 3 the goal is not a negation, and we add the negation ourselves.
   - Why is way 3 allowed? Because every statement is either true or false (the "law of excluded middle" of Module 5, next week). When way 1 or 2 works, you do not need way 3.

> **Claim.** Let $x$, $y$ be real numbers. If $x<y+\varepsilon$ for every $\varepsilon>0$, then $x\le y$.
>
> **Proof.** Suppose $x\le y$ is false, that is, $y<x$. Then $x-y>0$, so we may put $\varepsilon=x-y$ into the assumption. This gives $x<y+(x-y)=x$, a contradiction. Hence $x\le y$. ∎

```lean
example {x y : ℝ} (h : ∀ ε > 0, x < y + ε) : x ≤ y := by
  by_contra hxy                              -- assume hxy : ¬ x ≤ y; the goal is False
  rw [not_le] at hxy                         -- hxy becomes y < x
  have h1 : x < y + (x - y) := h (x - y) (sub_pos.mpr hxy)
  rw [add_sub_cancel] at h1                  -- h1 becomes x < x
  norm_num at h1
```

- This is the converse of the claim in §1. The key step is **choosing $\varepsilon$**: the assumption holds for every $\varepsilon$, so we pick one that causes trouble.
- Lemmas used:
  - `not_le : ¬a ≤ b ↔ b < a`
  - `sub_pos : 0 < a - b ↔ b < a` (`.mpr` reads it from right to left; §3 explains it properly)
  - `add_sub_cancel a b : a + (b - a) = b`

### Negation meets quantifiers

- **"Not for all" = "some fails"**: `¬ (∀ x, P x)` is equivalent to `∃ x, ¬ P x`. To refute a "for all", a single **counterexample** is enough.
- **"None exists" = "every one fails"**: `¬ (∃ x, P x)` is equivalent to `∀ x, ¬ P x`. Last week's $5\nmid 12$ has this shape: there is no $k$ with $12=5k$, that is, every $k$ makes $12=5k$ false.
- The Mathlib lemmas:
  - `not_forall : ¬(∀ x, P x) ↔ ∃ x, ¬P x`
  - `not_exists : ¬(∃ x, P x) ↔ ∀ x, ¬P x`
- They are "if and only if" statements, so `rw` can rewrite with them, just like `abs_lt`.

> **Claim.** The statement "for every real $x$, if $x<1$, then $x^2<x$" is false.

- Idea: multiplying both sides of $x<1$ by $x$ gives $x^2<x$, but only when $x>0$; when $x$ is negative the inequality flips. So look for a negative counterexample.

> **Proof.** We show that for some $x$, "if $x<1$, then $x^2<x$" fails. Take $x=-1$: $-1<1$, but $(-1)^2=1>-1$. ∎

```lean
example : ¬ (∀ x : ℝ, x < 1 → x ^ 2 < x) := by
  rw [not_forall]                              -- the goal becomes ∃ x, ¬ (x < 1 → x ^ 2 < x)
  use -1
  intro h                                      -- assume h : -1 < 1 → (-1) ^ 2 < -1
  have h1 : (-1 : ℝ) ^ 2 < -1 := h (by norm_num)
  norm_num at h1
```

- A counterexample must satisfy the condition ($-1<1$) **and** make the conclusion fail ($1>-1$). A value that makes the conclusion fail but does not satisfy the condition is not a counterexample.

## 3. If and only if (↔)

### Proving an "if and only if" goal: two directions

- In words: "($\Rightarrow$) Assume $P$. … So $Q$. ($\Leftarrow$) Assume $Q$. … So $P$." The two directions are two separate proofs.
- In Lean: `constructor` splits `P ↔ Q` into the two goals `P → Q` and `Q → P`.
- `constructor` means "prove the statement the way it is built": `↔` is built from two directions and `∧` from two halves, so it also splits an "and" (that is how we used it after `use δ` in §1).
- It does not replace `use`: when the goal is "there exists", first hand over a witness with `use`. `constructor` will not choose the witness for you.

> **Claim.** For every integer $n$, $8\mid 5n$ if and only if $8\mid n$.
>
> **Proof.** ($\Rightarrow$) This is last week's §4 example: assume $5n=8a$; then $n=16n-3\cdot(5n)=8(2n-3a)$. ($\Leftarrow$) Assume $n=8a$; then $5n=8\cdot 5a$. ∎

```lean
example {n : ℤ} : 8 ∣ 5 * n ↔ 8 ∣ n := by
  constructor
  · intro h                    -- (⇒) assume 8 ∣ 5n
    obtain ⟨a, ha⟩ := h
    use 2 * n - 3 * a
    calc
      n = 16 * n - 3 * (5 * n) := by ring
      _ = 16 * n - 3 * (8 * a) := by rw [ha]
      _ = 8 * (2 * n - 3 * a)  := by ring
  · intro h                    -- (⇐) assume 8 ∣ n
    obtain ⟨a, ha⟩ := h
    use 5 * a
    calc
      5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a)     := by ring
```

- The two directions are not equally hard: ($\Leftarrow$) works for any multiplier; ($\Rightarrow$) needs $5$ and $8$ to be coprime.

### Using an "if and only if": pick a direction, or rewrite

- Given `h : P ↔ Q`:
  - `h.mp` is `P → Q` (left to right) and `h.mpr` is `Q → P` (right to left). For example, with `hp : P`, `h.mp hp` is a proof of $Q$.
  - `rw [h]` replaces $P$ by $Q$ in the goal, like rewriting with an equation.
- You have done this before: `abs_lt` and `Int.modEq_iff_dvd` are "if and only if" statements.

### Chaining "if and only if": `calc`

- Like equations, "if and only if" statements can be chained: $P\iff Q$ and $Q\iff R$ give $P\iff R$. Lean's `calc` can chain `↔` too; each line is one "if and only if".
- Example: congruence, divisibility and "there exists" are three ways of writing the same thing.

```lean
example {a b n : ℤ} : a ≡ b [ZMOD n] ↔ ∃ c, b - a = n * c := by
  calc
    a ≡ b [ZMOD n] ↔ n ∣ b - a := Int.modEq_iff_dvd
    _ ↔ ∃ c, b - a = n * c    := Iff.rfl
```

- `Iff.rfl` on the second line: `n ∣ b - a` is defined as `∃ c, b - a = n * c`, so both sides are the same statement, just as `rfl` proves an equation whose two sides are the same.

## 4. Unique existence (∃!)

- "There is exactly one $x$ with $P(x)$" = "there exists" plus "at most one":
  - There exists: some $x$ satisfies $P(x)$.
  - At most one: every $y$ that satisfies $P$ equals that $x$.
- In Lean this is written `∃! x, P x`.
- "At most one" can also be said another way: there are no two **different** things that both satisfy $P$. Exercise 5 shows that the first way implies the second.

## Summary

| Shape | Prove (goal) | Use (hypothesis) |
|---|---|---|
| `∀ x, P x` | Let it be arbitrary: `intro x` | Plug in a value: `h a` |
| `∀ x, P x → Q x` | `intro x hx` | Hand over the value and the condition: `h a ha` |
| `¬P` (that is, `P → False`) | `intro h`, reach a contradiction | Feed it $P$: `hn hp : False` |
| `¬ ∀ x, P x` | `rw [not_forall]`, give a counterexample | Feed it a proof of `∀ x, P x` to get `False` |
| `¬ ∃ x, P x` | `rw [not_exists]`, let $x$ be arbitrary and prove `¬P x` | Feed it a witness: `hne ⟨x, hx⟩ : False` |
| A positive $P$, by contradiction | `by_contra h`, reach a contradiction | |
| `P ↔ Q` | `constructor`, prove each direction | `h.mp`, `h.mpr`, or `rw [h]` |

- `∀` and `→` are both proved with `intro`, and both are used by feeding them something.
- Handle quantifiers from the outside in. A later witness may depend on the variables taken earlier; an earlier one may not depend on later ones.
- The definition of a limit is "∀ε ∃δ ∀x, if … then …": let $\varepsilon$ be arbitrary, choose $\delta$, let $x$ be arbitrary, assume the condition, then estimate.
- To refute a "for all", give a counterexample; to refute a "there exists", show that every candidate fails.
- "If and only if" statements can be chained with `calc`, like equations.
- "Exactly one" = "there exists" + "at most one".

**Next week**: the complete rules for negation (negation meets "and", "or", "if … then …"), and the law of excluded middle behind proof by contradiction.
