---
module: 5
title: Week 7 Student Handout
week: 7
audience: students
---

# Week 7 Student Handout: Logic

- Every shape from the last five weeks (if … then, not, and, or, if and only if, for all, there exists) is collected in one table: for each shape, how to write it in words and how to write it in Lean.
- After that, two new things: the law of excluded middle (`by_cases`), and writing down the negation of a statement systematically.
- The exercises are handed out separately: the In-class Practice (done in class) and the Homework. Each exercise names the section of this handout it practises.

## 1. How to prove and use each shape

- When you read a statement, look at its **outermost** shape first. It decides the next step: to prove it, follow the "Prove" column; if you have it as a hypothesis, follow the "Use" column.
- After you remove one layer, what is left has its own outermost shape. Look it up again.

In each cell, the first line is how to write it in words, and the second line is the Lean.

| Shape | Prove (goal) | Use (hypothesis) |
|---|---|---|
| $P\to Q$ | "Assume $P$. … So $Q$."<br>`intro hp` | "From $P\to Q$ and $P$, we get $Q$."<br>`h hp` |
| $\neg P$ | "Assume $P$. … Contradiction. So $P$ fails."<br>`intro hp`; the goal becomes `False` | "$P$ and $\neg P$ contradict each other."<br>`hn hp : False` |
| $P\wedge Q$ | "First we prove $P$. … Next we prove $Q$. …"<br>`⟨hp, hq⟩` or `constructor` | "From $P$ and $Q$, we get $P$ (and $Q$)."<br>`h.1`, `h.2` or `obtain ⟨hp, hq⟩ := h` |
| $P\vee Q$ | "We prove $P$." (pick a side)<br>`left` / `right` | "There are two cases. If $P$, … If $Q$, …"<br>`obtain hp \| hq := h` |
| $P\leftrightarrow Q$ | "($\Rightarrow$) Assume $P$, … ($\Leftarrow$) Assume $Q$, …"<br>`constructor` | "From $P\leftrightarrow Q$ and $P$, we get $Q$."<br>`h.mp`, `h.mpr`, `rw [h]` |
| $\forall x\in A,\ P(x)$ | "Let $x\in A$ be arbitrary. … So $P(x)$."<br>`intro x hx` | "By assumption, taking $x=a$, we get $P(a)$."<br>`h a ha` |
| $\exists x\in A,\ P(x)$ | "Take $x=a$." Check $a\in A$ and $P(a)$.<br>`use a` | "By assumption, there is $x_0\in A$ with $P(x_0)$."<br>`obtain ⟨x, hx⟩ := h` |
| A positive $P$, by contradiction | "Suppose $P$ fails. … Contradiction. So $P$."<br>`by_contra h` | |

- Using a hypothesis produces new variables or facts. Give them new names. A variable comes from one of three places: it was taken arbitrary, it came out of an "exists", or you chose it.
- `∀ ε > 0, …` is short for `∀ ε, ε > 0 → …`, and `∃ δ > 0, …` is short for `∃ δ, δ > 0 ∧ …`. So after `use δ` you still have to prove an "and".

### Example: passing an "exists" along a "for all"

> **Claim.** Let `P` and `Q` be properties of the elements of a type `α`. If $P(x)$ implies $Q(x)$ for every $x$, and some $x$ has $P(x)$, then some $x$ has $Q(x)$.

- Idea: the conclusion needs a witness. The only candidate we have is the $x_0$ from the second assumption; the first assumption carries $P(x_0)$ to $Q(x_0)$.

> **Proof.** Assume that $P(x)$ implies $Q(x)$ for every $x$, and that some $x$ has $P(x)$; call this $x$ $x_0$. Take $x=x_0$. By the first assumption at $x=x_0$, $P(x_0)$ gives $Q(x_0)$. ∎

```lean
example {α : Type} (P Q : α → Prop) :
    (∀ x, P x → Q x) → (∃ x, P x) → ∃ x, Q x := by
  intro h hex                  -- Assume that P(x) implies Q(x) for every x, and that some x has P(x).
  obtain ⟨x₀, hx₀⟩ := hex      -- Call this x x₀.
  use x₀                       -- Take x = x₀.
  exact h x₀ hx₀               -- By the first assumption at x = x₀, P(x₀) gives Q(x₀).
```

- The comments are the proof in words, sentence by sentence. Each sentence is one cell of the table: proving two "if … then"s, using an "exists", proving an "exists", using a "for all".
- The order matters: `obtain` must give you $x_0$ before you can `use x₀`. A witness has to be something you already have.

### Example: the limit of a sum

Recall the definition from Week 5:

```lean
def Limit (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - L| < ε
```

Proofs about limits are mostly about absolute values. The most common moves:

| Task | Mathematics | Lean |
|---|---|---|
| Split an absolute value into two inequalities | $\lvert y\rvert<b \iff -b<y<b$ | `abs_lt : \|a\| < b ↔ -b < a ∧ a < b` |
| Replace the inside by an equal expression | $\lvert 3x+1-7\rvert=\lvert 3(x-2)\rvert$ | `congrArg abs (by ring)` |
| Triangle inequality | $\lvert a+b\rvert\le\lvert a\rvert+\lvert b\rvert$ | `abs_add_le a b : \|a + b\| ≤ \|a\| + \|b\|` |
| Split a product | $\lvert ab\rvert=\lvert a\rvert\,\lvert b\rvert$ | `abs_mul a b : \|a * b\| = \|a\| * \|b\|` |
| Drop the bars of a positive number | $a>0 \Rightarrow \lvert a\rvert=a$ | `abs_of_pos : 0 < a → \|a\| = a` |

> **Claim.** If $\displaystyle\lim_{x\to a}f(x)=L$ and $\displaystyle\lim_{x\to a}g(x)=M$, then $\displaystyle\lim_{x\to a}\big(f(x)+g(x)\big)=L+M$.

- Idea: we want $|f(x)+g(x)-(L+M)|<\varepsilon$. It is at most $|f(x)-L|+|g(x)-M|$, so make each term less than $\varepsilon/2$. Putting $\varepsilon/2$ into the two assumptions gives two $\delta$'s; both conditions must hold, so take the smaller one.

> **Proof.** Let $\varepsilon>0$. By the first assumption with $\varepsilon/2$, there is $\delta_1>0$ such that $|f(x)-L|<\varepsilon/2$ whenever $0<|x-a|<\delta_1$. Likewise there is $\delta_2>0$ such that $|g(x)-M|<\varepsilon/2$ whenever $0<|x-a|<\delta_2$. Take $\delta=\min(\delta_1,\delta_2)>0$. Let $x$ satisfy $0<|x-a|<\delta$. Then $|x-a|<\delta_1$ and $|x-a|<\delta_2$, so $|f(x)-L|<\varepsilon/2$ and $|g(x)-M|<\varepsilon/2$. Therefore
> $$|f(x)+g(x)-(L+M)|\le|f(x)-L|+|g(x)-M|<\tfrac{\varepsilon}{2}+\tfrac{\varepsilon}{2}=\varepsilon.\ ∎$$

```lean
example {f g : ℝ → ℝ} {a L M : ℝ} (hf : Limit f a L) (hg : Limit g a M) :
    Limit (fun x => f x + g x) a (L + M) := by
  intro ε hε                                        -- Let ε > 0.
  have hε2 : ε / 2 > 0 := div_pos hε (by norm_num)
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf (ε / 2) hε2           -- By the first assumption with ε/2, there is δ₁ > 0 ...
  obtain ⟨δ₂, hδ₂, h₂⟩ := hg (ε / 2) hε2           -- Likewise there is δ₂ > 0 ...
  use min δ₁ δ₂                                     -- Take δ = min(δ₁, δ₂)
  constructor
  · exact lt_min hδ₁ hδ₂                            -- > 0.
  · intro x hx                                      -- Let x satisfy 0 < |x - a| < δ.
    obtain ⟨h0, hlt⟩ := hx
    have hlt1 : |x - a| < δ₁ := lt_of_lt_of_le hlt (min_le_left δ₁ δ₂)    -- Then |x - a| < δ₁
    have hlt2 : |x - a| < δ₂ := lt_of_lt_of_le hlt (min_le_right δ₁ δ₂)   -- and |x - a| < δ₂,
    have e1 : |f x - L| < ε / 2 := h₁ x ⟨h0, hlt1⟩                         -- so |f(x) - L| < ε/2
    have e2 : |g x - M| < ε / 2 := h₂ x ⟨h0, hlt2⟩                         -- and |g(x) - M| < ε/2.
    calc                                                                   -- Therefore
      |f x + g x - (L + M)| = |(f x - L) + (g x - M)| := congrArg abs (by ring)
      _ ≤ |f x - L| + |g x - M|                       := abs_add_le (f x - L) (g x - M)
      _ < ε / 2 + ε / 2                               := add_lt_add e1 e2
      _ = ε                                           := by ring
```

- Again, the comments are the proof in words, sentence by sentence.
- `h₁ x ⟨h0, hlt1⟩`: the condition that `h₁` asks for is an "and", so we hand over a pair.
- The Infoview shows the goal as `|(fun x => f x + g x) x - (L + M)| < ε`. `(fun x => f x + g x) x` just means `f x + g x`; the first line of the `calc` can write `f x + g x` directly, and Lean accepts it.

## 2. Excluded middle: `by_cases`

- **The law of excluded middle**: every statement $P$ either holds or fails. So you can split into cases on any statement; you do not need an "or" in hand first.
- In words: "There are two cases: $P$ holds, or $P$ fails." In Lean: `by_cases h : P`. The first case has `h : P`, the second has `h : ¬P`.

> **Claim.** Let $P$ and $Q$ be statements. If $P$ and $Q$ do not both hold, then $P$ fails or $Q$ fails.

- Idea: to prove an "or" we must say which side holds. The assumption only says that the two do not both hold; it does not say which one fails. So we split into cases on $P$.

> **Proof.** Assume that $P$ and $Q$ do not both hold. There are two cases. If $P$ holds, we show that $Q$ fails: suppose $Q$ holds; then $P$ and $Q$ both hold, a contradiction. If $P$ fails, the left side of the conclusion holds. ∎

```lean
example (P Q : Prop) (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_cases hp : P             -- There are two cases. If P holds,
  · right                     -- we show that Q fails:
    intro hq                  -- suppose Q holds;
    exact h ⟨hp, hq⟩          -- then P and Q both hold, a contradiction.
  · left                      -- If P fails, the left side of the conclusion holds.
    exact hp
```

- **The contrapositive** also relies on excluded middle. To get "if $P$ then $Q$" from "if $\neg Q$ then $\neg P$", assume $P$ and split into cases on $Q$. If $Q$ holds, we are done. If $Q$ fails, then $\neg P$, which contradicts $P$.

## 3. Negation and disproof

### The rules of negation

| Statement | Its negation |
|---|---|
| $P\wedge Q$ | $\neg P\vee\neg Q$ |
| $P\vee Q$ | $\neg P\wedge\neg Q$ |
| $P\to Q$ | $P\wedge\neg Q$ |
| $\neg P$ | $P$ |
| $\forall x\in A,\ P(x)$ | $\exists x\in A,\ \neg P(x)$ |
| $\exists x\in A,\ P(x)$ | $\forall x\in A,\ \neg P(x)$ |
| $a<b$ | $a\ge b$ |
| $a\le b$ | $a>b$ |

- Apply the rules from the outside in, one layer at a time. **The range does not change**: the negation of "every $x>0$ has …" is "some $x>0$ does not have …".
- To disprove a "for all", give one counterexample. To disprove an "exists", you must argue for an arbitrary $x$; examples are not enough.
- In Lean, `push Not` applies these rules and rewrites the goal into its negated form in one step. For example, `¬ (∀ x y : ℝ, x < y → x ^ 2 < y ^ 2)` becomes `∃ x y, x < y ∧ y ^ 2 ≤ x ^ 2`. In the proof in words, always write out the negation by hand. In Lean, before you use `push Not`, write your predicted goal in a comment.

### Example: the limit is not 0

> **Claim.** Suppose $f(x)=1$ for every $x>0$. Then $\displaystyle\lim_{x\to 0}f(x)=0$ is false.

- Idea: first negate by hand. $\lim_{x\to 0}f(x)=0$ says "$\forall\varepsilon>0,\ \exists\delta>0,\ \forall x,\ 0<|x|<\delta\to|f(x)|<\varepsilon$". From the outside in:
  1. $\exists\varepsilon>0,\ \neg\big(\exists\delta>0,\ \forall x,\ \ldots\big)$
  2. $\exists\varepsilon>0,\ \forall\delta>0,\ \neg\big(\forall x,\ 0<|x|<\delta\to|f(x)|<\varepsilon\big)$
  3. $\exists\varepsilon>0,\ \forall\delta>0,\ \exists x,\ \neg\big(0<|x|<\delta\to|f(x)|<\varepsilon\big)$
  4. $\exists\varepsilon>0,\ \forall\delta>0,\ \exists x,\ 0<|x|<\delta\ \wedge\ |f(x)|\ge\varepsilon$
- So we choose $\varepsilon$, take $\delta$ arbitrary, and choose $x$ (which may depend on $\delta$). Take $\varepsilon=\tfrac12$ and $x=\delta/2$.

> **Proof.** Take $\varepsilon=\tfrac12$. Let $\delta>0$. Take $x=\delta/2$. Then $0<|x|=\delta/2<\delta$, and $|f(x)-0|=1\ge\tfrac12$. ∎

```lean
example {f : ℝ → ℝ} (hpos : ∀ x, x > 0 → f x = 1) : ¬ Limit f 0 0 := by
  intro h                                   -- assume the limit is 0; the goal is False
  obtain ⟨δ, hδ, hx⟩ := h (1 / 2) (by norm_num)
  have hd : 0 < δ / 2 := half_pos hδ
  have habs : |δ / 2 - 0| = δ / 2 := by
    rw [sub_zero]
    exact abs_of_pos hd
  have h0 : 0 < |δ / 2 - 0| := by
    rw [habs]
    exact hd
  have hlt : |δ / 2 - 0| < δ := by
    rw [habs]
    exact half_lt_self hδ
  have h1 : |f (δ / 2) - 0| < 1 / 2 := hx (δ / 2) ⟨h0, hlt⟩
  rw [hpos (δ / 2) hd] at h1                -- h1 : |1 - 0| < 1 / 2
  norm_num at h1
```

- The Lean proves $\neg$ as the table says: assume the limit is 0, put in the same $\varepsilon=\tfrac12$ and $x=\delta/2$, and get $1<\tfrac12$. The $\delta$ comes out of the assumption and we cannot choose it; that is the "let $\delta>0$" of the proof in words.

## Summary

- How to prove and use each shape: see the table in Section 1. Read a statement from the outside in, and look up the table again after each layer.
- Excluded middle: any statement can be split into the cases "holds" and "fails" (`by_cases`). Proof by contradiction and the contrapositive both rely on it.
- Negate from the outside in, keeping the range. The negation of "if … then" is an "and".
- To disprove a "for all", give a counterexample; to disprove an "exists", argue for an arbitrary element.

**Next week**: mathematical induction.
