---
module: 2
title: Week 3 Student Handout
week: 3
audience: students
---

# Week 3 Student Handout: Giving a Proof Its Shape

- Last week every proof was one chain, calculated from start to finish.
- This week proofs branch:
  - Prove a fact first, then use it.
  - Use a rule that holds for every value.
  - Split into cases and handle each one.
  - Hand over a specific number.
- The goal this week: **see the shape of a statement, and do what that shape asks for.**
- The last section uses the same constructions to define new mathematical objects of your own.
- Exercises marked **[In class]** are done in class: write the proof in words first (hand it in as a `.md` file), then the Lean. The other exercises are homework.

## 0. How to write a proof in words

### The shape of the statement decides the first sentence

| To prove | How to write it |
|---|---|
| If $P$, then $Q$ | "Assume $P$." Then prove $Q$. |
| $P$ and $Q$ | "First we prove $P$." When done, prove $Q$. |
| There exists $x\in A$ with $P(x)$ | "Take $x=\ldots$." Then check two things: $x\in A$, and $P(x)$. |
| For all $x\in A$, $P(x)$ | "Let $x\in A$ be arbitrary." Then prove $P(x)$.<br>$x$ is arbitrary: you may not pick a particular value. |

**Examples**

- There exists: "There is a positive real $x$ with $x^2>3$."
  - "Take $x=2$. Then $x>0$, and $x^2=4>3$."
- For all: "For every real $x\ge 1$, $x^2\ge x$."
  - "Let $x\ge 1$ be an arbitrary real number. Since $x\ge 1>0$, multiplying both sides by $x$ keeps the direction, so $x\cdot x\ge 1\cdot x$, that is, $x^2\ge x$."

**Notes**

- When shapes are nested, handle them one layer at a time.
- $A$ is the range of the variable: all reals, the positive reals, a subspace $W$, and so on. The first sentence names the range: "Let $x$ be an arbitrary real number", "Let $\varepsilon>0$ be arbitrary", "Let $u\in W$ be arbitrary".
- Why does taking **one** arbitrary $x$ prove the statement for **all** $x$?
  - After "let $x$ be arbitrary", all you know about $x$ is $x\in A$. The proof uses no other property of it.
  - So if you replace $x$ by any specific element of $A$, every step of the proof is still correct. That means the statement holds for every $x\in A$.
  - For the same reason, you may not add conditions halfway through, such as "let $x=2$". Then the proof only works for $2$.
- "There exists $x\in A$ with $P(x)$" means "there exists $x$ such that $x\in A$ **and** $P(x)$". So both $x\in A$ and $P(x)$ must be checked.
  - $x\in A$ can also be written in other ways. For example, "there exists $x\in\{r\in \mathbb{R}\ |\ r>0\}$ with $P(x)$" can be written "there exists $x>0$ with $P(x)$".

### Every variable has one of three sources

| Source | Who decides it | How to write it |
|---|---|---|
| Arbitrary | The reader: any value at all | "Let $x$ be an arbitrary real number." |
| From "there exists" | The hypothesis: you only know it exists | "Since $a$ is a multiple of 3, there is an integer $k$ with $a=3k$." |
| Your choice | You: you name a value | "Take $y=x+1$." |

- Before a variable appears, say where it comes from.
- Two variables from different sources get different letters.

### Idea and proof

- The idea can run backwards: "To prove A it is enough to have B; to have B it is enough to have C."
- The proof must run forwards: "Since C, we get B, and so A."

**Example A: writing forwards**

> **Claim.** For every real $x$, $x^2+1\ge 2x$.

- Idea: we want $x^2+1\ge 2x$. Moving terms over gives $x^2-2x+1\ge 0$, which is $(x-1)^2\ge 0$. That is true.

> **Proof.** Let $x$ be an arbitrary real number. A square is never negative, so $(x-1)^2\ge 0$. Expanding gives $x^2-2x+1\ge 0$. Adding $2x$ to both sides gives $x^2+1\ge 2x$. ∎

- The proof reverses the idea: it starts from $(x-1)^2\ge 0$, not from the statement $x^2+1\ge 2x$ we want.

**Example B: for all, there exists**

> **Claim.** For every real $M$, there exists a real $x$ with $2x-1>M$.

- Idea: we want $2x-1>M$, that is, $x>\frac{M+1}{2}$. Take something a bit larger, for example $x=\frac{M+2}{2}$.

> **Proof.** Let $M$ be an arbitrary real number. Take $x=\frac{M+2}{2}$. Then $2x-1=(M+2)-1=M+1>M$. Since $M$ was arbitrary, the claim holds. ∎

- Why may $x$ be written in terms of $M$?
  - "For every $M$ there exists $x$ …" means: each $M$ has its own $x$. Different $M$ may get different $x$.
  - So after "let $M$ be arbitrary", it is enough to find an $x$ for this one $M$. Of course $x$ may be written in terms of $M$.
- Why may $M$ not be written in terms of $x$?
  - $M$ must be arbitrary, so that the proof covers every $M$.
  - If $M$ depended on $x$, we would only have proved the claim for some $M$, not all.
- Swap the two quantifiers and the meaning changes: "there exists $x$ such that for every $M$ …" asks for **one** $x$ that works for all $M$. Then $x$ may not change with $M$.
- Every $\varepsilon$-$\delta$ proof in calculus has this skeleton: "Let $\varepsilon>0$ be arbitrary. Take $\delta=\ldots$. Check …". For the same reason, $\delta$ may be written in terms of $\varepsilon$, and $\varepsilon$ may not be written in terms of $\delta$.

### Exercise 1

Prove: for every real $M$, there exists a **positive** real $x$ with $x^2>M$.

1. Write the proof in words. After taking $x$, check two things: $x>0$, and $x^2>M$. Hint: $M$ may be negative.
2. Could your $x$ be chosen before "let $M$ be arbitrary"? Answer "yes" or "no", then give your reason in one or two sentences.

## 1. Intermediate facts and rules

`have` proves a small fact first and gives it a name, so that you can use it later. In a proof in words, this is "First we show …".

> **Claim.** If $f$ satisfies $f(x+y)=f(x)+f(y)$ for all $x$, $y$, then $f(0)=0$.

- A function satisfying this rule is called **additive**. Every linear map is additive.

> **Proof.** Put $x=y=0$ in the rule: $f(0+0)=f(0)+f(0)$, that is, $f(0)=f(0)+f(0)$. Subtracting $f(0)$ from both sides gives $f(0)=0$. ∎

```lean
example {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) : f 0 = 0 := by
  have h0 : f (0 + 0) = f 0 + f 0 := h 0 0
  rw [add_zero] at h0
  calc
    f 0 = (f 0 + f 0) - f 0 := by ring
    _ = f 0 - f 0           := by rw [← h0]
    _ = 0                   := by ring
```

- `h 0 0` is "put $x=y=0$ in the rule".
- `have h0` is "first we show $f(0)=f(0)+f(0)$".
- The final `calc` is "subtract $f(0)$ from both sides": first write $f(0)$ as $(f(0)+f(0))-f(0)$, then use `h0` to turn $f(0)+f(0)$ back into $f(0)$.
- The whole proof has one idea: **which values to put in**. Once you see that, the rest is calculation.

### Exercise 2 [In class]

`f` is additive, and we already know $f(0)=0$. Prove: for every real $x$, $f(-x)=-f(x)$.

1. Write the proof in words.
2. Write it in Lean. The lemma you need: `add_neg_cancel : a + -a = 0`. Write the last step ("move a term over") with `calc`, as in the example in §1.

```lean
example {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) (hz : f 0 = 0) (x : ℝ) :
    f (-x) = -f x := by
  sorry
```

## 2. Or: split into cases, or pick a side

### Using an "or" hypothesis: split into cases

- In words: "There are two cases." Prove the goal once in each case. The cases must cover every possibility. If one is missing, the proof is incomplete.
- In Lean: `obtain h1 | h2 := h`, followed by two `·`, one per case. Both cases have the same goal. Only what you know is different.
- Example: if $t=1$ or $t=2$, then $t^2-3t+2=0$.

```lean
example {t : ℝ} (h : t = 1 ∨ t = 2) : t ^ 2 - 3 * t + 2 = 0 := by
  obtain h1 | h2 := h
  · rw [h1]; norm_num
  · rw [h2]; norm_num
```

**Absolute value: finishing a proof with "or"**

- The absolute value `|x|` uses the straight bar `|` on your keyboard. It is not the same symbol as `∣` for "divides" (typed `\|` or `\mid`).
- The absolute value is defined piece by piece: $|x|=x$ when $x\ge 0$, and $|x|=-x$ when $x<0$.
- Every real number satisfies $x\ge 0$ or $x<0$. That is an "or".

Example:

> **Claim.** For every real $x$, $|x|\ge 0$.

> **Proof.** Let $x$ be an arbitrary real number. There are two cases. If $x\ge 0$, then $|x|=x\ge 0$. If $x<0$, then $|x|=-x>0$. In both cases $|x|\ge 0$. ∎

```lean
example (x : ℝ) : |x| ≥ 0 := by
  obtain h | h := le_total 0 x
  · rw [abs_of_nonneg h]
    exact h
  · rw [abs_of_nonpos h]
    linarith
```

- `le_total 0 x : 0 ≤ x ∨ x ≤ 0` provides the "or".
- `abs_of_nonneg h : |x| = x` and `abs_of_nonpos h : |x| = -x` replace $|x|$ in each case. What is left is an ordinary inequality.

### Exercise 3

Prove: for every real $x$, $x\le |x|$, and also $-|x|\le x$.

1. Write the proof in words first. Split into two cases. In each case, prove both inequalities.
2. Write it in Lean (one `example` per inequality). Hint:
   - `abs_of_nonneg : 0 ≤ a → |a| = a` and `abs_of_nonpos : a ≤ 0 → |a| = -a` replace $|x|$ in each case.

```lean
example (x : ℝ) : x ≤ |x| := by
  sorry

example (x : ℝ) : -|x| ≤ x := by
  sorry
```

### Proving an "or" goal: pick a side

- In words: "We prove the right-hand side." Once you pick, you prove only that side. A wrong pick cannot be undone, so decide first which side is true.
- In Lean: `left` / `right`, or hand over `Or.inl (…)` / `Or.inr (…)` directly.
- Example: if $2t-4=0$, then $t=1$ or $t=2$. ($t=2$, so we pick the right side.)

```lean
example {t : ℝ} (ht : 2 * t - 4 = 0) : t = 1 ∨ t = 2 :=
  Or.inr (by linarith)
```

### Exercise 4: Factor, then split into cases (the lecture example)

> **Claim.** If a real number $x$ satisfies $x^2-3x+2=0$, then $x=1$ or $x=2$.
>
> **Proof.** Assume $x^2-3x+2=0$. Factoring gives $(x-1)(x-2)=0$. A product is 0, so $x-1=0$ or $x-2=0$. There are two cases. If $x-1=0$, then $x=1$, and the left side of the conclusion holds. If $x-2=0$, then $x=2$, and the right side of the conclusion holds. ∎

```lean
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
```

- `eq_zero_or_eq_zero_of_mul_eq_zero : a * b = 0 → a = 0 ∨ b = 0`: if a product is 0, one of the factors is 0.

1. Follow how the goal changes in the comments. Which line **uses** an "or", and which lines **prove** an "or"? Which sentence of the proof in words does each correspond to? Write down the line and the matching sentence.
2. Change `right` in the second branch to `left` and run it. Which line does Lean report an error on? What is the goal at that point, and which hypothesis do you have? Say in one sentence why it cannot be proved.
3. **[In class]** With the same factoring and case split, prove: if a real number $x$ satisfies $x^2-5x+6=0$, then $x\ge 2$. Write both the proof in words and the Lean. This time the conclusion is not an "or". Does each branch still need `left` / `right`?

## 3. And: a pair of facts

### Using an "and" hypothesis: take out the two parts

- In words: "By assumption, $P$ holds, and $Q$ holds." Taking it apart changes what you **know**. It does not change how many things you have to prove.
- In Lean: `obtain ⟨hp, hq⟩ := h`, or use `h.1` and `h.2` for the first and second part directly.
- Example:

```lean
example (P Q : Prop) (h : P ∧ Q) : Q := h.2
```

### Proving an "and" goal: hand over a pair

- In words: "First we prove $P$. … Next we prove $Q$. …" Both halves must be proved.
- In Lean: hand over a pair `⟨hp, hq⟩`. When each half needs it
- Example:

```lean
example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := ⟨hp, hq⟩
```

- Symbols: "and" uses angle brackets `⟨ ⟩` (typed `\<` and `\>`); "or" uses the straight bar `|`.

### Exercise 5

Prove: if $P$ and ($Q$ or $R$), then ($P$ and $Q$) or ($P$ and $R$).

1. Write the proof in words first. Which one do you take apart first? Which one do you split into cases? In each case, which side do you pick, and which pair do you hand over?
2. Write it in Lean:

```lean
example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  sorry
```

**An absolute-value inequality is an "and"**

- $|a|<b$ is equivalent to $-b<a$ **and** $a<b$. The same goes for $|a|\le b$.
- For example, $|x-2|<\delta$ says $2-\delta<x$ and $x<2+\delta$: the distance from $x$ to $2$ is less than $\delta$.
- Every absolute-value inequality in calculus is short for two inequalities. When one is hard to read, split it into two first.

### Exercise 6

1. Prove: for every real $x$, if $|x-2|<1$, then $1<x$ and $x<3$. Conversely, if $1<x$ and $x<3$, then $|x-2|<1$. Write both the proof in words and the Lean. The lemma you need: `abs_lt : |a| < b ↔ -b < a ∧ a < b`. `rw [abs_lt]` turns the absolute value into an "and".

```lean
example (x : ℝ) (h : |x - 2| < 1) : 1 < x ∧ x < 3 := by
  sorry

example (x : ℝ) (h1 : 1 < x) (h2 : x < 3) : |x - 2| < 1 := by
  sorry
```

2. Prove: for every real $x$, if $0<|x-2|<1$, then $|x+2|<5$.
   - To prove $\lim_{x\to 2}x^2=4$, you have to handle $|x^2-4|=|x-2|\,|x+2|$. Restricting to $|x-2|<1$ first lets you bound $|x+2|$ by $5$. This exercise is that step.
   - $0<|x-2|<1$ is an "and" of two inequalities, so in Lean it is written `0 < |x - 2| ∧ |x - 2| < 1`.
   - Write the proof in words first, then the Lean. The hypothesis and the goal each contain an absolute value. Turn both into an "and".
   - Answer in one sentence: is the hypothesis $0<|x-2|$ used in this exercise? What is it for in the definition of a limit?

```lean
example (x : ℝ) (h : 0 < |x - 2| ∧ |x - 2| < 1) : |x + 2| < 5 := by
  sorry
```

## 4. There exists: hand over a witness

### Using a "there exists" hypothesis: the witness is given to you

- In words: "Let $b$ be such that …"
- In Lean: `obtain ⟨b, hb⟩ := h`.
- You receive a witness, but you **cannot choose which one**. You only know that it exists and the property it satisfies. So the rest of the argument must work for any witness with that property.
- Example:

> **Claim.** If there is a rational $b$ with $a=b^2+1$, then $a>0$.
>
> **Proof.** Let $b$ be a rational number with $a=b^2+1$. Since $b^2\ge 0$, we get $a\ge 1>0$. ∎

```lean
example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  have hb2 : b ^ 2 ≥ 0 := sq_nonneg b
  linarith
```

- `sq_nonneg b : 0 ≤ b ^ 2`: a square is never negative. `have hb2` is "since $b^2\ge 0$".
- Getting $a>0$ from $a=b^2+1$ and $b^2\ge 0$ is a linear step you can see at a glance, so `linarith` does it.

### Proving a "there exists" goal: hand over a witness

- In words: "Take $x=\ldots$." Then check. The witness is usually found while working out the idea. How you found it does not go into the proof.
- In Lean: `use t`, or hand over `⟨t, proof⟩` directly.

Example:

> **Claim.** $(3,5)$ is a linear combination of $(1,1)$ and $(1,2)$.

- Idea: solve $s+t=3$, $s+2t=5$ to get $s=1$, $t=2$.

> **Proof.** Take $s=1$, $t=2$. Then $1\cdot(1,1)+2\cdot(1,2)=(1+2,\,1+4)=(3,5)$. ∎

```lean
example : ∃ s t : ℝ, 3 = s * 1 + t * 1 ∧ 5 = s * 1 + t * 2 := by
  use 1, 2
  exact ⟨by norm_num, by norm_num⟩
```

- An equation of vectors splits into one equation per component, so after `use` an "and" is left.

### Exercise 7 [In class]: Take out the old witnesses, hand over a new one

- A definition can be a "there exists" too.
- "$n$ is a sum of two squares" means: there are integers $a$, $b$ with $n=a^2+b^2$. For example, $13=2^2+3^2$.

```lean
def IsSumOfTwoSquares (n : ℤ) : Prop := ∃ a b : ℤ, n = a ^ 2 + b ^ 2
```

Prove: the product of two sums of two squares is again a sum of two squares. This is $|z|^2|w|^2=|zw|^2$ for complex numbers: expand it with $z=a+bi$, $w=c+di$.

```lean
example {m n : ℤ} (hm : IsSumOfTwoSquares m) (hn : IsSumOfTwoSquares n) :
    IsSumOfTwoSquares (m * n) := by
  sorry
```

1. What do you get by **using** `hm`, and what by using `hn`?
2. What you have to **prove** is a "there exists". Which witnesses do you hand over? Hint: expand $(ac-bd)^2+(ad+bc)^2$.
3. Write the full proof in words first, then the Lean.

## 5. Packaging things: `structure`

- "And" packages two facts into a pair. "There exists" packages a witness together with its proof.
- Mathematical objects are often built the same way: **a few pieces of data, plus the properties they must satisfy.**
  - A closed interval $[a,b]$: two numbers, plus $a\le b$.
  - A vector space: a set, an addition, a zero vector, a scalar multiplication, plus eight axioms.
- Why package them? Take the closed interval, which calculus uses all the time:
  - Writing "two numbers $a$, $b$ with $a\le b$" every time is tiring, and it is easy to forget $a\le b$.
  - Once it is one object, you can say "let $I$ be a closed interval", and the property comes along with it.
- `structure` lets you give such a package a name, so that it becomes a new mathematical object.

```lean
structure ClosedInterval where
  lo : ℝ
  hi : ℝ
  le : lo ≤ hi
```

- `lo` and `hi` are data; `le` is a property. Each one is called a **field**.

**Building one: `⟨ ⟩`, as for "and" and "there exists"**

```lean
example : ClosedInterval := ⟨2, 5, by norm_num⟩
```

- Hand over the two numbers in order, then a proof of `2 ≤ 5`. Without the proof there is no interval: `⟨3, -1, …⟩` needs a proof of `3 ≤ -1`, which can never be given.

**Using one: `.` takes out a field**

- `I.lo` and `I.hi` take out the data. `I.le` takes out the property: it is a proof of `I.lo ≤ I.hi`.

Example:

> **Claim.** For every closed interval $I$, the right endpoint minus the left endpoint is not negative: $\mathrm{hi}-\mathrm{lo}\ge 0$.
>
> **Proof.** Let $I$ be a closed interval. By definition $\mathrm{lo}\le\mathrm{hi}$, so $\mathrm{hi}-\mathrm{lo}\ge 0$. ∎

```lean
example (I : ClosedInterval) : I.hi - I.lo ≥ 0 := by
  linarith [I.le]
```

### Exercise 8 [Bonus]: Cancellation in a vector space

- In linear algebra, a vector space is a set $V$ with an addition, a zero vector, a scalar multiplication, and eight axioms.
- The `structure` below lists only what this exercise needs: addition, the zero vector, negatives, and three axioms. The full definition also has scalar multiplication and the other axioms.

```lean
structure VectorSpaceAxioms (V : Type) where
  add : V → V → V
  zero : V
  neg : V → V
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  zero_add : ∀ v, add zero v = v
  neg_add : ∀ v, add (neg v) v = zero
```

- `S.add u v` is $u+v$, `S.zero` is the zero vector, and `S.neg u` is $-u$.
- All three axioms are "for all" rules. You use them like the additive-function rule in §1: put in specific vectors.
- Take an axiom out with `S.` followed by the field name, for example `S.zero_add`. Inside `calc`, rewrite with `rw [S.zero_add]`.

Prove the **cancellation law**: if $u+v=u+w$, then $v=w$. It is one of the first properties derived from the vector space axioms.

1. Write the proof in words first: start from $v$ and write a chain of equalities, each step using a single axiom or the hypothesis. Next to each equals sign, note which axiom or hypothesis it uses. Hint: $v=0+v=((-u)+u)+v=\ldots$
2. Write it in Lean. Each equals sign in your proof in words becomes one line of `calc`:

```lean
example {V : Type} (S : VectorSpaceAxioms V) (u v w : V)
    (h : S.add u v = S.add u w) : v = w := by
  sorry
```

## Summary

- A proof in words: write the first sentence according to the shape of the statement, say where every variable comes from, write forwards, and use full sentences.
- What each shape asks you to hand over:

| Shape | Proving it means handing over | Lean shorthand |
|---|---|---|
| An intermediate fact is needed | Prove it first and name it | `have` |
| The goal is a lemma's conclusion | Feed the lemma its inputs | `exact` |
| Hypothesis `P ∨ Q` | Handle each of the two cases | `obtain hp \| hq := h` |
| Goal `P ∨ Q` | Say which side: `Or.inl` / `Or.inr` | `left` / `right` |
| Hypothesis `P ∧ Q` | Take out the two parts | `obtain ⟨hp, hq⟩ := h` |
| Goal `P ∧ Q` | A pair: `⟨hp, hq⟩` | `exact ⟨by …, by …⟩` |
| Goal `∃ x, P x` | A witness plus its proof | `use t` |
| Hypothesis `∃ x, P x` | Take out the witness and its property | `obtain ⟨b, hb⟩ := h` |

- Using an "or" hypothesis: handle every case, and make sure the cases cover every possibility.
- Using a "there exists" hypothesis: the witness is given to you. You cannot choose it.
- Absolute value: the definition has two cases; $|a|<b$ is an "and" of two inequalities. The $0<|x-a|<\delta$ in the definition of a limit is also an "and".
- The order of quantifiers changes the meaning: with "let … be arbitrary" first and "take …" second, only the second may depend on the first.
- `structure` packages data and properties into a new object, such as a closed interval or a vector space. Build it with `⟨ ⟩`, take things out with `.`.

**Next week**: parity, divisibility and congruence. All of them are defined with "there exists", so this week's witnesses will be used every day.
