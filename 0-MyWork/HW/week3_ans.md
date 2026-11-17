# Week 3 Homework

# Exercise 1: For every $M$, an $x$ of its own

Prove: for every real $M$, there exists a **positive** real $x$ with $x^2>M$.

**1.1** Write the proof in words. After taking $x$, check two things: $x>0$, and $x^2>M$. Hint: $M$ may be negative.

    We choose x = (|M|)^(1/2) + 1. In this case, it satify the two required conditions.
    (1) |M| ≥ 0 => x = (|M|)^(1/2) + 1 ≥ 1 > 0. Thus, x is positive.
    (2) x ^ 2 = ((|M|)^(1/2) + 1) ^ 2 = |M| + 2 * (|M|)^(1/2) + 1 > |M|.  
        Since 2 * (|M|)^(1/2) + 1 > 0 and |M| ≥ M for any real number M.


*1.2** Could your $x$ be chosen before "let $M$ be arbitrary"? Answer "yes" or "no", then give your reason in one or two sentences.

    No. Because our choose of x is depends directly on M, M must chosen first.



## Exercise 3: $x$ lies between $-|x|$ and $|x|$

Prove: for every real $x$, $x\le |x|$, and also $-|x|\le x$.

**3.1** Write the proof in words. Split into two cases. In each case, prove both inequalities.

    If x ≥ 0 : x = |x| and -|x| < x .
    If x < 0 : x < |x| and -|x| = x .
    In both case, both inequality are satisfied.

**3.2** Write it in Lean, one `example` per inequality. You need:

- `le_total 0 x : 0 ≤ x ∨ x ≤ 0` for the case split;
- `abs_of_nonneg : 0 ≤ a → |a| = a` and `abs_of_nonpos : a ≤ 0 → |a| = -a` to replace $|x|$ in each case.

```lean
example (x : ℝ) : x ≤ |x| := by
  obtain h | h := le_total 0 x
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    linarith

example (x : ℝ) : -|x| ≤ x := by
  obtain h | h := le_total 0 x
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_nonpos h]
    linarith
```

## Exercise 4: Factor, then split into cases (4.1 and 4.2)


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

**4.1** Follow how the goal changes in the comments. Which line **uses** an "or", and which lines **prove** an "or"? Which sentence of the proof in words does each correspond to? Write down the line and the matching sentence.

    - line **uses** an "or":
        obtain h2 | h2 := eq_zero_or_eq_zero_of_mul_eq_zero h1 -- two cases, both with goal x = 1 ∨ x = 2
    - lines **prove** an "or":
        · left,  If $x-1=0$, then $x=1$, and the left side of the conclusion holds.
        · right, If $x-2=0$, then $x=2$, and the right side of the conclusion holds.


**4.2** Change `right` in the second branch to `left` and run it. Which line does Lean report an error on? What is the goal at that point, and which hypothesis do you have? Say in one sentence why it cannot be proved.

    The "linarith" below the second "left".
    Since the hypothesis and the goal doesn't match.


---

## Exercise 5: Take apart, split, pick, pair


Prove: if $P$ and ($Q$ or $R$), then ($P$ and $Q$) or ($P$ and $R$).

**5.1** Write the proof in words. Which one do you take apart first? Which one do you split into cases? In each case, which side do you pick, and which pair do you hand over?

    We should take apart the "and" hypothesis at first. We split into case base on the "or" hypothesis Q or R.
    In case 1, I'll pick the left side of the goal. (Assume Q holds). We hand over the pair containing P and Q.
    In case 2, I'll pick the right side of the goal. (Assume R holds). We hand over the pair containing P and R.
**5.2** Write it in Lean:

```lean
import Mathlib.Data.Real.Basic

example (P Q R : Prop) (h : P ∧ (Q ∨ R)) : (P ∧ Q) ∨ (P ∧ R) := by
  obtain ⟨hp, hq_or_hr⟩ := h
  obtain hq | hr := hq_or_hr
    left
    exact ⟨hp, hq⟩
    right
    exact ⟨hp, hr⟩
```

---

## Exercise 6: Absolute-value inequalities


The lemma you need for both parts: `abs_lt : |a| < b ↔ -b < a ∧ a < b`. `rw [abs_lt]` turns the absolute value into an "and"; `rw [abs_lt] at h` does the same inside a hypothesis `h`.

**6.1** Prove: for every real $x$, if $|x-2|<1$, then $1<x$ and $x<3$. Conversely, if $1<x$ and $x<3$, then $|x-2|<1$. Write both the proof in words and the Lean.

    In words:
    Assume |x - 2| < 1 hold. This inequality is equialent to the conjunction -1 < x - 2 and x - 2 < 1.
    - First, form -1 < x - 2, adding 2 in both sides gives 1 < x.
    - Second,  form x - 2 < 1, adding 2 in both sides gives x < 3.
    Conversly, assume 1 < x and x < 3 hold.
    - First, form 1 < x , subtracting 2 in both sides gives -1 < x - 2.
    - Second, form x < 3, subtracting 2 in both sides gives x - 2 < 1.
```lean
example (x : ℝ) (h : |x - 2| < 1) : 1 < x ∧ x < 3 := by
  rw [abs_lt] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨by linarith, by linarith⟩

example (x : ℝ) (h1 : 1 < x) (h2 : x < 3) : |x - 2| < 1 := by
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩
```

**6.2** Prove: for every real $x$, if $0<|x-2|<1$, then $|x+2|<5$.

- To prove $\lim_{x\to 2}x^2=4$, you have to handle $|x^2-4|=|x-2|\,|x+2|$. Restricting to $|x-2|<1$ first lets you bound $|x+2|$ by $5$. This exercise is that step.
- $0<|x-2|<1$ is an "and" of two inequalities, so in Lean it is written `0 < |x - 2| ∧ |x - 2| < 1`.
- Write the proof in words first, then the Lean. The hypothesis and the goal each contain an absolute value. Turn both into an "and".

**Forward Direction ($\Rightarrow$):**
Assume $|x - 2| < 1$ holds. By the property of absolute value, this inequality is equivalent to the conjunction $-1 < x - 2$ and $x - 2 < 1$. 
* First, from $-1 < x - 2$, adding $2$ to both sides gives $1 < x$. 
* Next, from $x - 2 < 1$, adding $2$ to both sides gives $x < 3$. 
Thus, we have both $1 < x$ and $x < 3$.

**Backward Direction ($\Leftarrow$):**
Assume both $1 < x$ and $x < 3$ hold. 
* Subtracting $2$ from both sides of $1 < x$ gives $-1 < x - 2$. 
* Subtracting $2$ from both sides of $x < 3$ gives $x - 2 < 1$. 
This gives us the pair of facts $-1 < x - 2$ and $x - 2 < 1$. By the property of absolute value, this conjunction is exactly equivalent to $|x - 2| < 1$. $\blacksquare$

**Proof:**
Assume $0 < |x - 2|$ and $|x - 2| < 1$ holds. From this conjunction, we take out the second part to get the hypothesis $|x - 2| < 1$. By the property of absolute value, $|x - 2| < 1$ is equivalent to $-1 < x - 2$ and $x - 2 < 1$. 
* From $-1 < x - 2$, adding $2$ gives $1 < x$.
* From $x - 2 < 1$, adding $2$ gives $x < 3$.

We want to prove $|x + 2| < 5$, which is equivalent to proving the "and" goal $-5 < x + 2$ and $x + 2 < 5$. 
* First, since $1 < x$, adding $2$ to both sides gives $3 < x + 2$. Because $-5 < 3$, by transitivity we get $-5 < x + 2$.
* Next, since $x < 3$, adding $2$ to both sides gives $x + 2 < 5$.

Since both conditions are met, we conclude that $|x + 2| < 5$. $\blacksquare$


- Answer in one sentence: is the hypothesis $0<|x-2|$ used in this exercise? What is it for in the definition of a limit?

    **No**, the hypothesis $0 < |x - 2|$ is not used in the algebraic evaluation of this exercise; in the formal definition of a limit, it ensures that $x \neq 2$, meaning the function's behavior is analyzed as $x$ approaches $2$ without considering the function's value at $2$ itself.

```lean
example (x : ℝ) (h : 0 < |x - 2| ∧ |x - 2| < 1) : |x + 2| < 5 := by
  obtain ⟨h0, h_abs⟩ := h
  rw [abs_lt] at h_abs
  obtain ⟨h1, h2⟩ := h_abs
  rw [abs_lt]
  exact ⟨by linarith, by linarith⟩
```

---

## Exercise 8 [Bonus]: Cancellation in a vector space

*Handout section: [5. Packaging things: `structure`](02-Week-3-Student-Handout.md#5-packaging-things-structure)*

The `structure` below lists only what this exercise needs from the definition of a vector space: addition, the zero vector, negatives, and three axioms.

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
- All three axioms are "for all" rules. You use them like the additive-function rule in §1 of the handout: put in specific vectors.
- Take an axiom out with `S.` followed by the field name, for example `S.zero_add`. Inside `calc`, rewrite with `rw [S.zero_add]`.

Prove the **cancellation law**: if $u+v=u+w$, then $v=w$.

**8.1** Write the proof in words: start from $v$ and write a chain of equalities, each step using a single axiom or the hypothesis. Next to each equals sign, note which axiom or hypothesis it uses. Hint: $v=0+v=((-u)+u)+v=\ldots$

**Proof:**
Let $S$ be a vector space with the given axioms, and let $u, v, w$ be vectors such that $u + v = u + w$. We want to show that $v = w$. We can establish this by the following chain of equalities:

$$
\begin{aligned}
v &= 0 + v && \text{(by zero\_add)} \\
&= ((-u) + u) + v && \text{(by neg\_add)} \\
&= (-u) + (u + v) && \text{(by add\_assoc)} \\
&= (-u) + (u + w) && \text{(by hypothesis } h: u + v = u + w) \\
&= ((-u) + u) + w && \text{(by add\_assoc)} \\
&= 0 + w && \text{(by neg\_add)} \\
&= w && \text{(by zero\_add)}
\end{aligned}
$$


Thus, we conclude that $v = w$. $\blacksquare$

**8.2** Write it in Lean. Each equals sign in your proof in words becomes one line of `calc`. Put the `structure` above your `example` so that the file compiles.

```lean
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
```
