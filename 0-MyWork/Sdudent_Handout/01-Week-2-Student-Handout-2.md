---
module: 1
title: Week 2 Student Handout
week: 2
audience: students
---

# Week 2 Student Handout: Making a Calculation Count as a Proof

Last week we read what Lean tells us. This week we write: a chain of steps, each one justified. The calculations are not hard. Saying why each line follows from the one above is the new part.

## Learning goals

- Choose the number system a statement lives in, and say why it matters.
- Use an equation in three ways: rewrite forwards, rewrite backwards (with `nth_rw` when you need one spot only), and apply a function to both sides.
- Read a `calc` chain and name the goal of each line.
- Chain steps that are not equalities, and check the direction.
- Say where `linarith` and `nlinarith` stop working.
- Read the three error messages you will meet most often this week.
- Use `sorry` to hold one step open and check the shape of the chain.

## Getting started

Create a new `.lean` file and type `import Mathlib` on the first line. Put the examples below after it, a small block at a time. Before you ask Lean, predict what it will show.

## 1. Choosing the number system

Every number in Lean has a type, and the type decides what is true about it. Last week we saw that subtraction on `ℕ` never gives a negative number. Division is the same:

```lean
#eval 7 / 2          -- on ℕ
#eval (7 : ℚ) / 2    -- on ℚ
```

The first prints `3`: division on `ℕ` rounds down. The second prints `7 / 2` — Lean shows a rational as a fraction, not as a decimal. Neither is a bug. They are two operations that share one symbol.

This is what the type annotation `(7 : ℚ)` is for. On its own, `7` is a natural number; `(7 : ℚ)` is the rational number 7.

The number system also decides whether a rearrangement holds:

```lean
example (a b : ℤ) : (a - b) + b = a := by ring
example (a b : ℕ) : (a - b) + b = a := by ring   -- fails
```

The second line is **false**: take `a = 2` and `b = 5`. On `ℕ`, `a - b` is `0`, and adding `b` back gives `5`, not `a`.
`ring` works over `ℤ`, `ℚ` and `ℝ`, but not over `ℕ`: it handles addition, subtraction and multiplication that behave well together, and subtraction on `ℕ` stops at zero instead.

**Rule of thumb.** If a statement has subtraction, negative numbers, or division, put it over `ℤ`, `ℚ`, or `ℝ`.

### Exercise 1: Predict the type, then the value

Predict what each line shows, then run it.

```lean
#eval 10 / 4
#eval (10 : ℚ) / 4
#check (10 : ℝ) / 4
#eval (2 : ℤ) - 5
```

1. Why do the first two lines disagree?
2. Why is the third line a `#check` and not an `#eval`?

## 2. Three ways to use an equation

Given `h : a = b`, there are three different things you can do with it.

### Rewrite forwards

`rw [h]` replaces `a` by `b` **inside the goal**:

```lean
example (a b : ℝ) (h : a = b) : a + 1 = b + 1 := by
  rw [h]
```

After the rewrite the goal is `b + 1 = b + 1`. Both sides are the same, so Lean closes it — that is why nothing follows `rw`.

### Rewrite backwards

If the goal contains the **right** side of the equation, use `rw [← h]` to replace the right side by the left side:

```lean
example {x y : ℤ} (h : y = x + 1) (hy : y ≤ 5) : x + 1 ≤ 5 := by
  rw [← h]
  exact hy
```

The goal `x + 1 ≤ 5` has no `y` in it, so `rw [h]` finds nothing to replace. The backward form looks for `x + 1` and replaces it by `y`. The goal becomes `y ≤ 5`, which is exactly `hy`.

Type `←` as `\l` followed by Tab. To pick the direction, ask: **which expression do I want to remove from the goal?** Read the hypothesis from the side that expression sits on.

### One spot only: `nth_rw`

`rw` replaces **every** match at once. Sometimes that is not what you want:

```lean
example (a b : ℤ) (h : a = b) : a + a = b + b := by
  nth_rw 1 [h]
  rw [h]
```

The goal has two copies of `a`. Put the cursor at the **end** of the `nth_rw` line: the Infoview shows `b + a = b + b`. Only the first copy changed; the second is untouched. The `rw [h]` on the next line changes the one that is left, and the goal closes.

(A one-step version would jump straight to `No goals`, and you would not see which copy moved. That is why the demo has two steps.)

The number is the position of the match, counted left to right, **across both sides of the equation**. In `a * a = a * b` there are three copies of `a`: two on the left, one on the right. Count them in the Infoview before you choose. Counting wrong usually gives no error — it changes the wrong spot.

### Apply a function to both sides

On paper you more often do something else: the same thing to both sides — square both sides, take the log of both sides, multiply both sides by a matrix. That is `congrArg`:

```lean
example (a b : ℝ) (h : a = b) : a ^ 2 = b ^ 2 :=
  congrArg (fun t : ℝ => t ^ 2) h
```

The difference is the direction. `rw` starts from a goal and edits it. `congrArg` starts from a fact you already have and makes a new fact.

**Why this matters in linear algebra.** Multiplying both sides of `A = B` by a matrix `M` gives either `M * A = M * B` or `A * M = B * M`. These are different statements, because matrix multiplication does not commute. "Multiply both sides" means: pick one side, and use it on both.

### Exercise 2: Three ways to use an equation

```lean
example (x y : ℝ) (h : x = y) : x + 3 = y + 3 := by sorry
example (f : ℝ → ℝ) (x y : ℝ) (h : x = y) : f x = f y := by sorry
example {m n : ℤ} (h : n = m - 1) (hn : n ≥ 0) : m - 1 ≥ 0 := by sorry
example (a b : ℝ) (h : a = b) : a * a = a * b := by sorry
```

1. The first two close with `rw [h]`. Write down the goal of each one after the rewrite.
2. The second one can also be proved by `congrArg f h`. Say what that line does, in one or two sentences.
3. In the third one, `rw [h]` fails but `rw [← h]` works. Say which side of `h` appears in the goal, and why that decides the direction.
4. The fourth goal has three copies of `a`. List their positions, give the number `nth_rw` needs, and write the goal you get.
5. You have `h : a = b` and you want a new fact, `a ^ 2 = b ^ 2`. There is no goal on screen. Can `rw` help? Say why or why not.

## 3. Reading a `calc` chain

The notes introduce `calc` as a chain from one side of the goal to the other. Three details are worth stating:

```lean
example {total : ℤ} (h : total = 12) : total - 4 = 8 := by
  calc
    total - 4 = 12 - 4 := by rw [h]
    _         = 8      := by norm_num
```

- **`_` is the right-hand side of the line above.** On line 2, `_` is `12 - 4`.
- **Each line is its own small goal**, justified after `:=`. Line 1 proves `total - 4 = 12 - 4`; line 2 proves `12 - 4 = 8`. Neither knows about the other.
- **The chain starts at the left side of the goal and ends at the right side.** If it starts elsewhere, Lean rejects it even when every line is true.

Put your cursor at the end of each line and watch the Infoview: you face one small goal at a time.

### Exercise 3: Name each line's goal

```lean
example {x : ℤ} (h : x + 4 = 2) : x = -2 := by
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4       := by rw [h]
    _ = -2          := by norm_num
```

1. Write the goal of each of the three lines.
2. What goes wrong if line 1 uses `rw [h]` instead?
3. Why does the chain start at `x` and not at `x + 4`?

## 4. Chains that are not equalities

Chains of `≤` and `<` work the same way, with one more thing to check: the direction.

```lean
example {x : ℤ} (h : x ≤ 2) : x + 3 ≤ 5 := by
  calc
    x + 3 ≤ 2 + 3 := add_le_add_left h 3
    _     = 5     := by norm_num
```

A `≤` step followed by an `=` step still gives `≤`. The rules are the ones from the lecture: adding the same quantity to both sides keeps the direction, multiplying by a negative number reverses it.

**Directions cannot be mixed.** From `A ≥ B` and `B ≤ C`, nothing follows about `A` and `C`: both arrows point at `B`. With `(A, B, C) = (5, 1, 100)` we get `A < C`; with `(100, 1, 5)` we get `A > C`. Both satisfy the assumptions.

**`calc` is not only for numbers.** Any relation where "`a` to `b`" and "`b` to `c`" give "`a` to `c`" can be chained — divisibility, for example:

```lean
example (a b c : ℕ) (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  calc
    a ∣ b := h1
    _ ∣ c := h2
```

You will meet this again with divisibility in Module 3 and with `⊆` in Module 8.

### Review: `linarith` and `nlinarith`

`linarith` looks for a **linear combination** of the hypotheses you already have:

```lean
example {a b : ℤ} (h : a - 2 * b = 1) : a = 2 * b + 1 := by linarith
```

Adding, subtracting, multiplying by constants, even dividing by a coefficient to isolate the unknown (from `3 * w + 1 = 4` to `w = 1`) — all inside its range. The limit is **unknowns multiplied together**: a term like `x * y` or `m ^ 2` is just an opaque lump to it.

`nlinarith` adds a limited amount of nonlinear reasoning, and often needs you to hand it the key fact:

```lean
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by nlinarith
```

`linarith` cannot do this one: it does not see how `x * y` relates to `x` and `y`, and reports `linarith failed to find a contradiction`. `nlinarith` tries products of the hypotheses, so it finds `0 ≤ x * y`.

Sometimes it also needs a fact from you, written in brackets: `nlinarith [sq_nonneg m]` hands it the fact that `m ^ 2` is not negative.

**Work out the chain first, then decide whether to automate.** Two reasons: when automation fails it does not tell you which step is wrong, and only the chain in your head does; and when it needs a fact handed to it, you have to know which fact — that part is the mathematics.

### Exercise 4: Chaining steps

Each `calc` proof below has the same shape:

```lean
example {a b c : ℤ} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := h1
    _ ≤ c := h2
```

1. Replace `sorry` with a `calc` block.

   ```lean
   example {a b c : ℤ} (h1 : a ≤ b) (h2 : b < c) : a < c := by
     sorry
   ```

2. Replace `sorry` with a `calc` block.

   ```lean
   example {a b c : ℤ} (h1 : a ≥ b) (h2 : b ≥ c) : a ≥ c := by
     sorry
   ```

3. From `a ≥ b` and `b ≤ c` you learn nothing about `a` and `c`. Say why, in your own words. Then give two sets of numbers for `a`, `b`, `c`: one where `a < c`, one where `a > c`. No Lean code for this one.

4. Replace `sorry` with a `calc` block. (`c ≥ b` is the same fact as `b ≤ c`.)

   ```lean
   example {a b c : ℤ} (h1 : a < b) (h2 : c ≥ b) : a < c := by
     sorry
   ```

5. Replace `sorry` with a `calc` block. Read `∣` as "divides".

   ```lean
   example {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
     sorry
   ```

6. The `x = -2` chain in section 3 closes with one line of `linarith`. So why learn to build the chain by hand? Two sentences.

## 5. When Lean does not accept a step

You will meet failures this week. These three cover most of them:

- **`unsolved goals`** — the justification on that line did not finish. The message shows what is left. Common cause: `norm_num` on a step that still has a variable in it.
- **`type mismatch`** — the proof you gave states something else, usually the wrong hypothesis. Compare the two statements in the message word by word.
- **`ring` cannot close the goal** — either the two sides are not equal, or you are on `ℕ` and the step uses subtraction.

When a step resists, do not delete the chain. Hold that step with `sorry` and check the rest of the structure:

```lean
example {r s : ℤ} (h1 : r + 2 * s = -1) (h2 : s = 3) : r = -7 := by
  calc
    r = (r + 2 * s) - 2 * s := by sorry
    _ = -1 - 2 * s          := by rw [h1]
    _ = -1 - 2 * 3          := by rw [h2]
    _ = -7                  := by norm_num
```

Lean accepts this with a warning. Replace every `sorry` before you hand anything in — a warning is not a pass.

### Exercise 5: Diagnose, don't guess

All three fail. Predict the message and the reason, then run them.

```lean
example (a b : ℕ) : (a - b) + b = a := by ring
example {x : ℤ} (h : x = 3) : x + 1 = 4 := by norm_num
example {x y : ℤ} (hx : x = 2) (hy : y = 5) : y = 5 := by exact hx
```

1. Which one fails because the statement is false, not because the tactic is wrong?
2. Fix the second one without changing its statement.

## 6. Putting it together: Cauchy–Schwarz in two lines

For any real numbers $a,b,c,d$:

$$(ac+bd)^2 \le (a^2+b^2)(c^2+d^2).$$

This is the Cauchy–Schwarz inequality in two dimensions. The proof is two lines:

```lean
example (a b c d : ℝ) : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  calc (a * c + b * d) ^ 2 ≤ (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
    _ = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by ring
```

Step one is the trick from section 4: adding a quantity that is not negative can only make it bigger, and a square is never negative. Step two: `ring` checks the equation.

But the two lines are not the hard part. `ring` can check

$$(ac+bd)^2 + (ad-bc)^2 = (a^2+b^2)(c^2+d^2),$$

and it will never tell you to add $(ad-bc)^2$. Seeing that you should is the whole mathematical content. The equation is called Lagrange's identity; you will meet its general form in linear algebra, because the inner product of $(a,b)$ and $(c,d)$ is exactly $ac+bd$.

One line of `nlinarith [sq_nonneg (a * d - b * c)]` also closes this goal — but it still needs you to think of that square first. Automation saves writing, not thinking.

### Exercise 6: Build your own chain

1. Prove that `2 * a * b ≤ a ^ 2 + b ^ 2` for all real `a` and `b`. Use the same shape as above. (Hint: which square do you add this time?)
2. In one sentence: which part of question 1 did `ring` check, and which part did you decide?
3. Divide the result of question 1 by 2 to get `a * b ≤ (a ^ 2 + b ^ 2) / 2`. Try to get from question 1 to this in Lean.

## Summary

- A number's type decides what is true about it. Subtraction and division on `ℕ` cut off, so state such things over `ℤ`, `ℚ`, or `ℝ`.
- `rw [h]` rewrites the goal forwards, `rw [← h]` backwards, `nth_rw n [h]` at position `n` only; `congrArg f h` makes a new fact from one you have.
- In a `calc` chain, `_` is the previous right-hand side, and every line is its own small goal.
- Anything where "`a` to `b`" and "`b` to `c`" give "`a` to `c`" can be chained: `≤`, `<`, `∣`, `⊆` — as long as the directions agree.
- `unsolved goals`, `type mismatch` and a failing `ring` cover most problems; `sorry` lets you check the shape of the chain first.
- `linarith` handles linear reasoning; unknowns multiplied together are outside it. `nlinarith` goes further but often needs a fact from you.
- `ring` checks a rearrangement; choosing it is your job. Cauchy–Schwarz is the extreme case.

Next week: proofs with structure — statements joined by "and", "or", and "there exists", and what a proof of each one must supply.
