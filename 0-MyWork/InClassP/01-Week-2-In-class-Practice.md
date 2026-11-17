---
module: 1
title: Week 2 In-class Practice
week: 2
audience: students
---

# Week 2 In-class Practice

The two exercises we did in class: Exercise 2 and Exercise 4 of the handout.

Exercise 2 is answered in words. Exercise 4 asks you to write Lean code, except for 4.3.

Hand in one file. Label each answer with its number (`2.1`, `4.3`, and so on).

If you already handed this in with the old numbering (`1.1`, `2.1`, …), your submission is fine.

---

## Exercise 2: Three ways to use an equation

Given `h : a = b`:

- `rw [h]` replaces `a` by `b` in the goal. `rw [← h]` goes the other way: it replaces `b` by `a`.
- `nth_rw n [h]` changes only the `n`-th copy, counted left to right across the whole goal.
- `congrArg f h` applies `f` to both sides of `h` and gives you a new fact. It does not need a goal.

Read these four examples:

```lean
example (x y : ℝ) (h : x = y) : x + 3 = y + 3 := by sorry
example (f : ℝ → ℝ) (x y : ℝ) (h : x = y) : f x = f y := by sorry
example {m n : ℤ} (h : n = m - 1) (hn : n ≥ 0) : m - 1 ≥ 0 := by sorry
example (a b : ℝ) (h : a = b) : a * a = a * b := by sorry
```

**2.1** The first two close with `rw [h]`. Write down the goal of each one after the rewrite.

**2.2** The second one can also be proved by `congrArg f h`. Say what that line does, in one or two sentences.

**2.3** In the third one, `rw [h]` fails but `rw [← h]` works. Say which side of `h` appears in the goal, and why that decides the direction.

**2.4** The fourth goal has three copies of `a`. List their positions, give the number `nth_rw` needs, and write the goal you get.

**2.5** You have `h : a = b` and you want a new fact, `a ^ 2 = b ^ 2`. There is no goal on screen. Can `rw` help? Say why or why not.

---

## Exercise 4: Chaining steps

Two facts chain only when the directions agree. Each `calc` proof below has the same shape:

```lean
example {a b c : ℤ} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  calc a ≤ b := h1
    _ ≤ c := h2
```

**4.1** Replace `sorry` with a `calc` block.

```lean
example {a b c : ℤ} (h1 : a ≤ b) (h2 : b < c) : a < c := by
  sorry
```

**4.2** Replace `sorry` with a `calc` block.

```lean
example {a b c : ℤ} (h1 : a ≥ b) (h2 : b ≥ c) : a ≥ c := by
  sorry
```

**4.3** From `a ≥ b` and `b ≤ c` you learn nothing about `a` and `c`. Say why, in your own words. Then give two sets of numbers for `a`, `b`, `c`: one where `a < c`, one where `a > c`. No Lean code for this one.

**4.4** Replace `sorry` with a `calc` block. (`c ≥ b` is the same fact as `b ≤ c`.)

```lean
example {a b c : ℤ} (h1 : a < b) (h2 : c ≥ b) : a < c := by
  sorry
```

**4.5** Replace `sorry` with a `calc` block. Read `∣` as "divides".

```lean
example {a b c : ℕ} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  sorry
```

**4.6** This chain closes with one line of `linarith`:

```lean
example {x : ℤ} (h : x + 4 = 2) : x = -2 := by
  calc
    x = (x + 4) - 4 := by ring
    _ = 2 - 4       := by rw [h]
    _ = -2          := by norm_num
```

So why learn to build the chain by hand? Two sentences.
