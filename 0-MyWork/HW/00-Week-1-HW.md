---
module: 0
title: Week 1 Homework
week: 1
audience: students
---

# Week 1 Homework

These are the four exercises from the [Week 1 Student Handout](00-Week-1-Student-Handout.md), collected here in one place.

Nothing here asks you to invent a proof or to memorize tactics. Every question can be answered by reading the code carefully, predicting what Lean will say, and then checking your prediction against what Lean actually says. **Predict before you run** — a wrong prediction tells you exactly which idea to go back and re-read.

Hand in your answers in your own file. Any readable format is fine. Please label each answer with its number (`1.1`, `2.2`, and so on) so that nothing gets lost.

---

## Exercise 1: Read the Infoview

*Handout section: [1. Entering symbols and reading the Infoview](00-Week-1-Student-Handout.md#1-entering-symbols-and-reading-the-infoview)*

Read the code first. Then place your cursor immediately before the final line.

```lean
example (a b : ℕ) (ha : a = 2) (hb : b = 5) : b = 5 := by
  exact hb
```

**1.1** Which variables and assumptions appear in the context?

**1.2** What is the goal? Which assumption matches it exactly?

**1.3** If we replace the last line with `exact ha`, why does Lean reject it?

---

## Exercise 2: Read the results of `#check`

*Handout section: [2. A basic view of types and `Prop`](00-Week-1-Student-Handout.md#2-a-basic-view-of-types-and-prop)*

Before running these commands, predict what Lean will display to the right of the colon. Record your prediction and the actual result for each line.

```lean
#check 10
#check (10 : ℚ)
#check fun n : ℕ => n + 1
#check (10 : ℤ) < 20
```

**2.1** Which line describes a function? What kind of input does it accept, and what kind of output does it produce?

**2.2** Which line has type `Prop`? Why?

---

## Exercise 3: Predict and explain

*Handout section: [3. `#eval`, natural-number subtraction, and real numbers](00-Week-1-Student-Handout.md#3-eval-natural-number-subtraction-and-real-numbers)*

Do not modify the code. Predict each result, then run the commands. Record your prediction and the actual result for each line.

```lean
#eval 3 - 10
#eval 10 - 3
#eval (3 : ℤ) - 10
#check √2
```

**3.1** Why is the first result not `-7`, while the third result is?

**3.2** `#check` can tell us the type of `√2`. Does that mean it can also be used with `#eval`?

---

## Exercise 4: Put the ideas together

*Handout section: [4. Functions, substitution, and scope](00-Week-1-Student-Handout.md#4-functions-substitution-and-scope)*

Read the following code. You do not need to modify it.

```lean
def shift (k : ℕ) (n : ℕ) : ℕ :=
  n + k

#check shift
#check shift 4
#eval shift 4 10

example (x : ℕ) (h : x = 4) : x = 4 := by
  exact h
```

**4.1** How many inputs does `shift` require? What are the types of its inputs and output?

**4.2** Why is `shift 4` still a function? What input is it still waiting for?

**4.3** What does `#eval shift 4 10` produce?

**4.4** What are the context and goal of the final example? Why does `exact h` complete it?
