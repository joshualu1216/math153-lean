---
module: 0
title: Week 1 Student Handout
week: 1
audience: students
---

# Week 1 Student Handout: Starting a Conversation with Lean

This week, our goal is to learn how to read the information Lean gives us. Through a few small experiments, we will see how Lean handles numbers, propositions, functions, and variables. You are not expected to memorize tactics or complete unfinished proofs this week.

## Learning goals

- Enter several common mathematical symbols in Lean using VS Code.
- Find the available information and the current target in the Infoview.
- Use `#check` to see how Lean classifies something and `#eval` to run a computation.
- Explain what `Prop` represents.
- Explain the difference between subtraction on natural numbers and subtraction on integers.
- Explain why Lean can reason about real numbers even though general real-number computations cannot be displayed with `#eval`.
- Read the inputs, output, and application of a simple function.
- Recognize where a variable is available and where it is out of scope.

## Getting started

Create a new `.lean` file and enter the following line at the top:

```lean
import Mathlib
```

You can place each example below after this line. Add only a small block at a time. Before asking Lean, make a prediction about what it will display.

## 1. Entering symbols and reading the Infoview

### Common symbols

In the Lean editor, type a backslash command. When the completion menu appears, press Space or Enter to insert the symbol.

| Input | Symbol | Meaning |
|---|---:|---|
| `\N` | `ℕ` | natural numbers |
| `\Z` | `ℤ` | integers |
| `\Q` | `ℚ` | rational numbers |
| `\R` | `ℝ` | real numbers |
| `\to` | `→` | function or implication |
| `\forall` | `∀` | for every |
| `\exists` | `∃` | there exists |
| `\le`, `\ge` | `≤`, `≥` | less than or equal to, greater than or equal to |
| `\ne` | `≠` | not equal to |
| `\and`, `\or` | `∧`, `∨` | and, or |

You do not need to memorize this table. If you forget a symbol, type `\` followed by a likely English name and inspect the completion menu.

### What are the context and the goal?

While a proof is in progress, the Infoview separates the situation into two parts:

- The **context** is the information currently available to you: the variables and assumptions supplied by the problem, together with any facts proved earlier. Think of it as the “Given” part of a written proof.
- The **goal** is the statement Lean is currently waiting for you to prove. Think of it as the “Prove” part of the problem.

The symbol `⊢` separates them. The context appears above `⊢`, and the goal appears below it.

Consider this proof:

```lean
example (n : ℕ) (h : n = 3) : n = 3 := by
  exact h
```

Place your cursor immediately before `exact h`. The Infoview will look similar to this:

```text
n : ℕ
h : n = 3
⊢ n = 3
```

We can read it as follows:

- The context contains a natural number called `n`.
- The context also contains an assumption called `h`, whose content is `n = 3`.
- The goal asks us to prove `n = 3`.
- Because the content of `h` is exactly the goal, `exact h` completes the proof.

A step may sometimes create several things that remain to be proved. In that case, the Infoview displays multiple goals. Lean accepts the full proof only after every goal has been completed.

### Exercise 1: Read the Infoview

Read the code first. Then place your cursor immediately before the final line.

```lean
example (a b : ℕ) (ha : a = 2) (hb : b = 5) : b = 5 := by
  exact hb
```

Answer the following questions:

1. Which variables and assumptions appear in the context?
2. What is the goal? Which assumption matches it exactly?
3. If we replace the last line with `exact ha`, why does Lean reject it?

## 2. A basic view of types and `Prop`

Lean needs to know what kind of thing each item is before it can determine which operations are allowed. This classification is called its **type**.

Enter the following commands:

```lean
#check 3
#check (3 : ℤ)
#check 3 + 4
#check 3 + 4 = 7
```

Lean will display something similar to:

```text
3 : ℕ
3 : ℤ
3 + 4 : ℕ
3 + 4 = 7 : Prop
```

You can read the colon as “is of type”:

- `3 : ℕ` says that Lean is treating `3` as a natural number here.
- `(3 : ℤ)` explicitly asks Lean to treat `3` as an integer.
- `3 + 4 = 7 : Prop` says that `3 + 4 = 7` is a proposition.

### What is `Prop`?

`Prop` is Lean's special type for propositions. Equations, inequalities, and statements involving “and,” “or,” or “there exists” can all be propositions.

```lean
#check 2 + 2 = 4
#check (10 : ℤ) < 20
#check True
#check False
```

When we write a theorem, we announce that we are going to provide a proof of a proposition:

```lean
theorem two_plus_two : 2 + 2 = 4 := by
  rfl
```

For now, read this as follows:

- `2 + 2 = 4` is the proposition to be proved.
- `by` begins the proof.
- `rfl` completes the proof in this particular example.

You do not need a deeper account of type theory this week, and you should not treat `rfl` as a general-purpose arithmetic method. Later modules will introduce the proof methods we will actually use.

### Exercise 2: Read the results of `#check`

Before running these commands, predict what Lean will display to the right of the colon.

```lean
#check 10
#check (10 : ℚ)
#check fun n : ℕ => n + 1
#check (10 : ℤ) < 20
```

Answer the following questions:

1. Which line describes a function? What kind of input does it accept, and what kind of output does it produce?
2. Which line has type `Prop`? Why?

## 3. `#eval`, natural-number subtraction, and real numbers

`#check` shows a type. In contrast, `#eval` actually runs something that can be computed.

```lean
#check 8 + 5
#eval 8 + 5
```

The first command tells us how Lean classifies `8 + 5`. The second command actually calculates the answer.

### Natural-number subtraction does not produce negative numbers

Before running the next two lines, predict whether they will produce the same answer.

```lean
#eval 2 - 5
#eval (2 : ℤ) - 5
```

The actual results are:

```text
0
-3
```

Without an additional annotation, Lean interprets the first line as subtraction on natural numbers `ℕ`. Natural numbers do not include negative numbers. Lean therefore uses truncated subtraction on natural numbers: a result that would be negative stops at zero.

The second line explicitly uses integers `ℤ`, so its result can be `-3`. The same symbol `-` can therefore refer to different versions of subtraction depending on the type.

### Real numbers can be discussed but not directly evaluated

$\pi$ and $\sqrt{2}$ are two familiar real numbers. Mathlib represents them as exact real numbers, not as decimal approximations truncated in advance:

```lean
#check Real.pi
#check √2
```

Lean tells us:

```text
Real.pi : ℝ
√2 : ℝ
```

Now remove the comment marker from each of the following lines, one at a time, and observe Lean's response.

```lean
-- #eval Real.pi
-- #eval √2
```

This does not mean that Lean does not understand $\pi$ or $\sqrt{2}$. Rather, Mathlib's real numbers are not ordinary executable data whose arbitrary exact values can be displayed directly by `#eval`. The fact that neither $\pi$ nor $\sqrt{2}$ has a finite decimal expansion helps illustrate the difference between an exact real number and a directly displayed string of digits. The technical reason, however, is that Mathlib's construction of the real numbers does not provide the executable representation and display mechanism required by `#eval`.

Lean can still state and check mathematical facts about them:

```lean
#check Real.pi_pos
#check Real.sqrt_nonneg 2
```

The first line shows that Mathlib contains `Real.pi_pos : 0 < Real.pi`, a proof that $\pi>0$. The second shows `Real.sqrt_nonneg 2 : 0 ≤ √2`, a proof that $\sqrt{2}\ge0$.

We must therefore distinguish two questions:

- Can Lean run this with `#eval`?
- Can Lean state and prove something about it?

These are not the same question.

### Exercise 3: Predict and explain

Do not modify the code. Predict each result, then run the commands.

```lean
#eval 3 - 10
#eval 10 - 3
#eval (3 : ℤ) - 10
#check √2
```

Answer the following questions:

1. Why is the first result not `-7`, while the third result is?
2. `#check` can tell us the type of `√2`. Does that mean it can also be used with `#eval`?

## 4. Functions, substitution, and scope

### Defining and applying a function

A function accepts an input and produces an output. The following function accepts a natural number `n` and returns `2 * n`:

```lean
def double (n : ℕ) : ℕ :=
  2 * n

#check double
#eval double 7
#eval double (3 + 4)
```

`double 7` means that `7` is supplied as the input to `double`. Function application in Lean is normally written as `f x`, rather than the `f(x)` notation often used in school mathematics.

A function does not have to be named first:

```lean
#check fun n : ℕ => n + 1
#eval (fun n : ℕ => n + 1) 5
```

Read `fun n : ℕ => n + 1` as: “Accept a natural number `n` and return `n + 1`.”

### A function can wait for more than one input

```lean
def addK (k : ℕ) (n : ℕ) : ℕ :=
  n + k

#check addK
#check addK 3
#eval addK 3 10
```

- `addK` is still waiting for the two inputs `k` and `n`.
- `addK 3` has received its first input but is still waiting for one natural number.
- `addK 3 10` has received both inputs, so Lean can calculate the result `13`.

### The scope of a variable

A variable is available only in the region where it has been declared:

```lean
section ScopeDemo

variable (n : ℕ)

#check n

example : n = n := by
  rfl

end ScopeDemo

-- Removing the comment marker produces an “unknown identifier” error:
-- #check n
```

The variable `n` is available between `section ScopeDemo` and `end ScopeDemo`. Outside that scope, Lean no longer knows what `n` refers to.

A function parameter also has its own scope:

```lean
def nextNat (n : ℕ) : ℕ :=
  n + 1
```

Here, `n` is available from `(n : ℕ)` to the end of the definition. It does not automatically appear in another function or theorem.

### Exercise 4: Put the ideas together

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

Answer the following questions:

1. How many inputs does `shift` require? What are the types of its inputs and output?
2. Why is `shift 4` still a function? What input is it still waiting for?
3. What does `#eval shift 4 10` produce?
4. What are the context and goal of the final example? Why does `exact h` complete it?

## Summary

- The context contains the variables, assumptions, and previously proved facts currently available to us. The goal is the statement we must prove now.
- `#check` displays a type; `#eval` runs something that can be computed.
- A type can initially be understood as a classification used by Lean. `Prop` is the special type of propositions.
- Natural numbers do not include negative numbers, so subtraction on natural numbers differs from subtraction on integers.
- The fact that a real-number calculation cannot be displayed with `#eval` does not prevent Lean from stating or proving propositions about real numbers.
- A function accepts inputs and produces an output. Function application is written as `f x`.
- A variable can be used only within the scope in which it is declared.

Before beginning proofs by calculation next week, we will discuss conversions between number systems and the difference between applying a function and rewriting with an equation.
