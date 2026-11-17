---
module: 5
title: Week 7 Homework
week: 7
audience: students
---

# Week 7 Homework

The Week 7 exercises that we do not do in class. Exercises 1, 3 and 5 are in the [Week 7 In-class Practice](05-Week-7-In-class-Practice.md). Each exercise names the section of the [Week 7 Student Handout](05-Week-7-Student-Handout.md) it practises.

Each exercise asks for a **proof in words** and a **Lean proof**. Write the proof in words first: decide the shape, then translate it. The proof in words may be in Chinese or English.

Hand in one `.md` file. Label each answer with its number (`2`, `4`). Put your Lean code in a code block that starts with ` ```lean `.

---

## Exercise 2: "Or" distributes over "and"

*Handout section: 1. How to prove and use each shape*

Prove: $P\vee(Q\wedge R)$ if and only if $(P\vee Q)\wedge(P\vee R)$. Write the proof in words first, then the Lean.

  一開始是if and only if，所以要拆成兩個方面討論。向右又分成P成立和Q且R成立。向左也分成兩種，P成立和Q成立，Q成立又要看成P成立和R成立。
- The lecture notes prove the other law ("and" over "or"). For ($\Leftarrow$) here, you need to split two "or"s into cases.

```lean
example (P Q R : Prop) : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) := by
  constructor
  · intro h
    obtain hp | hqr := h
    · constructor
      · left
        exact hp
      · left
        exact hp
    · obtain ⟨hq, hr⟩ := hqr
      constructor
      · right
        exact hq
      · right
        exact hr
  · intro h
    obtain ⟨h1, h2⟩ := h
    obtain hp | hq := h1
    · left
      exact hp
    · obtain hp | hr := h2
      · left
        exact hp
      · right
        exact ⟨hq, hr⟩
```

---

## Exercise 4: One of them always implies the other

*Handout section: 2. Excluded middle*

Prove: for any two statements $P$ and $Q$, at least one of "if $P$ then $Q$" and "if $Q$ then $P$" holds. Write the proof in words first, then the Lean.

只觀察Q的部分。若Q成立，P to Q全對。若Q不成立，可以使用若Q則P：假設Q成立，但是這個與前提Q不成立矛盾，所以P成立，則若Q則P成立。
- Hint: split on whether $Q$ holds. When your hypotheses contradict each other but the goal is not `False`, use `by_contra` first to turn the goal into `False`.
- This result looks strange: take any two unrelated sentences, and one of them "implies" the other. After the proof, explain in one or two sentences why it is not strange. (Think of "vacuous truth" from this week's lecture.)

```lean
example (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  by_cases hq : Q
  · left
    intro hp
    exact hq
  · right
    intro hq'
    by_contra hnp
    exact hq hq'
```
