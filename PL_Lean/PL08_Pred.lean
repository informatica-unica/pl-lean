set_option autoImplicit false

/-
# Predicate logic and dependent types

In the previous lab we proved statements built from *propositions* `P Q R : Prop`
with the connectives `→ ∧ ∨ ¬ ↔`, and we discovered the Curry–Howard isomorphism:
propositions are types, and proofs are programs.

That language is too poor to talk about *data*.  How do we say "every grade is at most
30", "some student passed", or "`n + 0 = n` for every natural number `n`"?  We need three
new ingredients:

* **predicates**: properties of objects, such as "`n` is even";
* **quantifiers**: "for all" (`∀`) and "there exists" (`∃`);
* **equality**: `a = b`.

The Curry–Howard isomorphism extends to all of them, and the extension is the notion of
**dependent type**:

  a proof of  ∀ x : A, P x   is a *function* that maps every a : A to a proof of P a;
                             the *type* of the result, `P a`, depends on the argument `a`.
  a proof of  ∃ x : A, P x   is a *pair* ⟨a, h⟩: an object `a : A` together with a
                             proof `h : P a` that `a` has the property.

Here is the dictionary, extended with the new rows:

    Logic                   Types
    --------------------    -------------------------------------
    P → Q     (implies)     A → B           (functions)
    P ∧ Q     (and)         A × B           (products)
    P ∨ Q     (or)          A ⊕ B           (sums)
    True                    Unit
    False                   Empty
    P → False (not)         A → Empty
    P ↔ Q     (iff)         (A → B) × (B → A)
    ∀ x : A, P x            (x : A) → B x   (dependent function)
    ∃ x : A, P x            (x : A) × B x   (dependent pair)
    a = b                   identity type

We will have a few surprises, finding that:
* `A → B` is the special case of `(x : A) → B x` in which `B` does not mention `x`
  (in Lean, the two types are literally the same);
* `A × B` is the special case of `(x : A) × B x` in which `B` does not mention `x`.
  (in Lean, the two types are not the same, but they are isomorphic).

So, the connectives `→` and `×` are the *non-dependent* versions of the quantifiers.

By the end of the lecture, you should be able to:

* write predicates as functions into `Prop`, and read quantified statements;
* prove statements with `∀`, `∃` and `=` in tactic mode and in term mode, and translate
  between the two modes;
* explain why a proof of `∀` is a function and a proof of `∃` is a pair;
* explain which quantifier laws are provable constructively and which are not, and why;
* disprove false conjectures by exhibiting counterexamples.

You find additional extended exercises in the file `PL08_PredEx.lean`.
-/

section Predicates

/-
## Predicates

A **predicate** on a type `A` is a function `A → Prop`: it takes a value of type `A`
and returns a proposition.  For instance:
-/

def IsZero (n : Nat) : Prop :=
  n = 0

def Even (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k

def Odd (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

example : IsZero 0 := by rfl

example : Even 42 := by exists 21 --- witness for ∃

example : ¬ IsZero 3 := by
  intro h
  cases h


/-
__Checkpoint 1__  Predict the types of the following expressions, then check them.
Which of them are propositions? Which of them are predicates? Which of them are not well-typed?
-/

-- #check IsZero
-- #check IsZero (2+2)
-- #check if True then True else False
-- #check if (IsZero 0) = true then True else False
-- #check (fun (n : Nat) => n + 1 = 3)
-- #check (fun (n : Nat) => if n = 0 then true else false)
-- #check Even
-- #check (fun (d n : Nat) => ∃ q, n = d * q)
-- #check (fun (n : Nat) => ∀ q, (∃ d, n = d * q) → q = 1 ∨ q = n)


/-
Applying a predicate to a value gives a proposition, which may be true or false:
`IsZero 0` is provable, `IsZero 3` is a perfectly good proposition that we cannot prove
(indeed, we can prove its negation, i.e. refute it).

A predicate can also be understood as a **family of propositions indexed by values**.
Since, by the Curry–Howard isomorphism, a proposition is a type (the type of its proofs),
this is also a **family of types**.

For example, `Even : Nat → Prop` associates a proposition with every natural number:

    Even 0,  Even 1,  Even 2,  Even 3,  ...

and different numbers give different propositions. Unfolding the definition of `Even`:

    Even 8   unfolds to   ∃ k : Nat, 8 = 2 * k
    Even 3   unfolds to   ∃ k : Nat, 3 = 2 * k

The first one is provable: a proof is the pair `⟨4, rfl⟩`, where `rfl` proves `8 = 2 * 4`
by computation (in tactic mode, the tactic `exists 4` builds this pair).
The second one has no proof, because no natural number `k` satisfies `3 = 2 * k`.

Thus, applying `Even` to a number produces a different type of proofs: the type `Even n`
depends on the value of `n`. Each `Even n` is a **dependent type**, and `Even` is the
**family** of all of them, indexed by the natural numbers.

More generally, given a predicate

    P : A → Prop

every value `x : A` determines a type `P x`, whose elements are the proofs that `x`
satisfies `P`. Lean has a type of functions that, for every `x : A`, return an element of
the corresponding type `P x`:

    (x : A) → P x

This is a **dependent function type**, because the result type `P x` depends on the
argument `x`.  When `P x` is a proposition.
-/

end Predicates



section Universal

/-
## The universal quantifier

The statement `∀ x : A, P x` is Lean's notation for the dependent type `(x : A) → P x`.

Accordingly, a proof of `∀ x : A, P x` is a **function** that takes any `a : A`
and returns a proof of `P a`.

When `P` does not depend on `x` this is the arrow `A → P`: therefore, implication is
a degenerate universal quantifier.

We illustrate this on a tiny example about natural numbers. Recall that in a previous lecture
we proved that 0 is the right identity of addition. The proof was by `rfl`:
-/

def AddZeroId (n : Nat) := n + 0 = n    -- this is our predicate
#check AddZeroId

theorem add_zero : ∀ n : Nat, AddZeroId n := by
  intro n        -- n : Nat ⊢ n + 0 = n
  rfl

/-
Here `rfl` works because `n + 0` computes to `n`: indeed, addition was defined
by recursion on its second argument.
-/

/-
The type-theoretic nature of the proof becomes more evident when we write it in term mode.
The proof is a function that takes `n` as input, and returns `rfl`, a proof that `n + 0 = n`.
-/
theorem add_zero_term : ∀ n : Nat, AddZeroId n :=
  fun _n => rfl


/-
In the next theorem, `P : A → Prop` is an arbitrary predicate on type `A`.
It states that what holds for all `x` also holds for a specific `a`.
-/

theorem univ_inst {A : Type} {P : A → Prop} (a : A) : (∀ x, P x) → P a := by
  intro h
  apply h a

/- The proof in term mode is similar. -/

theorem univ_inst_term {A : Type} {P : A → Prop} (a : A) : (∀ x, P x) → P a :=
  fun h => h a

/-
Why does this proof term work? In the proof context, we have:
** `a : A`
** `∀ x, P x`, a function that takes as input any `x : A` and returns a proof of `P x`.

A term of type `(∀ x, P x) → P a` is then a function that takes as input `h : ∀ x, P x`,
applies to `a`, and outputs a proof of `P a`.
-/


/-
We now prove another interesting theorem about implication and universal quantification.
If `P` implies `Q` for every `x`, and `P` holds for every `x`, then `Q` holds for every `x`.
-/

theorem forall_imp_forall {A : Type} {P Q : A → Prop} :
    (∀ x, P x → Q x) → (∀ y, P y) → ∀ z, Q z := by
  intro hpq hp z
  have pz : P z := by apply hp z
  have pqz : P z → Q z := by apply hpq z
  apply pqz pz

/-
Let's analyse the proof in terms of the Curry-Howard correspondence. We have:
** `hpq : ∀ x, P x → Q x`, a function that transforms `x` into a proof of `P x → Q x`
** `hp  : ∀ y, P y`, a function that transforms `y` into a proof of `P y`

The goal is to prove `∀ z, Q z`, i.e. a function that transforms `z` into a proof of `Q z`.

The proof term is straightforward:
1. we apply `hp` to z, obtaining a proof of `P z`
2. we apply `hpq` to `z`. The output is a function of type `P z → Q z`
3. we apply this function to the proof of `P z` obtained at step 1, obtaining a proof of `Q z`
-/

theorem forall_imp_forall_term {A : Type} {P Q : A → Prop} :
    (∀ x, P x → Q x) → (∀ y, P y) → ∀ z, Q z :=
  fun hpq hp z => hpq z (hp z)


/-
__Checkpoint 2__  The same symbol `∀` can quantify over objects, over propositions,
and over types. Predict the *type* of each of the following statements: is it a `Prop`,
or something bigger? (Recall the note on universes in the lab on polymorphism.)
-/

-- #check (∀ n : Nat, n + 0 = n)
-- #check (∀ P : Prop, P → P)
-- #check (∀ A : Type, A → A)

/-
Note that the third has type `Type 1`: it is the type of the polymorphic identity function
we have seen in one of the previous labs.

So **polymorphism corresponds to universal quantification over types**:
`∀ A : Type, A → A` and `∀ P : Prop, P → P` are morally the same statement,
one about types and one about propositions.

Every theorem of the previous lab, such as `P ∧ Q → Q ∧ P`, was already *implicitly*
quantified over all propositions `P` and `Q`: the braces `{P Q : Prop}` of the theorem
are actually a `∀` that Lean hides from us.

We can rewrite the statement with an *explicit* universal quantification as follows:
-/

example : ∀ P Q : Prop, P ∧ Q → Q ∧ P :=
  fun _ _ ⟨p, q⟩ => ⟨q, p⟩


/- __Exercise (difficulty: 2/4)__ If every `x` satisfies `P`, or every `x` satisfies `Q`,
then every `x` satisfies `P` or `Q`. -/

theorem forall_or {A : Type} {P Q : A → Prop} :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x := by
  sorry

theorem forall_or_term {A : Type} {P Q : A → Prop} :
    (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
  sorry

/-
Note that the previous proof works as well to show the following type is inhabited.
-/

def forall_or_term_data {A B C : Type} :
    (A → B) ⊕ (A → C) → (A → B ⊕ C) :=
  fun h x => match h with
  | .inl hp => .inl (hp x)
  | .inr hq => .inr (hq x)


/-
__Checkpoint 3__  Is the **converse** of the last exercise provable?

    (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)

Think about natural numbers with `P x` = "`x` is even" and `Q x` = "`x` is odd".
Then think of the hypothesis as a *program*: what does it compute, and what would
the conclusion require us to build?
-/

end Universal



section Existential

/-
## The existential quantifier

A proof of `∃ x : A, P x` is a **pair** `⟨a, h⟩`, where `a : A` is a *witness* and
`h : P a` is a proof that the witness has the property `P`.
The type of the second component depends on the first one: this is a *dependent pair*.

Introducing an `∃` means choosing a witness.  *Using* an `∃` means opening the pair: we
get a witness `x` (about which we know nothing, except what its proof says) and a proof
`hx : P x`.

In term mode, a proof is a pair `⟨a,h⟩`, where `h : P a`.
When the goal is a *closed* computation, the second component is usually `rfl`.

In tactic mode, `exists a` supplies the witness `a` and then tries to close the goal `P a`
automatically with `trivial` (which succeeds, for instance, on goals provable by `rfl`).
If `trivial` fails, the goal `P a` remains open and we must prove it ourselves, as in
`exists_mono` below.
-/

theorem exists_five : ∃ n : Nat, n + 2 = 5 := by
  exists 3

theorem exists_five_term : ∃ n : Nat, n + 2 = 5 :=
  ⟨3, rfl⟩


/-
__Exercise (difficulty: 1/4)__ Prove that there are two natural numbers satisfying the
following constraints.
-/

theorem exists_pair : ∃ n : Nat, ∃ m : Nat, n + m = 5 ∧ n+1 = m := by
  sorry

/- In the proof term, be aware that your goal is a conjunction. -/
theorem exists_pair_term : ∃ n : Nat, ∃ m : Nat, (n + m = 5 ∧ n+1 = m) :=
  sorry


/- __Exercise (difficulty: 1/4)__ Existential introduction:
if `a` satisfies `P`, then there exists some `x` that satisfies `P`. -/

theorem exists_intro {A : Type} {P : A → Prop} (a : A) : P a → ∃ x, P x := by
  sorry

theorem exists_intro_term {A : Type} {P : A → Prop} (a : A) : P a → ∃ x, P x :=
  sorry


/- The following proof shows how to use an existential in the context.
Recall that a proof of `∃ x, P x` is a pair `⟨a, pa⟩`, where `pa` is a
proof of `P a`. We can then match an `∃ x, P x` in the context as we
do for pairs, and use its witness and proof to prove the goal. -/

theorem exists_mono {A : Type} {P Q : A → Prop} :
    (∀ x, P x → Q x) → (∃ x, P x) → ∃ x, Q x := by
    intro f h
    rcases h with ⟨a, pa⟩
    exists a
    apply f a
    exact pa

/- The proof term is similar. We can write it succinctly using some syntactic sugar. -/

theorem exists_mono_term {A : Type} {P Q : A → Prop} :
    (∀ x, P x → Q x) → (∃ x, P x) → ∃ x, Q x :=
    fun f ⟨a,pa⟩ => ⟨a,f a pa⟩


/- __Exercise (difficulty: 2/4)__ If some `x` satisfies both `P` and `Q`,
then some `x` satisfies `P` and some `x` satisfies `Q`. -/

theorem exists_and {A : Type} {P Q : A → Prop} :
    (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x) := by
  sorry


/-
__Checkpoint 4__  Is the **converse** of the last exercise provable?

    (∃ x, P x) ∧ (∃ x, Q x) → ∃ x, P x ∧ Q x

Can you find two predicates `P` and `Q` such that `∃ x, P x` and `∃ x, Q x` are true,
but `∃ x, P x ∧ Q x` is false?
-/


/- __Exercise (difficulty: 3/4)__ Quantifier alternation: if there is a single `x` that
is related by `R` to every `y`, then every `y` is related to some `x`. -/

theorem exists_forall_forall_exists {A B : Type} {R : A → B → Prop} :
    (∃ x, ∀ y, R x y) → ∀ y, ∃ x, R x y := by
  sorry


/-
__Checkpoint 5__  Is the **converse** `(∀ y, ∃ x, R x y) → ∃ x, ∀ y, R x y` provable?
(Take `R x y` = "`x` is a friend of `y`".  Compare the two English sentences "everybody has
a friend" and "somebody is a friend of everybody".)  What is the difference between the two
statements when you read them as programs?
-/

end Existential



section Negation

/-
## Quantifiers and negation

Recall that `¬A` means `A → False`.  How do `¬`, `∀` and `∃` interact?
The "De Morgan laws for quantifiers" say that "not exists" is "for all not", and
"not for all" is "exists not". As in propositional logic, only some of these laws are
provable in constructive logic. We prove some of them below.
-/

/- __Exercise (difficulty: 2/4)__ There is no `x` satisfying `P` iff all `x` fail to
satisfy `P`. -/

theorem not_exists_forall_not {A : Type} {P : A → Prop} :
  (¬ ∃ x, P x) ↔ ∀ x, ¬ P x := by
  sorry

end Negation



section Bounded_quantifiers

/-
## Quantifying over the elements of a list

In programs we usually quantify not over *all* objects of a type, but over the elements of
a given collection, such as a list `l : List A`.  Lean has a shorthand for this:

    ∀ x ∈ l, P x       means   ∀ x, x ∈ l → P x        ("every element of l satisfies P")
    ∃ x ∈ l, P x       means   ∃ x, x ∈ l ∧ P x        ("some element of l satisfies P")

So a bounded `∀` is a `∀` followed by `→`, and a bounded `∃` is an `∃` followed by `∧`.
Lean accepts these equations by `rfl`:
-/

example : 2 ∈ [1,5,2,3] := by trivial
example : ¬ (4 ∈ [1,5,2,3]) := by trivial

example {A : Type} {P : A → Prop} {l : List A} :
    (∀ x ∈ l, P x) = (∀ x, x ∈ l → P x) := rfl

example {A : Type} {P : A → Prop} {l : List A} :
    (∃ x ∈ l, P x) = (∃ x, x ∈ l ∧ P x) := rfl

/-
Rule of thumb: **`∀` goes with `→`, and `∃` goes with `∧`.**  Note that:
* `∀ x, x ∈ l ∧ P x` would say that *every object* belongs to `l` (false in general),
* `∃ x, x ∈ l → P x` would be satisfied by any object that does not belong to `l`.

A bounded quantifier over the **empty** list `l` is a special case:
* `∀ x ∈ l, P x` is true: in an empty list, no element can violate `P`
* `∃ x ∈ l, P x` is false: in an empty list, there cannot be any element satistying `P`.
-/

theorem forall_nil_tac {A : Type} {P : A → Prop} : ∀ x ∈ ([] : List A), P x := by
  intro x hx
  cases hx

theorem forall_nil_term {A : Type} {P : A → Prop} : ∀ x ∈ ([] : List A), P x :=
  fun _ hx => nomatch hx

/- __Exercise (difficulty: 1/4)__ Prove the dual result of `forall_nil` for exists. -/

theorem not_exists_nil_tac {A : Type} {P : A → Prop} : ¬ ∃ x ∈ ([] : List A), P x := by
  sorry

theorem not_exists_nil_term {A : Type} {P : A → Prop} : ¬ ∃ x ∈ ([] : List A), P x :=
  sorry

end Bounded_quantifiers



section Disproving_false_conjectures

/-
## Disproving false conjectures

Not every proposition that we can state in Lean is true. When a conjecture is false,
our goal is to prove its *negation*.

Recall that

    ¬ P

is notation for

    P → False

Therefore, to prove `¬ P`, we assume that `P` holds and derive a contradiction:

    intro h       -- assume h : P
    ...
                  -- derive False

Here is a simple example. We assume that the two Bool constructors are equal.
Since different constructors cannot be equal, `cases h` closes the proof.
-/

example : ¬ (false = true) := by
  intro h
  cases h


/-
### Disproving a universal statement

To disprove a statement of the form

    ∀ x, P x

it is sufficient to find one particular value `a` for which `P a` is false.
The value `a` is called a *counterexample*.

For example, consider the false conjecture that every Boolean value is `true`.
After assuming the conjecture, we apply it to `false`, obtaining the impossible equality.
-/

example : ¬ (∀ b : Bool, b = true) := by
  intro h
  have hfalse : false = true := h false
  cases hfalse


/-
The general proof pattern can be stated as a theorem. If there exists an `x`
for which `P x` is false, then it is not the case that `P x` holds for every `x`.

This is a constructive quantifier-negation principle, now interpreted as the familiar
method of disproving a universal conjecture by giving a counterexample.
-/

theorem counterexample_disproves_forall {A : Type} {P : A → Prop} :
    (∃ x, ¬ P x) → ¬ ∀ x, P x := by
  intro hcex hall
  rcases hcex with ⟨a,npa⟩
  have pa : P a := hall a
  exact npa pa      -- contradiction


/-
### Disproving a supposed logical law

Consider the following conjecture:

  For every type `A` and every two predicates `P` and `Q` over `A`,
  if some element satisfies `P` and some element satisfies `Q`,
  then some element satisfies both `P` and `Q`.

In symbols:

  ∀ (A : Type) (P Q : A → Prop),
    (∃ x, P x) ∧ (∃ x, Q x) →
      ∃ x, P x ∧ Q x

Note that the two existential hypotheses may have *different witnesses*.

For instance, take:

* `A` to be `Bool`;
* `P b` to mean `b = false`;
* `Q b` to mean `b = true`.

There exists a Bool satisfying `P` (witness: `false`), and one satisfying `Q`,
(witness: `true`). However, no Bool is both `false` and `true`.
-/

def IsFalse : Bool → Prop := fun b => b = false
def IsTrue  : Bool → Prop := fun b => b = true

example :
    ¬ (∀ (A : Type) (P Q : A → Prop),
        ((∃ x, P x) ∧ (∃ x, Q x) →
          ∃ x, P x ∧ Q x)) := by
  intro h

  /- We instantiate the supposed law with `Bool` and the predicates given above. -/
  have hboth : ∃ x, IsFalse x ∧ IsTrue x := by
    apply h Bool IsFalse IsTrue
    constructor
    . exact ⟨false, rfl⟩
    . exact ⟨true, rfl⟩

  /- Back to the main goal: some Bool `b` is both `false` and `true`. -/
  rcases hboth with ⟨b, ⟨hbfalse,hbtrue⟩⟩
  unfold IsFalse at hbfalse
  unfold IsTrue at hbtrue

  /- Replacing `b` with `false` in `hbtrue` produces the equality `false = true`. -/
  rw [hbfalse] at hbtrue
  cases hbtrue    -- contradiction

/-
Notice the position of the negation:

  ¬ (∀ A P Q, ...)

says that the property cannot hold for all choices of `A`, `P`, and `Q`.
We proved it by exhibiting one choice for which the property fails.
(The opposite reasoning, from `¬ ∀` to the existence of a specific counterexample,
is *not* constructively valid: see the section `Classical_boundary`).

By contrast,

  ∀ A P Q, ¬ (...)

would say that the property fails for *every* choice of `A`, `P`, and `Q`.
That much stronger statement is false. For example, it does not fail when
`P` and `Q` are both always true.
-/


/-
__Exercise (difficulty: 1/4)__ Disprove the following purported logical law.
-/

example : ¬ (∀ P Q : Prop, P ∨ Q → P) := by
  sorry


end Disproving_false_conjectures



section Classical_boundary

/- ### The classical boundary for quantifiers

The converse of the previous theorem `exists_not_not_forall` is:

  (¬ ∀ x, P x) → ∃ x, ¬ P x

Let's try to start a tactic proof, and look at the goal after `intro h`.
-/

theorem not_forall_exists_not_sorry {A : Type} {P : A → Prop} : (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  sorry

/-
After `intro h` the goal is `∃ x, ¬ P x`: to prove it we must exhibit a witness `x`
and a refutation of `P x`.  The hypothesis `h : ¬ ∀ x, P x` only tells us that a
universal statement fails; it does not tell us **which** `x` is a counterexample,
and there is no way to compute one.  This statement is *not* provable constructively.
-/

/-
When we choose to reason classically, Lean provides the theorem `Classical.byContradiction`

  Classical.byContradiction {p : Prop} (h : ¬p → False) : p

We use this classical principle to prove `not_forall_exists_not`.
-/

#check Classical.byContradiction

theorem not_forall_exists_not {A : Type} {P : A → Prop} :
    (¬ ∀ x, P x) → ∃ x, ¬ P x := by
  intro h
  apply Classical.byContradiction
  intro hne                       -- hne : ¬ ∃ x, ¬ P x  ⊢ False
  apply h                         -- ⊢ ∀ x, P x
  intro x
  apply Classical.byContradiction
  intro hnp                       -- hnp : ¬ P x  ⊢ False
  apply hne
  exact ⟨x, hnp⟩

/- The theorem `counterexample_disproves_forall` has no classical dependencies, while
`not_forall_exists_not` depends on Lean's classical axioms.
The command `#print axioms` allows us to inspect this distinction. -/

#print axioms counterexample_disproves_forall
#print axioms not_forall_exists_not


end Classical_boundary



section Equality

/-
## Equality

As seen in lab lecture `PL02_Nat`, equality `a = b` is not a primitive notion: it is an
*inductive type family* with one constructor `Eq.refl`:

  Eq.refl a : a = a

The term and tactic `rfl` ask Lean to construct an equality proof using `Eq.refl`.
-/

/-
Lean accepts `rfl` as a proof of `a = b` whenever `a` and `b` are **definitionally equal**,
i.e. they become the same by unfolding definitions and computing.

The elimination rule is *substitution of equals* (Leibniz's principle): if `a = b` and
`P a` holds then `P b` holds.
-/

/-
__Checkpoint 6__  Which of the following claims does Lean accept, and why?
-/

-- example (n : Nat) : n + 0 = n := rfl
-- example (n : Nat) : 0 + n = n := rfl
-- example : 2 + 2 = 4 := rfl


/- __Exercise (difficulty: 1/4)__ Symmetry of equality.  -/

theorem eq_symm {A : Type} {a b : A} : a = b → b = a := by
  sorry

end Equality



section Dependent_types

/-
## Dependent types as data

So far, `∀` and `∃` have appeared as *logic*, with `Prop`.  The same constructions exist for
*data*, with `Type`, and this is where the name "dependent types" comes from.

Both quantifiers are built from a **family of types**: a function `B : A → Type` (or
`B : A → Prop`, which we called a *predicate*), so that for every `a : A` there is a type
`B a`.

* The type of **dependent functions** `(x : A) → B x` contains the functions `f` such that
  `f a : B a` for every `a : A`.  The *type of the result* depends on the argument.
* The type of **dependent pairs** `(x : A) × B x` contains the pairs `⟨a, b⟩` with `a : A`
  and `b : B a`.  The *type of the second component* depends on the first component.

When the family lives in `Prop` we obtain logic; when it lives in `Type` we obtain data:

    Logic (P x : Prop)         Data (B x : Type)          Name
    -------------------------  -------------------------  ---------------------------
    ∀ x : A, P x               (x : A) → B x              dependent function (Π-type)
    ∃ x : A, P x               (x : A) × B x              dependent pair     (Σ-type)

If `B` does not mention `x`, we obtain the ordinary connectives.  For functions this is
literally true: in Lean, `(x : Nat) → Bool` *is* the type `Nat → Bool`.
-/

example : ((x : Nat) → Bool) = (Nat → Bool) := rfl

/-
For pairs, `(x : A) × B` and `A × B` are two *different* types, but they are isomorphic:
we will define the isomorphism in an exercise below.
-/

/-
Types are ordinary values of Lean, so we can write *functions that return types*.
The following function takes a Boolean and returns a type: `Nat` if the Boolean is `true`,
`String` if it is `false`.  We declare it with `abbrev` so that Lean unfolds it
automatically when needed.
-/

abbrev Choice : Bool → Type
  | true  => Nat
  | false => String

#check Choice          -- a function from Bool to Type
#check Choice true     -- a type
example : Choice true = Nat := rfl
example : Choice false = String := rfl

/-
`Choice` is a family of types indexed by `Bool`. Here is a dependent function whose type is
`(b : Bool) → Choice b`: given `b`, it returns a *natural number* when `b` is `true`, and a
*string* when `b` is `false`. When we define it by pattern matching on `b`, the expected type
of each branch is obtained by computing `Choice` on that constructor:
-/

def pick : (b : Bool) → Choice b
  | true  => 42
  | false => "forty-two"

#check pick

#eval pick true
#eval pick false

/- The function `pick` has type `(b : Bool) → Choice b`: the type of `pick true` is not the
same as the type of `pick false`.  This is exactly like a proof of `∀ x, P x`, whose result
`h a : P a` has a type (a proof) that depends on `a`.

The dependent *pair* type `(b : Bool) × Choice b` contains pairs whose first component
is a Boolean, and whose second component has the type `Choice` of the first. -/

def pickPair : (b : Bool) × Choice b :=
  ⟨true, 42⟩

#check pickPair


/-
A proof of `∃ x, P x` has the same *shape* as a dependent pair, but it is a proposition,
and Lean treats all proofs of a proposition as equal: the witness cannot be extracted
into data. If we want to keep the witness, we must use a *data* type, such as the
subtype `{n : Nat // n * n = 4}` of numbers with a property: its elements are pairs of a
number `val` and a proof `property`.
-/

theorem sqrt4_exists : ∃ n : Nat, n * n = 4 :=
  ⟨2, rfl⟩

/-
Although the proof of `sqrt4_exists` was constructed using the witness 2, its type only exposes an existential proposition. Lean does not allow an arbitrary proof of `∃ n, P n` to be eliminated into computational data such as `Nat`.

With a **subtype**, instead, the witness is deliberately stored as data and can be accessed through `.val`.

Classical choice can select a witness from an existential proof, but the resulting definition is noncomputable.
-/

def sqrt4 : {n : Nat // n * n = 4} :=
  ⟨2, rfl⟩


#eval sqrt4.val           -- from `sqrt4` we can *compute* `sqrt4.val`, which is `2`. -/
#check sqrt4.property     -- the proof that `val` satisfies the property


/-
**Induction is a dependent function.**  The induction principle on natural numbers is itself a
universally quantified statement, over *all predicates* `P`.  Its proof term is the recursor
`Nat.rec`, the dependent version of recursion that you used to define functions on `Nat`.
-/


#check @Nat.rec

theorem nat_induction {P : Nat → Prop} (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact hs k ih

/-
So **recursion on data and induction in proofs are the same construction**, one for `Type`
and one for `Prop`.  This is the Curry–Howard isomorphism at its most general.
-/

end Dependent_types
