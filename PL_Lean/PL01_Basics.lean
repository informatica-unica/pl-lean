/-
# Introduction to functional programming and theorem proving in Lean

This file is both a lecture and a Lean program.  Read the comments from top to
bottom, but also place the cursor on each command and inspect Lean's Infoview.
You are encouraged to change expressions, introduce mistakes, and observe
Lean's responses.

In this lecture we will learn how to:

* inspect and evaluate Lean expressions;
* define constants and pure functions;
* use the built-in type `Bool`;
* use Boolean operators and conditional expressions;
* define functions by pattern matching;
* use functions as values;
* state a few simple properties and prove them with basic tactics.

Throughout the lecture you will be asked to solve several exercises.
Their difficulties use the following relative scale:

* **1/4:** one direct idea;
* **2/4:** two ideas must be combined;
* **3/4:** a more substantial construction or proof;
* **4/4:** an optional challenge.

You find additional extended exercises in the file `PL01_BasicsEx.lean`.
-/


/-
The option `autoImplicit false` asks Lean to report undeclared names instead of silently
turning some of them into implicit variables. This makes beginner mistakes easier to detect.
-/

set_option autoImplicit false


section Reading_this_file

/-
## How to read this file

Text between `/-` and `-/` is a block comment.
Text following `--` is a single-line comment.
Lean ignores comments when checking the program.

Lean code often contains Unicode symbols.  In the Lean editor, type a
backslash followed by an abbreviation and then a space.  For example:

* `\to` produces `→`;
* `\and` produces `∧`;
* `\or` produces `∨`;
* `\<` and `\>` produce `⟨` and `⟩`.
* `\alpha`,`\beta`,... produce `α` and `β`, ...
* `x\_1`, `y\^2` produce `x₁` and `y²`

Hovering over a symbol normally shows one or more available abbreviations.
This lecture mainly uses `→`, which denotes a function type.
-/

/-
  __Checkpoint 1__: Type a formula involving a few symbols in a comment.
  Don't worry if it is not valid Lean syntax for now.
-/

end Reading_this_file


section Queries

/-
## Expressions, values, and types

In an imperative language, we often think in terms of commands that update a
store: assign a variable, execute a loop, print a result, and so on.

Functional programming starts from a different viewpoint.  An expression has
a value, and evaluating the expression computes that value.  A pure function
maps inputs to outputs without modifying hidden state.

Every valid Lean expression also has a type.  A type tells us what kind of
value an expression produces and which operations may be applied to it.

Lean provides three useful commands for exploration:

* `#check e` asks Lean for the type of expression `e`;
* `#eval e` evaluates `e` and displays its value;
* `#print name` displays the declaration associated with `name`.

These commands help us interact with Lean, but they do not become part of the
program being defined.
-/

#check true         --- values have types
#check false
#check Bool         --- also types have types!

#eval true
#eval false

/-
Lean reports that `true` and `false` both have type `Bool`.

The type name is capitalized: `Bool`.
The two values are lowercase: `true` and `false`.

Importantly, we can also ask Lean to print how the type Bool is defined.
-/

#print Bool

/-
We see that Bool is an *inductive type*. We will return to this key feature later,
but for the moment note that `Bool` has two *constructors*:

* `Bool.false : Bool`
* `Bool.true : Bool`
-/

end Queries


section Defining_names

/-
We can give a name to a value using `def`.
-/

def theLightIsOn : Bool := true

#check theLightIsOn
#eval theLightIsOn
#print theLightIsOn

/-
Read the declaration as follows:

* `def` starts a definition;
* `theLightIsOn` is the new name;
* `: Bool` states its type;
* `:= true` gives the expression being named.

A Lean definition is not a mutable variable.  There is no later assignment
that changes `theLightIsOn` to `false`.  Definitions name values.
-/

end Defining_names



section Defining_functions

/-
## Defining and applying functions

A function definition lists its parameters before the result type.
-/

def negB (b : Bool) : Bool :=
  !b

#check negB
#eval negB true
#eval negB false

/-
The type of `negB` is:

    Bool → Bool

This is pronounced "Bool arrow Bool".  It says that `negB` accepts a Boolean
and produces a Boolean.

Function application is written by placing the argument after the function:

    negB true

In particular, Lean does not require the notation `negB(true)`.

Multiple parameters can be written next to one another.
-/

def andB (a b : Bool) : Bool :=
  a && b

#check andB
#eval andB true true
#eval andB true false


/-
__Exercise (difficulty: 1/4)__

Define a function `orB` that implements the disjunction connective.
-/

def orB (a b : Bool) : Bool :=
  sorry


/-
## Statements and proofs

A main feature of Lean is that is works as a *proof assistant*, in the sense that
it allows you to write statements and formally prove them.

As a first example, we consider a basic equality that is true "by definition".
-/

theorem false_and_any_is_false (a: Bool): andB false a = false := by
  rfl

/-
We have introduced a new theorem, named `false_and_any_is_false`, stating that
`andB false a` evaluates to `false` for any Bool parameter `a`.

Lean can prove this theorem simply by computation. After unfolding the
definition of `andB`, the left-hand side becomes:

      false && a

which evaluates to `false`, since the `&&` operator has a short-circuit semantics.
Therefore, both sides of the equality are identical, and `rfl` (reflexivity) closes the proof.

More complex statements usually require more complex tactics than `rfl`.

When we do not know how to complete a proof, wa can leave some parts of it unfinished,
mark them with `sorry`.
-/

theorem andB_commutative_sorry (a b : Bool) : andB a b = andB b a := by sorry


/-
__Checkpoint__: Try to replace `sorry` with `rfl` in the previous proof,
and see what happens in the Infoview.
-/


/-
Using `sorry` has several benefits:
* The incomplete code is accepted, without generating any error.
* When putting the cursor over each occurrence of `sorry`, Lean reports what is
  the expected type of the term that should be written at that point.
-/


/-
## Partial application

Lean displays the type of `andB` as:

    Bool → Bool → Bool

Arrows associate to the right, so this means:

    Bool → (Bool → Bool)

We may therefore supply the arguments one at a time. Applying `andB` to only
one argument produces another function.

This feature is called *partial application*.  It is one reason that functions
are especially convenient in functional programming.
-/

#check andB true

def mystery : Bool → Bool :=
  andB true

/-
__Exercise (difficulty: 1/4)__

Find a simpler way to define a function equivalent to the `mystery` above.
The function must satisfy the equality specified by the theorem `mystery_resolved`.
For the moment, leave the `sorry` in `mystery_resolved`.
-/

def mystery₂ : Bool → Bool :=
  sorry

theorem mystery_resolved (b: Bool): mystery b = mystery₂ b := by
  sorry


/-
## Anonymous functions

Functions do not need to have names.  The expression

    fun b : Bool => !b

is an anonymous function. It plays a role similar to a lambda expression in other languages.
-/

#check (fun b : Bool => !b)
#eval (fun b : Bool => !b) true

def negLambda : Bool → Bool :=
  fun b : Bool => !b

#eval negLambda true

/-
The ascii keywork `fun` can be equivalently written as the greek letter `\lambda`:
-/

def negLambda₂ : Bool → Bool :=
  λ b : Bool => !b

/-
The two definitions `negB` and `negLambda` compute exactly the same function.
The first notation is usually more convenient when naming a function; the second
makes it especially clear that functions are expressions and values.
-/

end Defining_functions



section Boolean_operators

/-
## Boolean operators

Lean provides the standard Boolean operations:

* `!a`       -- negation, "not a";
* `a && b`   -- conjunction, "a and b";
* `a || b`   -- disjunction, "a or b".

The following examples define their truth tables.
Examples can be seen as unnamed theorems.
-/

example : !true = false := by rfl
example : !false = true := by rfl

example : (false && false) = false := by rfl
example : (false && true)  = false := by rfl
example : (true  && false) = false := by rfl
example : (true  && true)  = true  := by rfl

example : (false || false) = false := by rfl
example : (false || true)  = true  := by rfl
example : (true  || false) = true  := by rfl
example : (true  || true)  = true  := by rfl

/-
We can build new Boolean operations from the existing ones.
An implication is false only when its first input is true and its second input is false.
-/

def impB (a b : Bool) : Bool :=
  (!a) || b

example : (impB false false) = true  := by rfl
example : (impB false true)  = true  := by rfl
example : (impB true  false) = false := by rfl
example : (impB true  true)  = true  := by rfl

/-
__Exercise (difficulty: 1/4)__ The *exclusive or* is true when exactly one input is true.
Define the connective, and give its truth table through examples.
-/

def xorB (a b : Bool) : Bool :=
  sorry

end Boolean_operators



section Conditional_expressions

/-
## Conditional expressions

In an imperative language, an `if` is a *command* that chooses which branch to execute.

In functional languages, an `if` is an *expression*: it computes a value.

So, both branches must produce values of the same type, and the `else` branch  is required.
-/

#eval if true  then 5 else 7
#eval if false then 5 else 7

#eval if impB false true then "hi" else "ciao"
#eval if andB true false then "hi" else "ciao"

/-
Note that there are no assignments and no `return` commands.  The value of the
selected branch is the value of the whole `if`.
-/

/-
__Checkpoint__: Try to write a conditional expression where the `true` branch evaluates to
a number, while the `false` branch evaluates to a string. Check the error in the Infoview.
-/


/- __Exercise (difficulty: 1/4)__ Redefine the negation using conditional expressions. -/

def negIf (b : Bool) : Bool :=
  sorry


/-
__Exercise (difficulty: 1/4)__ Redefine the implication using conditional expressions.
-/

def impIf (a b : Bool) : Bool :=
  sorry


/- __Exercise (difficulty: 1/4)__ Redefine the XOR using conditional expressions. -/

def xorIf (a b : Bool) : Bool :=
  sorry


/-
__Exercise__: Define a function `majority` that returns true when at least two
of its three inputs are true. Check if the tests below pass.
-/

def majority (a b c : Bool) : Bool :=
  sorry

example : majority true false true = true   := by
  sorry

example : majority false true true = true   := by
  sorry

example : majority false true false = false := by
  sorry

end Conditional_expressions



section Pattern_matching

/-
## Pattern matching

Since a Boolean has only two possible values, a function can explicitly say
what to do in each case.
-/

def negMatch (b : Bool) : Bool :=
  match b with
  | true  => false
  | false => true

example : negMatch true = false := by rfl
example : negMatch false = true := by rfl

/-
Lean checks that the patterns cover every possible input. If either case is
deleted, Lean reports that the match is not exhaustive.

There is also a compact equation style in which the parameters are matched directly.
-/

def negMatch₂ : Bool → Bool
  | true  => false
  | false => true

/-
We can pattern-match on more than one input.
Patterns are considered from top to bottom.
The underscore `_` is a *wildcard*: it matches any value when we do not need
to give that value a name.
-/

def andMatch : Bool → Bool → Bool
  | true,  b => b
  | false, _ => false

example : andMatch true false = false := by rfl


/- __Exercise (difficulty: 1/4)__: Redefine the implication using pattern matching. -/

def impMatch (a b : Bool) : Bool :=
  sorry


example : (impMatch false false) = true  := by
  sorry


/- __Exercise__: Redefine the XOR using pattern matching. -/

def xorMatch (a b : Bool) : Bool :=
  sorry

example : (xorMatch false false) = false := by
  sorry

end Pattern_matching



section Local_definitions

/-
## Local names with `let`

A complex expression can be made easier to read by giving an intermediate result a
local name. A `let` binding is not mutable: it names a value for the rest of the expression.
-/

def alarmShouldSound
    (armed doorOpen motionDetected : Bool) : Bool :=
  let intrusion := doorOpen || motionDetected
  armed && intrusion

#eval alarmShouldSound true false true
#eval alarmShouldSound false true true

/-
Compare this with an imperative local variable. We do not first store one value in
`intrusion` and later overwrite it. The name always denotes the same value within its scope.
-/

end Local_definitions


section Functions_as_values

/-
## Higher-order functions

Functions may be passed as arguments to other functions.  A function that
accepts or returns another function is called a *higher-order function*.

`applyTwice` accepts a function `f` and a Boolean `b`, then applies `f` two times.
-/

def applyTwice (f : Bool → Bool) (b : Bool) : Bool :=
  f (f b)

#eval applyTwice negB true
#eval applyTwice negB false

/-
The parameter `f` is used just like any other value. This ability is central
to functional programming and later supports reusable operations over lists,
trees, state transition systems, and many other structures.
-/

end Functions_as_values



section Proofs_basics

/-
## Proofs basics

Lean is both a programming language and a theorem prover.  After defining a
function, we can state and *mechanically verify* properties of it.

We have already proved some equations involving fixed Boolean values, such as:

    andB true true = true

These proofs can be completed with `rfl`. To check `rfl`, Lean *unfolds* the
definitions and performs the relevant computations. If both sides reduce to
the same expression, the equality is proved.

We can also prove statements quantified *for all* possible inputs. For example,
`andB false a` is `false` regardless of whether `a` is `true` or `false`.

Indeed, we have already developed such proof for the theorem `false_and_any_is_false`.
We can equivalently restate such theorem as follows:
-/

theorem false_and_any_is_false_forall :
  ∀ (a: Bool), andB false a = false := by
  intro a   --- instantiate the universally quantified variable
  rfl

/-
The symbol `∀` means "for all". Thus, the statement below reads:

    For all Boolean values `a`, `andB false a` is equal to `false`.

To prove theorems of this form, we usually start by saying "Suppose `a` is some Boolean ..."
Formally, this is rendered in the proof by `intros a`, which moves `a` from the quantifier
to the goal (place your cursor after the `intro a` and see what happend in the Infoview).

Note that the name `a` we chose with `intro a` is irrelevant: we could as well have used
another name instead of `a`, preserving the validity of the proof.

Then, the proof can be closed with `rfl`, since as we noted before `&&` is short-circuit.
-/

/-
## Propositions versus Boolean values

An important but subtle point is that Lean distinguishes Boolean values from propositions:

* `Bool` is a data type used for computation;
* `Prop` is the type of logical statements;

In particular, in our theorem `false_and_any_is_false`:
* `andB false a` computes a `Bool`;
* `andB false a = false` is a proposition asserting an equality.

The commands `example` and `theorem` state a proposition and ask you to provide a proof.

We will clarify this distinction in a future lab lecture: for the moment, we just focus
on Boolean values and implicitly deal with propositions when stating theorems.
-/

/-
## The `cases` tactic

We state below that Boolean negation is *involutory*, i.e. applying it twice results
in the original value. Its proof cannot be accomplished through reflexivity only
(try `rfl` and see what happens in the Infoview).

So, in this proof we introduce a new tactic: `cases`.

The tactic `cases b` creates one goal for `b = false` and another for `b = true`.
In our theorem, in each case the equality follows by computation, so `rfl` finishes it.
-/

theorem neg_is_involutory (b : Bool) : negB (negB b) = b := by
  cases b with
  | false => rfl
  | true  => rfl


/-
__Exercise (difficulty: 1/4)__ Prove that `negB` and `negIf` are equivalent.
-/

example (b : Bool): negB b  = negIf b  := by
  sorry


/-
__Exercise (difficulty: 1/4)__ Prove that `impB` and `impIf` are equivalent.
-/

example (a b : Bool) : impB a b = impIf a b := by
  sorry


/-
The `cases` tactic can be nested, similarly to conditional expressions.
This is useful when we need to deal with more than one inputs.
-/

theorem andB_commutative (a b : Bool) : andB a b = andB b a := by
  cases a with
  | false => cases b with
    | false => rfl
    | true  => rfl
  | true => cases b with
    | false => rfl
    | true  => rfl


/-
__Exercise (difficulty: 2/4)__ Prove that `xorB` and `xorMatch` are equivalent.
-/

example (a b : Bool) : xorB a b = xorMatch a b := by
  sorry


/-
## The `simp` tactic

The `simp` tactic repeatedly applies a collection of standard simplification rules.
It is convenient for routine Boolean identities.

For example, the following theorem states that true is a right identity of conjunction:
-/

theorem and_true_right (b : Bool) : andB b true = b := by
  simp [andB] --- unfold andB and apply known simplification rules for &&


/- An alternative proof can be done via case analysis. -/

theorem and_true_right_cases (b : Bool) : andB b true = b := by
  cases b with
  | false => rfl
  | true  => rfl


/- __Exercise (difficulty: 1/4)__: Prove that false is a right identity of disjunction. -/

theorem or_false_right (b : Bool) : orB b false = b := by
  sorry


/-
These proofs are intentionally small.  Their purpose is to show the basic workflow:

1. define a function;
2. state a precise property;
3. inspect the proof state in the Infoview;
4. use tactics to reduce the goal to elementary cases;
5. let Lean's kernel check the completed proof.
-/

end Proofs_basics
