/-
INTRODUCTION and ELIMINATION RULES
-/

/-
For ∀ x, P x (every x has property P)
  - introduction rule: assume arbitrary x, then show P x
  - elimination rule: *apply* a proof of ∀ x, P x, as a 
  kind of function to a specific value of x, say k, to 
  produce a proof of P k.
-/

theorem silly : ∀ (n : ℕ), true :=
begin
  assume (n : ℕ),
  exact true.intro, 
end

/-
The proposition true is unconditionally true,
as proven by an always available proof called
(in Lean) true.intro.
-/

#check silly 7

/-
The check command will tell you the type of any
expression (aka term) in Lean. Here we can see 
that silly is like a function, and that when we
apply it to the specific argument, 7, we get back
a proof of the resulting proposition (which is 
just, "true"). We'll soon be equipped to deal
with more interesting "return types".
-/

/-
For P → Q (if P is true then Q must also be true)
- introduction rule: assume arbitrary P, then show Q
- elimination rule: *apply* a proof of P → Q, as a
kind of function, to any proof of P to derive a proof of Q!
-/

lemma foo : ∀ (x : ℕ), x = 0 → x + 1 = 1 := 
begin
  assume x h,
  rw h,
end

/-
Wow! ∀ and → sure do seem similar. Indeed they're the same!
They define function types. We construct a proof of ∀ or → 
by assuming the premise and showing that in that context we
can derive a result of the conclusion type. We can then use
a proof of a ∀ or → by treating it as a function that can
be applied to a specific value to derive a proof *for that
specific value. Indeed, in Lean, → is really just another
notation for forall!

And :

P Q : Prop can be re-written as:
P ^ Q
introduction proof for and: and.intro 
  -takes an argument (proof) of P and argument (proof) of Q 
  get back a proof of P and Q
-/

axioms (P Q : Prop)

#check P
#check (P ∧ Q)

axioms (p: P) (q:Q)

example: P ∧ Q := and.intro p q 

/-
Prove that if arbitrary propisitions P and Q are true
(which is to say that we have a proof for each of them)
, that the proposition P ∧ Q is also true. 

Proof: The conjecture that P ∧ Q is true is proved by application 
of the introduction rule for and.
-/

example : 0 = 0 ∧ 1 =1 :=

begin
  apply and.intro _ _,
  apply eq.refl 0,
  apply eq.refl 1,
end

/-
ways of rewriting this proof
-/
theorem bar : 0 = 0 ∧ 1 =1 :=

begin
  apply and.intro (eq.refl 0) (eq.refl 1),
end

/-
And has two elimination rules:
  - an elimination rule that proves the left AND the right 
-/

#check bar

#check and.elim_right bar
#check and.elim_left bar

theorem and_commutative: ∀ (P Q : Prop), P ∧ Q → Q ∧ P :=
begin
  assume P Q h,
  apply and.intro _ _,
  apply and.elim_right h,
  apply and.elim_left h,
end
