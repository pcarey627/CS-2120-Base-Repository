/-
Patrick Carey
jpc9rr
-/

/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

--example : false :=    -- trick question? why? - There's no proof of false

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward direction 
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards direction
    assume p,
    exact or.intro_right P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
    assume pandp,
    apply and.elim pandp,
    assume p,
    assume p,
    exact p,
  --backward
    assume p,
    apply and.intro _ _,
    exact p,
    exact p,
end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro,
  -- P or Q implies Q or P
    assume porp,
    apply or.elim porp,
    -- P implies Q or P
      assume p,
      apply or.intro_right,
      exact p,
    -- Q implies Q or P
      assume q,
      apply or.intro_left,
      exact q,
  -- Q or P implies P or Q
    assume qorp,
    apply or.elim qorp,
    -- Q implies P or Q
    assume q,
    apply or.intro_right,
    exact q,
    -- P implies P or Q
    assume p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro,
  -- P and Q implies Q and P
    assume pandq,
    apply and.intro _ _,
    -- P and Q implies Q
      apply and.elim_right pandq,
    -- P and Q implies P
      apply and.elim_left pandq,
  -- Q and P implies P and Q
    assume qandp,
    apply and.intro _ _,
    --Q and P implies Q
      apply and.elim_right qandp,
    --Q and P implies P
      apply and.elim_left qandp,
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro,
--Left to right
  assume h,
  have p: P := and.elim_left h,
  have qr : Q ∨ R := and.elim_right h,
  cases qr,
  --Case where q or r is q
    apply or.intro_left,
    apply and.intro,
    exact p,
    exact qr,
  -- Case where q or r is r
    apply or.intro_right,
    apply and.intro,
    exact p,
    exact qr,
-- Right to Left
assume h,
cases h,
  -- Case where we have P and Q
  apply and.intro,
  apply and.elim_left h,
  apply or.intro_left,
  apply and.elim_right h,
  --Case where we have P and R
  apply and.intro,
  apply and.elim_left h,
  apply or.intro_right,
  apply and.elim_right h,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro,
  --Front direction
    assume h,
    cases h,
      -- Case where we have P
        apply and.intro,
        --Show P leads to P or Q
          apply or.intro_left,
          exact h,
        --Show P leads to P or R
          apply or.intro_left,
          exact h,
      --Case where we have Q and R
        apply and.intro,
        --Show Q and R leads to P or Q
          apply or.intro_right,
          apply and.elim_left h,
        --Show Q and R leads to P or R
          apply or.intro_right,
          apply and.elim_right h,
  -- Back direction
    assume h,
    have poq: (P ∨ Q) := and.elim_left h,
    have por: (P ∨ R) := and.elim_right h,
    cases poq,
      apply or.intro_left,
        exact poq,
      cases por,
        apply or.intro_left,
        exact por,
        apply or.intro_right,
        apply and.intro,
        exact poq,
        exact por,
     --Show P and Q or P and R leads to P    
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  assume h,
  apply and.elim_left h,
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro,
  -- Left to Right
    assume pandporq,
    apply or.elim pandporq,
    -- P implies P
      assume p,
      exact p,
    -- P and Q implies P
      apply and.elim_left,
  -- Right to left
    assume p,
    --Split right into p and P or Q
      apply or.intro_left,
      exact p,
  
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  --Left to right
      assume portrue,
      exact true.intro,
  -- Right to Left
      assume true,
      apply or.intro_right,
      exact true,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  --Left to Right
    assume porfalse,
    apply or.elim,
    exact porfalse,
    assume p,
    exact p,
    assume false,
    exact false.elim,
  --Right to Left
    assume p,
    apply or.intro_left,
    exact p,
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  apply and.elim_left,
  assume p,
  apply and.intro _ _,
  exact p,
  exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  apply and.elim_right,
  assume false,
  exact false.elim,
end


