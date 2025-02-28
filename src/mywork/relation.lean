section relation
variables {α : Sort u} {β : Sort v} (r : β → β → Prop)
local infix `≺`:50 := r

def reflexive := ∀ x, x ≺ x

def symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x

def transitive := ∀ ⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

def equivalence := reflexive r ∧ symmetric r ∧ transitive r

def total := ∀ x y, x ≺ y ∨ y ≺ x

lemma mk_equivalence (rfl : reflexive r) (symm : symmetric r) (trans : transitive r) :
  equivalence r :=
⟨rfl, symm, trans⟩

def irreflexive := ∀ x, ¬ x ≺ x

def anti_symmetric := ∀ ⦃x y⦄, x ≺ y → y ≺ x → x = y

def empty_relation := λ a₁ a₂ : α, false

def subrelation (q r : β → β → Prop) := ∀ ⦃x y⦄, q x y → r x y

def inv_image (f : α → β) : α → α → Prop :=
λ a₁ a₂, f a₁ ≺ f a₂

lemma inv_image.trans (f : α → β) (h : transitive r) : transitive (inv_image r f) :=
λ (a₁ a₂ a₃ : α) (h₁ : inv_image r f a₁ a₂) (h₂ : inv_image r f a₂ a₃), h h₁ h₂

lemma inv_image.irreflexive (f : α → β) (h : irreflexive r) : irreflexive (inv_image r f) :=
λ (a : α) (h₁ : inv_image r f a a), h (f a) h₁

inductive tc {α : Sort u} (r : α → α → Prop) : α → α → Prop
| base  : ∀ a b, r a b → tc a b
| trans : ∀ a b c, tc a b → tc b c → tc a c
end relation