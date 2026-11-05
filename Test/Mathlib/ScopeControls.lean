import Mathlib

example (p q : Prop) : p ∧ q → q ∧ p := by tauto
example (p q : Prop) : p ∨ q → q ∨ p := by tauto

universe u_1 u_2 u_3
example (α : Type u_1) (β : Type u_2) (γ : Type u_3)
    [DecidableEq α] (s t u v : Finset α) (a b : α) :
    a ∉ s → ((∀ a ∈ t, a ∉ s) ↔ ∀ ⦃a : α⦄, a ∈ s → a ∉ t) := by
  tauto
