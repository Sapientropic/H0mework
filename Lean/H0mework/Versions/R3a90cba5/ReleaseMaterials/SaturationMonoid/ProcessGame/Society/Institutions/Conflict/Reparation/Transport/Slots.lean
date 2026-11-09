import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Keys
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Future.Structure

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld DebtActivationLedger

/-- An extension has exactly one row at an active support and no row
at an inactive support. -/
def Slot {law : DebtActivationLaw} : Option law.DebtState → Type
  | none => Empty
  | some _ => Unit

def expose (base : WorldRelationNetwork) (law : DebtActivationLaw) (support : base.Support) :
    (phase : Option law.DebtState) →
      (OpenResponsibilityAt base support ⊕ Slot phase) ≃
        OpenResponsibilityAt (ExtendedNetwork base law) (support, phase)
  | none =>
    { toFun := fun entry => match entry with
        | .inl old => oldEntry old
        | .inr inactive => nomatch inactive
      invFun := fun ⟨key, witness⟩ => match key with
        | .inl old => .inl ⟨old, witness⟩
        | .inr _ => nomatch witness
      left_inv := fun entry => by cases entry with
        | inl old => cases old; rfl
        | inr inactive => exact nomatch inactive
      right_inv := by
        rintro ⟨key, witness⟩
        cases key with
        | inl old => rfl
        | inr _ => exact nomatch witness }
  | some state =>
    { toFun := fun entry => match entry with
        | .inl old => oldEntry old
        | .inr _ => debtEntry support state
      invFun := fun ⟨key, witness⟩ => match key with
        | .inl old => .inl ⟨old, witness⟩
        | .inr _ => .inr ()
      left_inv := fun entry => by cases entry with
        | inl old => cases old; rfl
        | inr slot => cases slot; rfl
      right_inv := by
        rintro ⟨key, witness⟩
        cases key with
        | inl old => rfl
        | inr id => rcases witness with ⟨⟨same⟩⟩; subst id; rfl }

@[simp] theorem expose_old (base : WorldRelationNetwork) (law : DebtActivationLaw) (support : base.Support)
    (phase : Option law.DebtState) (entry : OpenResponsibilityAt base support) :
    expose base law support phase (.inl entry) = oldEntry entry := by
  cases phase <;> rfl

def swapMiddle (A B C : Type) : ((A ⊕ B) ⊕ C) ≃ ((A ⊕ C) ⊕ B) where
  toFun
    | .inl (.inl old) => .inl (.inl old)
    | .inl (.inr later) => .inr later
    | .inr retained => .inl (.inr retained)
  invFun
    | .inl (.inl old) => .inl (.inl old)
    | .inl (.inr retained) => .inr retained
    | .inr later => .inl (.inr later)
  left_inv value := by rcases value with (old | later) | retained <;> rfl
  right_inv value := by rcases value with (old | retained) | later <;> rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport
