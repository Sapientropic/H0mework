import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Network

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private def switch {A B C : Type} : (A ⊕ B) ⊕ C → (A ⊕ C) ⊕ B
  | .inl (.inl first) => .inl (.inl first)
  | .inl (.inr middle) => .inr middle
  | .inr last => .inl (.inr last)

private def switchRetract (A B C : Type) : ConstructiveRetract ((A ⊕ B) ⊕ C) ((A ⊕ C) ⊕ B) where
  forward := switch
  backward := switch
  backward_forward := fun value => by cases value with
    | inl inside => cases inside <;> rfl
    | inr last => rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def keys : ConstructiveRetract (OldN seed claim).Responsibility (NewN seed claim).Responsibility :=
  switchRetract _ _ _

def claims : ConstructiveRetract (OldN seed claim).Claim (NewN seed claim).Claim := switchRetract _ _ _

def forwardRow (support : (OldN seed claim).Support) :
    OpenResponsibilityAt (OldN seed claim) support →
      OpenResponsibilityAt (NewN seed claim) (forwardSupport seed claim support) := by
  rcases support with ⟨⟨background,productive⟩,gross⟩
  rintro ⟨key,opened⟩
  cases key with
  | inl old => cases old with
      | inl original => exact ⟨.inl (.inl original),opened⟩
      | inr productiveKey => cases productive with
          | none => exact opened.elim
          | some state => exact ⟨.inr productiveKey,opened⟩
  | inr grossKey => cases gross with
      | none => exact opened.elim
      | some state => exact ⟨.inl (.inr grossKey),opened⟩

def backwardRow (support : (OldN seed claim).Support) :
    OpenResponsibilityAt (NewN seed claim) (forwardSupport seed claim support) →
      OpenResponsibilityAt (OldN seed claim) support := by
  rcases support with ⟨⟨background,productive⟩,gross⟩
  rintro ⟨key,opened⟩
  cases key with
  | inl old => cases old with
      | inl original => exact ⟨.inl (.inl original),opened⟩
      | inr grossKey => cases gross with
          | none => exact opened.elim
          | some state => exact ⟨.inr grossKey,opened⟩
  | inr productiveKey => cases productive with
      | none => exact opened.elim
      | some state => exact ⟨.inl (.inr productiveKey),opened⟩

def rows (support : (OldN seed claim).Support) : ConstructiveRetract
    (OpenResponsibilityAt (OldN seed claim) support)
    (OpenResponsibilityAt (NewN seed claim) (forwardSupport seed claim support)) where
  forward := forwardRow seed claim support
  backward := backwardRow seed claim support
  backward_forward := by
    rcases support with ⟨⟨background,productive⟩,gross⟩
    rintro ⟨key,opened⟩
    cases key with
    | inl old => cases old with
        | inl original => rfl
        | inr productiveKey => cases productive with
            | none => exact opened.elim
            | some state => rfl
    | inr grossKey => cases gross with
        | none => exact opened.elim
        | some state => rfl

theorem every_new_row_is_the_same_original_row (support : (OldN seed claim).Support)
    (row : OpenResponsibilityAt (NewN seed claim) (forwardSupport seed claim support)) :
    (rows seed claim support).forward ((rows seed claim support).backward row) = row := by
  rcases support with ⟨⟨background,productive⟩,gross⟩
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old => cases old with
      | inl original => rfl
      | inr grossKey => cases gross with
        | none => exact opened.elim
        | some state => rfl
  | inr productiveKey => cases productive with
      | none => exact opened.elim
      | some state => rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
