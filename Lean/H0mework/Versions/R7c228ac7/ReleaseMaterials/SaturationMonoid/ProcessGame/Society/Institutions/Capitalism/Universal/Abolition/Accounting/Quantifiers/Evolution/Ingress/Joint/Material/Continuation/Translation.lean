import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private def identity (α : Type) : ConstructiveRetract α α := ⟨id,id,fun _ => rfl⟩

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

def translation : TypedSemanticWorldNetworkTranslationAt (OldN seed claim) (NewN seed claim) where
  support := supportRetract seed claim
  anchor := identity _
  incidence := identity _
  lineage := identity _
  responsibility := keys seed claim
  claim := claims seed claim
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := rows seed claim
  oldOpenClaim_commutes := by
    rintro ⟨⟨background,productive⟩,gross⟩ ⟨key,opened⟩
    cases key with
    | inl old => cases old with
        | inl original => rfl
        | inr productiveKey => cases productive with
            | none => exact opened.elim
            | some state => rfl
    | inr grossKey => cases gross with
        | none => exact opened.elim
        | some state => rfl
  oldOpenProgressBudget_commutes := by
    rintro ⟨⟨background,productive⟩,gross⟩ ⟨key,opened⟩
    cases key with
    | inl old => cases old with
        | inl original => rfl
        | inr productiveKey => cases productive with
            | none => exact opened.elim
            | some state => exact the_actual_remaining_budget_is_literal seed claim state
    | inr grossKey => cases gross with
        | none => exact opened.elim
        | some state => rfl
  oldHoldsSurvives := by
    rintro ⟨⟨background,productive⟩,gross⟩ key held
    cases key with
    | inl old => cases old with
        | inl original => exact held
        | inr productiveClaim => cases productive with
            | none => exact held.elim
            | some state => exact held
    | inr grossClaim => cases gross with
        | none => exact held.elim
        | some state => exact held
  oldDispositionSurvives := by
    intro support kind receipt
    cases kind with
    | supportSettlement => exact receipt
    | transfer => exact .inl receipt
    | lawSurfaceExtension => exact .inl receipt

theorem every_original_row_keeps_its_exact_relabelled_key
    (support : (OldN seed claim).Support) (row : OpenResponsibilityAt (OldN seed claim) support) :
    ((rows seed claim support).forward row).1 = (keys seed claim).forward row.1 := by
  rcases support with ⟨⟨background,productive⟩,gross⟩
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old => cases old with
      | inl original => rfl
      | inr productiveKey => cases productive with
          | none => exact opened.elim
          | some state => rfl
  | inr grossKey => cases gross with
      | none => exact opened.elim
      | some state => rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Continuation
