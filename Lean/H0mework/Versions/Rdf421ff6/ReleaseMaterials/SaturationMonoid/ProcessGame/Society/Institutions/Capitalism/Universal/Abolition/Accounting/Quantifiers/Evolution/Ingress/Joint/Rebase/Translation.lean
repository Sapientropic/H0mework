import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Rows

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open Source.Program Innovation Quantifiers.Joint

noncomputable section

private def sumLeft {A B C : Type} (map : ConstructiveRetract A B) : ConstructiveRetract (A ⊕ C) (B ⊕ C) where
  forward := Sum.map map.forward id
  backward := Sum.map map.backward id
  backward_forward := by
    intro value
    cases value with
    | inl old => exact congrArg Sum.inl (map.backward_forward old)
    | inr same => rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

/-- One conservative re-presentation of the existing financial shape and
productive row. The initial ledger creates no restitution row or payment. -/
def translation : TypedSemanticWorldNetworkTranslationAt (OldN seed) (NewN seed grossClaim) where
  support := supportRetract seed grossClaim
  anchor := (Background.translation seed).anchor
  incidence := (Background.translation seed).incidence
  lineage := (Background.translation seed).lineage
  responsibility := sumLeft (Background.translation seed).responsibility
  claim := sumLeft (Background.translation seed).claim
  anchor_commutes := fun support => (Background.translation seed).anchor_commutes support.1
  incidence_commutes := fun support => (Background.translation seed).incidence_commutes support.1
  lineage_commutes := fun support => (Background.translation seed).lineage_commutes support.1
  oldOpenLedger := rowRetract seed grossClaim
  oldOpenClaim_commutes := by
    rintro ⟨support,state⟩ ⟨key,opened⟩
    cases key with
    | inl old => exact congrArg Sum.inl ((Background.translation seed).oldOpenClaim_commutes support ⟨old,opened⟩)
    | inr debt => cases state with
        | none => exact opened.elim
        | some old => rfl
  oldOpenProgressBudget_commutes := by
    rintro ⟨support,state⟩ ⟨key,opened⟩
    cases key with
    | inl old => exact (Background.translation seed).oldOpenProgressBudget_commutes support ⟨old,opened⟩
    | inr debt => cases state with
        | none => exact opened.elim
        | some old => rfl
  oldHoldsSurvives := by
    rintro ⟨support,state⟩ claim held
    cases claim with
    | inl old => exact (Background.translation seed).oldHoldsSurvives support old held
    | inr debt => cases state with
        | none => exact held.elim
        | some old => exact held
  oldDispositionSurvives := by
    rintro ⟨support,state⟩ kind receipt
    cases kind with
    | supportSettlement => exact (Background.translation seed).oldDispositionSurvives support .supportSettlement receipt
    | transfer =>
        cases receipt with
        | inl old => exact .inl ((Background.translation seed).oldDispositionSurvives support .transfer old)
        | inr active => cases state with
            | none => exact active.elim
            | some old => cases active with
                | inl step => exact .inr (.inl ⟨.legacy step.1,.legacy step.2⟩)
                | inr carry => exact .inr (.inr ⟨.legacy carry.1,.legacy carry.2⟩)
    | lawSurfaceExtension =>
        cases receipt with
        | inl old => exact .inl ((Background.translation seed).oldDispositionSurvives support .lawSurfaceExtension old)
        | inr active => cases state with
            | none => exact active.elim
            | some old => exact .inr active

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
