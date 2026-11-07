import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Identity
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion SourceNativeInquiryRuntime
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument] [DecidableEq Technology]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (claim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

inductive Stage
  | source | native (index : Nat)

def process : SourceNativeInquiryEngineProcess where
  State := Stage
  stateAt := fun stage => .active (match stage with
    | .source => presentation seed claim
    | .native n => answerPresentation seed claim n)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases leftActive
    cases rightActive
    cases left with
    | source => cases right with
      | source => rfl
      | native n => exact (source_ne_target seed claim n same).elim
    | native n => cases right with
      | source => exact (source_ne_target seed claim n same.symm).elim
      | native m => exact congrArg Stage.native (answer_presentation_erase_injective seed claim same)
  initial := .source
  successorAt := by
    intro stage query
    cases stage with
    | source => exact ⟨.native 0,source_successor_valid seed claim query⟩
    | native n => exact ⟨.native (n + 1),successor_valid seed claim n query⟩

def runtime : SourceNativeInquiryRuntime (process seed claim) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique PUnit.unit
    (by intro candidate; cases candidate; rfl)
    (by intro stage query; cases stage <;> exact PUnit.unit)
    (by intro stage query candidate; cases stage <;> cases candidate <;> rfl)

theorem the_source_programme_is_consumed_by_the_named_canonical_runtime :
    RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction
      ((runtime seed claim).tickAt 0).resolution (generated seed claim) := by
  have actual := ((runtime seed claim).tickAt 0).resolution_eq_generated
  have selected := RootInquiryProcessNode.active_actualAction_resolution_eq
    (presentation seed claim) PUnit.unit (generated seed claim) rfl
  have total := actual.trans selected
  exact Eq.mpr (congrArg (fun resolution =>
    RootInquiryProcessNode.ResolutionAt.ContainsSequentialActualAction resolution (generated seed claim)) total) HEq.rfl

theorem the_first_activated_next_is_the_actual_body_successor :
    ((runtime seed claim).stateAt 1).engine.node = .active (answerPresentation seed claim 0) := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Material.Runtime
