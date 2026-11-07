import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime.Inventory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation
open SourceNativeInquiryRuntime

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.NativeFrame input)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (claim : Responsibility.Family.Claim mechanism past nature response)
  (origin : Source.OriginAt input frame visit claim)
  (word : RawEvent Party Good Port Technology Instrument)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (Source.sourceEntry input frame visit))
  [Finite frame.root.toAuthoritativeRoot.source.projectionLaw.Projection]

local notation "firstSource" => source input frame visit claim origin word authority
local notation "nextPresentation" => target input frame visit claim word
local notation "admission" => Installation.generated input frame visit claim origin word authority

omit [Finite frame.root.toAuthoritativeRoot.source.projectionLaw.Projection] in
theorem source_successor_valid (query : (firstSource).Query) :
    (nextPresentation 0).erase = (RootInquiryProcessNode.answered firstSource query).erase ∧
      (RootInquiryProcessNode.active firstSource).PreservesGeneratedLivingLawAt query (.active (nextPresentation 0)) := by
  cases query
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid firstSource (nextPresentation 0) PUnit.unit admission
  · rfl
  · exact (congrArg (fun current =>
      (⟨(admission).target.TargetN,current⟩ : AnyAuthoritativeRootCurrent))
      (admission).target.targetAnswerAndNext_next_eq).symm
  · exact HEq.rfl

inductive Stage
  | input | body (index : Nat)

def process : SourceNativeInquiryEngineProcess where
  State := Stage
  stateAt := fun stage => .active (match stage with | .input => firstSource | .body n => nextPresentation n)
  erase_injective := by
    intro left right leftState rightState leftActive rightActive same
    cases leftActive
    cases rightActive
    cases left with
    | input => cases right with
      | input => rfl
      | body n => exact (source_ne_target input frame visit claim origin word authority n same).elim
    | body n => cases right with
      | input => exact (source_ne_target input frame visit claim origin word authority n same.symm).elim
      | body m =>
          exact congrArg Stage.body (Source.Inquiry.presentation_erase_injective
            input (Installation.native input frame visit claim word) visit claim word same)
  initial := .input
  successorAt := by
    intro stage query
    cases stage with
    | input => exact ⟨.body 0,source_successor_valid input frame visit claim origin word authority query⟩
    | body n => exact ⟨.body (n + 1),Source.Inquiry.successor_valid
        input (Installation.native input frame visit claim word) visit claim word n query⟩

def runtime : SourceNativeInquiryRuntime (process input frame visit claim origin word authority) where
  activationLaw := Engine.SourceNativeInquiryActivationLaw.ofUnique PUnit.unit
    (by intro candidate; cases candidate; rfl)
    (by intro stage query; cases stage <;> exact PUnit.unit)
    (by intro stage query candidate; cases stage <;> cases candidate <;> rfl)

theorem the_compulsory_admission_is_consumed_by_the_named_canonical_runtime :
    RootInquiryProcessNode.ResolutionAt.ContainsDebtAdmissionActualAction
      ((runtime input frame visit claim origin word authority).tickAt 0).resolution admission := by
  have emitted := ((runtime input frame visit claim origin word authority).tickAt 0).resolution_eq_generated
  have selected := RootInquiryProcessNode.active_debtAdmission_resolution_eq firstSource PUnit.unit admission rfl
  have total := emitted.trans selected
  exact Eq.mpr (congrArg (fun resolution =>
    RootInquiryProcessNode.ResolutionAt.ContainsDebtAdmissionActualAction resolution admission) total) HEq.rfl

theorem the_generated_next_is_the_active_family_root :
    ((runtime input frame visit claim origin word authority).stateAt 1).engine.node = .active (nextPresentation 0) := rfl

theorem the_actual_repair_then_keeps_its_residual_root_active :
    ((runtime input frame visit claim origin word authority).stateAt 2).engine.node = .active (nextPresentation 1) := rfl

theorem the_actual_observed_answer_is_the_same_physical_update :
    HEq ((runtime input frame visit claim origin word authority).tickAt 2).answer
      (Source.observed input frame visit claim word) := HEq.rfl

#print axioms runtime
#print axioms the_compulsory_admission_is_consumed_by_the_named_canonical_runtime
#print axioms the_actual_repair_then_keeps_its_residual_root_active

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Action.Runtime
