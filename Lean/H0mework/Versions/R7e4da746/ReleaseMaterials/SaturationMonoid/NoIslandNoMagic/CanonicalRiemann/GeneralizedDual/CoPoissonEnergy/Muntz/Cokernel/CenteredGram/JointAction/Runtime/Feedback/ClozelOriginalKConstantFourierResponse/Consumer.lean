import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierResponse.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierResponseConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open FixedWindowFourierReaction FixedWindowFourierReaction.FullSchur
namespace A
export OriginalConstantFourierResponseAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actionState actionTrace action_value_source)
end A
namespace S
export OriginalConstantFourierResponseSource
  (result quarterValue quarter_actual actual_full_equation actual_existing_inverse
   environment etaCode inverse embed inputValue)
end S
namespace C
export OriginalConstantFourierNativeConsumer (eta u forcing)
end C
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value paid_history)
end OC
open private state_source trace_source trace_length expression normalizedTrace paid from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource

namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7) (input:BurnolL2)
local notation "reader" => (fun _ => OriginalConstantFourierResponseSource.Generated.reader
  root.toAuthoritativeRoot input (root.emitted visit.current))
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def etaInput : Σ value:BurnolL2,
    Trace (OriginalConstantFourierResponseSource.Generated.environment input) S.etaCode (.const value) ×
      PLift (S.inverse value=OC.value root.toAuthoritativeRoot visit.current reader) :=
  originalInput (actualTrace root visit u7 calculus input)
theorem eta_actual : (etaInput root visit u7 calculus input).1=
    OriginalConstantFourierResponseSource.center input :=
  (etaInput root visit u7 calculus input).2.1.sound.symm
theorem paid_three : (Adapter.state root visit u7 calculus reader).2.length=3 :=
  paid root visit u7 calculus reader
theorem value_source : Adapter.terminalValue root visit u7 calculus reader=
    (OriginalConstantFourierResponseSource.Generated.result root.toAuthoritativeRoot visit.current input).2.2.1 := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
end EndRead

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal t
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal t
local notation "input" => S.inputValue observation nontrivial half depth ordinal t
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2

noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader

theorem next_state_source : HEq (nextState observation nontrivial half depth ordinal t)
    (A.actionState observation nontrivial half depth ordinal t) :=
  state_source src here u7 calculus reader
theorem next_trace_source : HEq (nextState observation nontrivial half depth ordinal t).2
    (A.actionTrace observation nontrivial half depth ordinal t) :=
  trace_source src here u7 calculus reader
theorem next_paid : (nextState observation nontrivial half depth ordinal t).2.length=3 :=
  EndRead.paid_three src here u7 calculus input

noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus input

/-- The eta child is eliminated from the actual target's full paid trace. -/
noncomputable def etaInput := EndRead.etaInput src here u7 calculus input

theorem eta_actual : (etaInput observation nontrivial half depth ordinal t).1=
    S.embed (C.eta observation nontrivial half depth ordinal t) :=
  EndRead.eta_actual src here u7 calculus input

theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 :=
  EndRead.value_source src here u7 calculus input

noncomputable def nextQuarter : Hq :=
  burnolQuarterRestriction (nextValue observation nontrivial half depth ordinal t)
theorem next_quarter_result : nextQuarter observation nontrivial half depth ordinal t=
    S.quarterValue observation nontrivial half depth ordinal t :=
  congrArg burnolQuarterRestriction (next_value_source observation nontrivial half depth ordinal t)
theorem actual_u : nextQuarter observation nontrivial half depth ordinal t=
    (C.u observation nontrivial half depth ordinal t:Hq) :=
  (next_quarter_result observation nontrivial half depth ordinal t).trans
    (S.quarter_actual observation nontrivial half depth ordinal t)

theorem actual_full_equation : nextQuarter observation nontrivial half depth ordinal t-
    burnolTruncatedFourier (burnolTruncatedFourier (nextQuarter observation nontrivial half depth ordinal t))=
      C.forcing observation nontrivial half depth ordinal t := by
  rw [next_quarter_result]
  exact S.actual_full_equation observation nontrivial half depth ordinal t

theorem actual_existing_inverse : sourceInverse q
    (quarterChart (C.forcing observation nontrivial half depth ordinal t))=
      quarterChart (nextQuarter observation nontrivial half depth ordinal t) :=
  (S.actual_existing_inverse observation nontrivial half depth ordinal t).trans
    (congrArg quarterChart (next_quarter_result observation nontrivial half depth ordinal t).symm)

end OriginalConstantFourierResponseConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierResponseConsumer"
