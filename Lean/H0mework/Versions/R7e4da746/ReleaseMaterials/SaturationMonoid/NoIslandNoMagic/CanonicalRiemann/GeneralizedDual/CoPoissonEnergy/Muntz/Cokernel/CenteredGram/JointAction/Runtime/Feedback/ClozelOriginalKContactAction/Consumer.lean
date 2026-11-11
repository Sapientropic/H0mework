import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKContactAction.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ContactFeedback.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalContactConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open scoped InnerProductSpace
namespace A
export OriginalContactAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end A
namespace S
export OriginalContactSource (result actual_output)
end S
namespace G
export OriginalContactSource.Generated (reader result)
end G
namespace Input
export OriginalContactPriceInput (uValue vValue alphaLift betaLift gapValue)
end Input
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
open private state_source trace_source expression normalizedTrace paid from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private value_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action

namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (u v alpha beta gap:BurnolL2)
local notation "reader" => (fun _ => G.reader root.toAuthoritativeRoot c u v alpha beta gap (root.emitted visit.current))
local notation "actualValue" => Adapter.terminalValue root visit u7 calculus reader
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def tateInput := originalInput (actualTrace root visit u7 calculus c u v alpha beta gap)
noncomputable def rInput := originalInput (tateInput root visit u7 calculus c u v alpha beta gap).2.1
noncomputable def forcingInput := originalInput (rInput root visit u7 calculus c u v alpha beta gap).2.1
theorem paid_all : (Adapter.state root visit u7 calculus reader).2.length=46 :=
  (paid root visit u7 calculus reader).trans (OriginalContactProgram.code_budget c alpha beta gap)
private theorem terminal_value : actualValue=OC.value root.toAuthoritativeRoot visit.current reader := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
theorem result_value : actualValue=(G.result root.toAuthoritativeRoot visit.current c u v alpha beta gap).2.2.1 :=
  (terminal_value root visit u7 calculus c u v alpha beta gap).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c u v alpha beta gap))
theorem tate_action : burnolTateReciprocalL2 (tateInput root visit u7 calculus c u v alpha beta gap).1=actualValue :=
  (tateInput root visit u7 calculus c u v alpha beta gap).2.2.down.trans
    (terminal_value root visit u7 calculus c u v alpha beta gap).symm
theorem r_action : burnolDirectRightResolventCLM (OriginalKBFiniteCalculation.conjugateCoordinate c)
    (rInput root visit u7 calculus c u v alpha beta gap).1=(tateInput root visit u7 calculus c u v alpha beta gap).1 :=
  (rInput root visit u7 calculus c u v alpha beta gap).2.2.down
theorem forcing_tate_action : burnolTateReciprocalL2 (forcingInput root visit u7 calculus c u v alpha beta gap).1=
    (rInput root visit u7 calculus c u v alpha beta gap).1 :=
  (forcingInput root visit u7 calculus c u v alpha beta gap).2.2.down
theorem forcing_source : (forcingInput root visit u7 calculus c u v alpha beta gap).1=
    (OriginalContactProgram.forcingCode c alpha beta gap).eval (OriginalContactProgram.environment u v) :=
  (forcingInput root visit u7 calculus c u v alpha beta gap).2.1.sound.symm
end EndRead

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal t
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal t
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "u" => Input.uValue observation nontrivial half depth ordinal t
local notation "v" => Input.vValue observation nontrivial half depth ordinal t
local notation "alpha" => Input.alphaLift observation nontrivial half depth ordinal t
local notation "beta" => Input.betaLift observation nontrivial half depth ordinal t
local notation "gap" => Input.gapValue observation nontrivial half depth ordinal t
noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader
noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus c u v alpha beta gap
noncomputable def tateInput := EndRead.tateInput src here u7 calculus c u v alpha beta gap
noncomputable def rInput := EndRead.rInput src here u7 calculus c u v alpha beta gap
noncomputable def forcingInput := EndRead.forcingInput src here u7 calculus c u v alpha beta gap
theorem next_state_source : type_of% (state_source src here u7 calculus reader) := state_source src here u7 calculus reader
theorem next_trace_source : type_of% (trace_source src here u7 calculus reader) := trace_source src here u7 calculus reader
theorem next_paid : type_of% (EndRead.paid_all src here u7 calculus c u v alpha beta gap) := EndRead.paid_all src here u7 calculus c u v alpha beta gap
theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 := EndRead.result_value src here u7 calculus c u v alpha beta gap
theorem actual_tate_action : type_of% (EndRead.tate_action src here u7 calculus c u v alpha beta gap) := EndRead.tate_action src here u7 calculus c u v alpha beta gap
theorem actual_R_action : type_of% (EndRead.r_action src here u7 calculus c u v alpha beta gap) := EndRead.r_action src here u7 calculus c u v alpha beta gap
theorem actual_forcing_tate : type_of% (EndRead.forcing_tate_action src here u7 calculus c u v alpha beta gap) := EndRead.forcing_tate_action src here u7 calculus c u v alpha beta gap
theorem actual_forcing_source : type_of% (EndRead.forcing_source src here u7 calculus c u v alpha beta gap) := EndRead.forcing_source src here u7 calculus c u v alpha beta gap
theorem actual_output : nextValue observation nontrivial half depth ordinal t=
    OriginalContactFeedbackSource.generatedContactAction c :=
  (next_value_source observation nontrivial half depth ordinal t).trans (S.actual_output observation nontrivial half depth ordinal t)

/-- The cotest reads the actual new target, with the existing original paired column. -/
theorem actual_paired_fee (h:ℝ) :
    inner ℂ (OriginalPrimitiveRankBalance.pairedColumn c h) (nextValue observation nontrivial half depth ordinal t)=
      inner ℂ (OriginalPrimitiveRankBalance.pairedColumn c h) (OriginalContactFeedbackSource.generatedContactAction c) :=
  congrArg (inner ℂ (OriginalPrimitiveRankBalance.pairedColumn c h)) (actual_output observation nontrivial half depth ordinal t)
noncomputable def retainedPriceState := (OriginalContactAction.actualInputFace observation nontrivial half depth ordinal t).rootRead
theorem retained_price_state : type_of% (OriginalContactAction.target_input_state observation nontrivial half depth ordinal t) :=
  OriginalContactAction.target_input_state observation nontrivial half depth ordinal t
theorem retained_parent_state : type_of% (OriginalContactAction.target_parent_state observation nontrivial half depth ordinal t) :=
  OriginalContactAction.target_parent_state observation nontrivial half depth ordinal t
end OriginalContactConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalContactConsumer"
