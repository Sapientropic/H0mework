import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalCFixedAdjoint.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCFixedAdjointConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace A
export OriginalCFixedAdjointAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end A
namespace S
export OriginalCFixedAdjointSource (correctionValue result actual_output code_budget operation)
end S
namespace G
export OriginalCFixedAdjointSource.Generated (reader result)
end G
namespace Root
export OriginalCFixedAdjointOrigin (correctionTrace correction_trace_source correction_actual)
end Root
namespace C
export OriginalKCombReceiptFeedback (receipt)
end C
namespace Child
export OriginalKOutsideCorrectionChildSource (childCode originalChild)
end Child
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value)
end OC
namespace Energy
export OriginalKCrossParameterRAdjointSource.CayleyEnergySource
  (sourceCayley sourceDamping sourceDamping_pos sourceCayley_apply)
end Energy
open private state_source trace_source expression normalizedTrace paid from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource
open private value_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

namespace EndRead
variable {W:WorldRelationNetwork} {V:Vocabulary}
variable (root:SourceNativeLivingRootClosure W V)
variable (visit:SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7)
variable (c:BurnolCompletedMellinCoordinate) (actualC:BurnolL2)
local notation "reader" => (fun _ => G.reader root.toAuthoritativeRoot c actualC (root.emitted visit.current))
local notation "actualValue" => Adapter.terminalValue root visit u7 calculus reader
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def input := originalInput (actualTrace root visit u7 calculus c actualC)
theorem input_binding : (input root visit u7 calculus c actualC).1=actualC :=
  (input root visit u7 calculus c actualC).2.1.sound.symm
theorem paid_all : (Adapter.state root visit u7 calculus reader).2.length=2 :=
  (paid root visit u7 calculus reader).trans (S.code_budget c)
private theorem terminal_value : actualValue=OC.value root.toAuthoritativeRoot visit.current reader := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
theorem result_value : actualValue=(G.result root.toAuthoritativeRoot visit.current c actualC).2.2.1 :=
  (terminal_value root visit u7 calculus c actualC).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c actualC))
theorem action : S.operation c (input root visit u7 calculus c actualC).1=actualValue :=
  (input root visit u7 calculus c actualC).2.2.down.trans
    (terminal_value root visit u7 calculus c actualC).symm
/-- A dependent resolvent readout of the same adjoint action, with no extra Step. -/
theorem rstar_effect : (Energy.sourceDamping c:ℂ)⁻¹ •
    (actualValue-(input root visit u7 calculus c actualC).1)=
      (burnolDirectRightResolventCLM c).adjoint (input root visit u7 calculus c actualC).1 := by
  have generated : S.operation c (input root visit u7 calculus c actualC).1=
      (input root visit u7 calculus c actualC).1+(Energy.sourceDamping c:ℂ) •
        (burnolDirectRightResolventCLM c).adjoint (input root visit u7 calculus c actualC).1 := by
    apply ext_inner_right ℂ
    intro y
    change inner ℂ ((Energy.sourceCayley c).adjoint _) y=inner ℂ (_+(Energy.sourceDamping c:ℂ) •
      (burnolDirectRightResolventCLM c).adjoint _) y
    rw [ContinuousLinearMap.adjoint_inner_left,Energy.sourceCayley_apply,inner_add_right,inner_smul_right,
      inner_add_left,inner_smul_left,ContinuousLinearMap.adjoint_inner_left,Complex.conj_ofReal]
    rfl
  have nonzero : (Energy.sourceDamping c:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Energy.sourceDamping_pos c))
  rw [← action root visit u7 calculus c actualC,generated,add_sub_cancel_left,
    smul_smul,inv_mul_cancel₀ nonzero,one_smul]
end EndRead

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal t
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal t
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "actualC" => S.correctionValue observation nontrivial half depth ordinal t
noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader
noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus c actualC
noncomputable def input := EndRead.input src here u7 calculus c actualC
theorem next_state_source : type_of% (state_source src here u7 calculus reader) :=
  state_source src here u7 calculus reader
theorem next_trace_source : type_of% (trace_source src here u7 calculus reader) :=
  trace_source src here u7 calculus reader
theorem next_paid : type_of% (EndRead.paid_all src here u7 calculus c actualC) :=
  EndRead.paid_all src here u7 calculus c actualC
theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 :=
  EndRead.result_value src here u7 calculus c actualC
theorem input_binding : type_of% (EndRead.input_binding src here u7 calculus c actualC) :=
  EndRead.input_binding src here u7 calculus c actualC
theorem actual_rstar_effect : type_of% (EndRead.rstar_effect src here u7 calculus c actualC) :=
  EndRead.rstar_effect src here u7 calculus c actualC
theorem actual_action : type_of% (EndRead.action src here u7 calculus c actualC) :=
  EndRead.action src here u7 calculus c actualC

/-- The target's actual variable child carries the complete original C child receipt. -/
noncomputable def inputCorrectionTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1)
    (.const ((input observation nontrivial half depth ordinal t).1)) :=
  Eq.mp (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
    (Child.childCode observation nontrivial half depth 1) (.const point))
      (input_binding observation nontrivial half depth ordinal t).symm)
    (Root.correctionTrace observation nontrivial half depth ordinal t)
theorem input_trace_source : type_of% ((mp_heq
    (congrArg (fun point => Trace (C.receipt observation nontrivial depth half).1.environment
      (Child.childCode observation nontrivial half depth 1) (.const point))
        (input_binding observation nontrivial half depth ordinal t).symm)
      (Root.correctionTrace observation nontrivial half depth ordinal t)).trans
        (Root.correction_trace_source observation nontrivial half depth ordinal t)) :=
  (mp_heq _ _).trans (Root.correction_trace_source observation nontrivial half depth ordinal t)
theorem input_actual : (input observation nontrivial half depth ordinal t).1=
    OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c :=
  (input_binding observation nontrivial half depth ordinal t).trans
    (Root.correction_actual observation nontrivial half depth ordinal t)
theorem actual_output : nextValue observation nontrivial half depth ordinal t=
    S.operation c (OriginalKPairedBEulerJunctionSource.BandFullStockEuler.correctionRaw c) :=
  (next_value_source observation nontrivial half depth ordinal t).trans
    (S.actual_output observation nontrivial half depth ordinal t)

end OriginalCFixedAdjointConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalCFixedAdjointConsumer"
