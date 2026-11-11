import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierFullResponse.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierFullResponseConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace A
export OriginalConstantFourierFullResponseAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end A
namespace S
export OriginalConstantFourierFullResponseSource
  (result inputU inputEta meanScalar meanChannel wave constant forcingWord fullInverse
   actual_forcing mu_scalar_actual nu_scalar_actual actual_return)
end S
namespace Prior
export OriginalConstantFourierResponseConsumer (nextValue)
end Prior
namespace Native
export OriginalConstantFourierNativeConsumer (mu nu forcing)
end Native
namespace G
export OriginalConstantFourierFullResponseSource.Generated
  (reader result inverseInput forcing_equation mu_binding v_equation rawMu rawNu)
end G
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
variable (u7:U7ProducerCalculus W) (calculus:U7ObstructionEvolutionCalculus W u7) (u eta:BurnolL2)
local notation "reader" => (fun _ => G.reader root.toAuthoritativeRoot u eta (root.emitted visit.current))
local notation "actualValue" => Adapter.terminalValue root visit u7 calculus reader
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def forcingInput := originalInput (actualTrace root visit u7 calculus u eta)
noncomputable def forcingSplit := Trace.splitAdd (forcingInput root visit u7 calculus u eta).2.1
noncomputable def leftSplit := Trace.splitAdd (forcingSplit root visit u7 calculus u eta).leftTrace
noncomputable def nuLift := originalInput (leftSplit root visit u7 calculus u eta).rightTrace
noncomputable def nuInput := originalInput (nuLift root visit u7 calculus u eta).2.1
noncomputable def rightNegInput := originalInput (forcingSplit root visit u7 calculus u eta).rightTrace
noncomputable def muLift := originalInput (rightNegInput root visit u7 calculus u eta).2.1
noncomputable def muInput := originalInput (muLift root visit u7 calculus u eta).2.1
noncomputable def rawMu : ℂ := S.meanScalar (muInput root visit u7 calculus u eta).1
noncomputable def rawNu : ℂ := S.meanScalar (nuInput root visit u7 calculus u eta).1

theorem paid_twelve : (Adapter.state root visit u7 calculus reader).2.length=12 :=
  paid root visit u7 calculus reader
private theorem terminal_value : actualValue=OC.value root.toAuthoritativeRoot visit.current reader := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
theorem result_value : actualValue=(G.result root.toAuthoritativeRoot visit.current u eta).2.2.1 :=
  (terminal_value root visit u7 calculus u eta).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot u eta))
theorem forcing_source : (forcingInput root visit u7 calculus u eta).1=
    (G.inverseInput root.toAuthoritativeRoot visit.current u eta).1 := by
  have actual : (forcingInput root visit u7 calculus u eta).1=S.forcingWord u eta :=
    (forcingInput root visit u7 calculus u eta).2.1.sound.symm
  exact actual.trans (G.forcing_equation root.toAuthoritativeRoot visit.current u eta).symm
theorem mu_source : rawMu root visit u7 calculus u eta=G.rawMu root.toAuthoritativeRoot visit.current u eta := by
  have actual : (muInput root visit u7 calculus u eta).1=u :=
    (muInput root visit u7 calculus u eta).2.1.sound.symm
  exact congrArg S.meanScalar (actual.trans (G.mu_binding root.toAuthoritativeRoot visit.current u eta).symm)
theorem nu_source : rawNu root visit u7 calculus u eta=G.rawNu root.toAuthoritativeRoot visit.current u eta := by
  have actual : (nuInput root visit u7 calculus u eta).1=S.wave u :=
    (nuInput root visit u7 calculus u eta).2.1.sound.symm
  exact congrArg S.meanScalar (actual.trans (G.v_equation root.toAuthoritativeRoot visit.current u eta).symm)
theorem nu_lift : (nuLift root visit u7 calculus u eta).1=rawNu root visit u7 calculus u eta • S.constant :=
  (nuInput root visit u7 calculus u eta).2.2.down.symm
theorem mu_lift : (muLift root visit u7 calculus u eta).1=rawMu root visit u7 calculus u eta • S.constant :=
  (muInput root visit u7 calculus u eta).2.2.down.symm
theorem inverse_action : S.fullInverse (forcingInput root visit u7 calculus u eta).1=actualValue :=
  (forcingInput root visit u7 calculus u eta).2.2.down.trans (terminal_value root visit u7 calculus u eta).symm
end EndRead

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ)
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal t
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal t
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal t
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal t
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal t
local notation "u" => S.inputU observation nontrivial half depth ordinal t
local notation "eta" => S.inputEta observation nontrivial half depth ordinal t

noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader
noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus u eta
noncomputable def forcingInput := EndRead.forcingInput src here u7 calculus u eta
noncomputable def muInput := EndRead.muInput src here u7 calculus u eta
noncomputable def nuInput := EndRead.nuInput src here u7 calculus u eta
noncomputable def muLift := EndRead.muLift src here u7 calculus u eta
noncomputable def nuLift := EndRead.nuLift src here u7 calculus u eta
noncomputable def rawMu := EndRead.rawMu src here u7 calculus u eta
noncomputable def rawNu := EndRead.rawNu src here u7 calculus u eta

theorem next_state_source : type_of% (state_source src here u7 calculus reader) :=
  state_source src here u7 calculus reader
theorem next_trace_source : type_of% (trace_source src here u7 calculus reader) :=
  trace_source src here u7 calculus reader
theorem next_paid : type_of% (EndRead.paid_twelve src here u7 calculus u eta) :=
  EndRead.paid_twelve src here u7 calculus u eta
theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 :=
  EndRead.result_value src here u7 calculus u eta
theorem mu_lift : type_of% (EndRead.mu_lift src here u7 calculus u eta) :=
  EndRead.mu_lift src here u7 calculus u eta
theorem nu_lift : type_of% (EndRead.nu_lift src here u7 calculus u eta) :=
  EndRead.nu_lift src here u7 calculus u eta

theorem actual_mu : rawMu observation nontrivial half depth ordinal t=Native.mu observation nontrivial half depth ordinal t :=
  (EndRead.mu_source src here u7 calculus u eta).trans (S.mu_scalar_actual observation nontrivial half depth ordinal t)
theorem actual_nu : rawNu observation nontrivial half depth ordinal t=Native.nu observation nontrivial half depth ordinal t :=
  (EndRead.nu_source src here u7 calculus u eta).trans (S.nu_scalar_actual observation nontrivial half depth ordinal t)
theorem actual_forcing : (forcingInput observation nontrivial half depth ordinal t).1=
    burnolQuarterZeroExtension (Native.forcing observation nontrivial half depth ordinal t) :=
  (EndRead.forcing_source src here u7 calculus u eta).trans (S.actual_forcing observation nontrivial half depth ordinal t)
theorem actual_inverse_action : type_of% (EndRead.inverse_action src here u7 calculus u eta) :=
  EndRead.inverse_action src here u7 calculus u eta
theorem actual_return : nextValue observation nontrivial half depth ordinal t=
    Prior.nextValue observation nontrivial half depth ordinal t :=
  (next_value_source observation nontrivial half depth ordinal t).trans (S.actual_return observation nontrivial half depth ordinal t)

end OriginalConstantFourierFullResponseConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierFullResponseConsumer"
