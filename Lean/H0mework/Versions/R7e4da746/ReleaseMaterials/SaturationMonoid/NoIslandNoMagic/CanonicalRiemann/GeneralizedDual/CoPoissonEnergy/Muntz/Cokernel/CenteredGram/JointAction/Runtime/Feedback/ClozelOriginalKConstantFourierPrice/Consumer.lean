import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Action

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceConsumer
open RootInquiryCompletion BurnolPhysicalState SourceOperationEffects SourceOperationExecution
namespace A
export OriginalConstantFourierPriceAction (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader)
end A
namespace S
export OriginalConstantFourierPriceSource (seedValue bValue sbValue result actual_output code_budget)
end S
namespace P
export OriginalConstantFourierPriceProgram (priceLift driveCode)
end P
namespace M
export OriginalConstantFourierPriceMath (scalarRead scalarLift scalar_lift inverse wave)
end M
namespace G
export OriginalConstantFourierPriceSource.Generated (reader result)
end G
namespace T
export OriginalConstantFourierPriceSource.Traced
  (priceInput inverseInput firstDrive secondDrive firstTrace secondTrace inverse_equation price_equation full_input_equation)
end T
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
variable (c:BurnolCompletedMellinCoordinate) (seed b sb:BurnolL2)
local notation "reader" => (fun _ => G.reader root.toAuthoritativeRoot c seed b sb (root.emitted visit.current))
local notation "actualValue" => Adapter.terminalValue root visit u7 calculus reader
noncomputable def actualTrace := normalizedTrace root visit u7 calculus reader
noncomputable def priceInput := T.priceInput c b sb (actualTrace root visit u7 calculus c seed b sb)
noncomputable def inverseInput := T.inverseInput c b sb (actualTrace root visit u7 calculus c seed b sb)
noncomputable def firstDrive := T.firstDrive c b sb (actualTrace root visit u7 calculus c seed b sb)
noncomputable def secondDrive := T.secondDrive c b sb (actualTrace root visit u7 calculus c seed b sb)
noncomputable def firstTrace := T.firstTrace c b sb (actualTrace root visit u7 calculus c seed b sb)
noncomputable def secondTrace := T.secondTrace c b sb (actualTrace root visit u7 calculus c seed b sb)

theorem paid_all : (Adapter.state root visit u7 calculus reader).2.length=269 :=
  (paid root visit u7 calculus reader).trans (S.code_budget c b sb)
private theorem terminal_value : actualValue=OC.value root.toAuthoritativeRoot visit.current reader := by
  unfold Adapter.terminalValue
  rw [expression root visit u7 calculus reader]
  rfl
theorem result_value : actualValue=(G.result root.toAuthoritativeRoot visit.current c seed b sb).2.2.1 :=
  (terminal_value root visit u7 calculus c seed b sb).trans
    (value_source root.toAuthoritativeRoot visit.current (G.reader root.toAuthoritativeRoot c seed b sb))
theorem inverse_action : type_of% (T.inverse_equation c b sb (actualTrace root visit u7 calculus c seed b sb)).symm :=
  (T.inverse_equation c b sb (actualTrace root visit u7 calculus c seed b sb)).symm
theorem price_action : P.priceLift c (priceInput root visit u7 calculus c seed b sb).1=actualValue :=
  (T.price_equation c b sb (actualTrace root visit u7 calculus c seed b sb)).symm.trans
    (terminal_value root visit u7 calculus c seed b sb).symm
theorem full_input_equation : type_of% (T.full_input_equation c b sb (actualTrace root visit u7 calculus c seed b sb)) :=
  T.full_input_equation c b sb (actualTrace root visit u7 calculus c seed b sb)
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
local notation "seed" => S.seedValue observation nontrivial half depth ordinal t
local notation "b" => S.bValue observation nontrivial half depth ordinal t
local notation "sb" => S.sbValue observation nontrivial half depth ordinal t

noncomputable def nextFace := Adapter.targetFace src here u7 calculus reader
noncomputable def nextState := Adapter.state src here u7 calculus reader
noncomputable def nextValue := Adapter.terminalValue src here u7 calculus reader
noncomputable def nextTrace := EndRead.actualTrace src here u7 calculus c seed b sb
noncomputable def priceInput := EndRead.priceInput src here u7 calculus c seed b sb
noncomputable def inverseInput := EndRead.inverseInput src here u7 calculus c seed b sb
noncomputable def firstDrive := EndRead.firstDrive src here u7 calculus c seed b sb
noncomputable def secondDrive := EndRead.secondDrive src here u7 calculus c seed b sb
noncomputable def firstTrace := EndRead.firstTrace src here u7 calculus c seed b sb
noncomputable def secondTrace := EndRead.secondTrace src here u7 calculus c seed b sb

theorem next_state_source : type_of% (state_source src here u7 calculus reader) :=
  state_source src here u7 calculus reader
theorem next_trace_source : type_of% (trace_source src here u7 calculus reader) :=
  trace_source src here u7 calculus reader
theorem next_paid : type_of% (EndRead.paid_all src here u7 calculus c seed b sb) :=
  EndRead.paid_all src here u7 calculus c seed b sb
theorem next_value_source : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 :=
  EndRead.result_value src here u7 calculus c seed b sb
theorem actual_inverse_action : type_of% (EndRead.inverse_action src here u7 calculus c seed b sb) :=
  EndRead.inverse_action src here u7 calculus c seed b sb
theorem actual_price_action : type_of% (EndRead.price_action src here u7 calculus c seed b sb) :=
  EndRead.price_action src here u7 calculus c seed b sb
theorem actual_full_input : type_of% (EndRead.full_input_equation src here u7 calculus c seed b sb) :=
  EndRead.full_input_equation src here u7 calculus c seed b sb

theorem actual_lift : nextValue observation nontrivial half depth ordinal t=
    M.scalarLift (OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c) :=
  (next_value_source observation nontrivial half depth ordinal t).trans (S.actual_output observation nontrivial half depth ordinal t)
noncomputable def actualPrice : ℂ := M.scalarRead (nextValue observation nontrivial half depth ordinal t)
theorem actual_price : actualPrice observation nontrivial half depth ordinal t=
    OriginalWholeDebtRJointMobiusContactClosureSource.finitePrice c c :=
  (congrArg M.scalarRead (actual_lift observation nontrivial half depth ordinal t)).trans (M.scalar_lift _)

end OriginalConstantFourierPriceConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceConsumer"
