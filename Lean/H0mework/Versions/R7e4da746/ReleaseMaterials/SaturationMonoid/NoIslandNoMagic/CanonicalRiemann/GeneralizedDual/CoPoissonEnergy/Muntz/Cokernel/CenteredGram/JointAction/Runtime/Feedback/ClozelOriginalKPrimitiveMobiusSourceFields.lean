import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReciprocalCotestSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPrimitiveMobiusSourceOccurrences

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPrimitiveMobiusSourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
local instance levelGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade target
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative
  (native oldStock oldEnvironment beforeStock beforeEnvironment sourceFrame sourceBase packetAdmission)
end WN
namespace AR
export SourceInventoryExecutionFeed.AdmissionReceipt (Admission)
end AR
namespace Engine
export ActualNativeRelationTransport.AS (stockScalar)
end Engine
namespace C
export OriginalKCombReceiptFeedback
  (receipt wholeDebtRPrimitiveMobiusSourceBinding wholeDebtRPrimitiveMobiusSourceCode
   wholeDebtRPrimitiveMobiusSourceTrace whole_debt_R_primitive_mobius_source_preserved)
end C
namespace Prog
export OriginalKPrimitiveMobiusSourceCalculation (Value Var code sourceEnvironment)
end Prog
namespace R
export OriginalWholeDebtRSourceReceiptConsumer (bornWordMap wordMapAt)
end R
namespace Born
export OriginalKBFiniteCalculation.BornInventory
  (packetAt sourceBornHistory actualBornHistory actual_source_relations_in_born)
end Born
namespace NW
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback (admissionWord)
end NW
namespace PT
export SourceOperationPaidRelations (words exposure paid_boundary events_trace complete_steps)
end PT
namespace SN
export SourceInventoryExecutionFeed.SourceWordNative
  (request generatedAction nextOriginFace sourceWord nextFullValue
   source_effect source_inverse same_ledger same_visit compiles whole_first canonical_next next_source_occurrences)
end SN
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "raw" => C.wholeDebtRPrimitiveMobiusSourceCode observation nontrivial depth half
local notation "trace" => C.wholeDebtRPrimitiveMobiusSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)

theorem bound_code_value (field : Fin 3) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (Prog.code c field).eval Prog.sourceEnvironment := by
  unfold C.wholeDebtRPrimitiveMobiusSourceCode
  rw [Expr.eval_subst]
  have bindingSource : (fun sort name =>
      ((C.wholeDebtRPrimitiveMobiusSourceBinding observation nontrivial depth half field) sort name).eval
        environment) = Prog.sourceEnvironment := by
    funext sort name
    change (runtimePrimitiveMobiusCalculationResultAt observation nontrivial depth half field).1.environment
      sort name = _
    rw [runtimePrimitiveMobiusCalculationResultAt_source]
    rfl
  rw [bindingSource]
  rfl

def actualValue (field : Fin 3) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 3) : actualValue observation nontrivial half depth field =
    (runtimePrimitiveMobiusCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value, runtimePrimitiveMobiusCalculationResultAt_source]
  exact (OriginalKWholeDebtRCalculationFace.mobius_result_value observation nontrivial half field
    (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence).symm

def boundary (field : Fin 3) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 3) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ)-
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)


end OriginalKPrimitiveMobiusSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
