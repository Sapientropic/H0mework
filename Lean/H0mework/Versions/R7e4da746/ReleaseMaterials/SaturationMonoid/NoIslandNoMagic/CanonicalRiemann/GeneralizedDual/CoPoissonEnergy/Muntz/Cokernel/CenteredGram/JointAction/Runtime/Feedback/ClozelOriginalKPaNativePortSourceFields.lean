import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReturnJetStepSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativePortSourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativePortSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativePortSourceWriteback
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
  (receipt paNativePortSourceBinding paNativePortSourceCode
   paNativePortSourceTrace pa_native_port_source_preserved)
end C
namespace Prog
export OriginalKCombReceiptFeedback (Value Var)
end Prog
namespace JP
export OriginalKPaNativePortSourceCalculation (code unitAction)
end JP
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
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "raw" => C.paNativePortSourceCode observation nontrivial depth half
local notation "trace" => C.paNativePortSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)
private abbrev emittedAt := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private abbrev environmentAt (field : Fin 2) :=
  (runtimePaNativePortCalculationResultAt observation nontrivial depth half field).1.environment
local notation "occurrence" => emittedAt observation nontrivial depth
local notation "nativeEnv" => environmentAt observation nontrivial half depth

theorem bound_code_value (field : Fin 2) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (JP.code c field).eval (nativeEnv field) := by
  unfold C.paNativePortSourceCode
  rw [Expr.eval_subst]
  rfl

def actualValue (field : Fin 2) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 2) : actualValue observation nontrivial half depth field =
    (runtimePaNativePortCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value]
  fin_cases field
  · exact (OriginalKWholeDebtRCalculationFace.pa_native_port_result_value observation nontrivial half 0 occurrence).symm
  · exact (OriginalKWholeDebtRCalculationFace.pa_native_port_result_value observation nontrivial half 1 occurrence).symm

def rInputCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (0 : Fin 2) : OriginalKPaNativePortSourceCalculation.E).subst
    (C.paNativePortSourceBinding observation nontrivial depth half 0)

def correctionRCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (0 : Fin 2) : OriginalKPaNativePortSourceCalculation.E).subst
    (C.paNativePortSourceBinding observation nontrivial depth half 1)

def correctionPaCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (1 : Fin 2) : OriginalKPaNativePortSourceCalculation.E).subst
    (C.paNativePortSourceBinding observation nontrivial depth half 1)

def negativeUnitCode : Expr Prog.Value Prog.Var () :=
  .linear (-JP.unitAction c).toLinearMap.toAddMonoidHom
    (correctionPaCode observation nontrivial half depth)

def actualRInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (rInputCode observation nontrivial half depth) (.const point) ×
      PLift (burnolDirectRightResolventCLM c point = actualValue observation nontrivial half depth 0) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (rInputCode observation nontrivial half depth))
      (.const (actualValue observation nontrivial half depth 0)) := trace 0
  exact SourceOperationExecution.originalInput executed

theorem actualR_input_binding : (actualRInput observation nontrivial half depth).1 =
    (runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1 := by
  exact (actualRInput observation nontrivial half depth).2.1.sound.symm

def actualCorrectionTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (.add (correctionRCode observation nontrivial half depth)
      (negativeUnitCode observation nontrivial half depth))
    (.const (actualValue observation nontrivial half depth 1)) := trace 1

/-- The original add history itself supplies both children and their exact interleaving. -/
def actualCorrectionInputs := Trace.splitAdd (actualCorrectionTrace observation nontrivial half depth)

def actualUnitInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (correctionPaCode observation nontrivial half depth) (.const point) ×
      PLift ((-JP.unitAction c) point =
        (actualCorrectionInputs observation nontrivial half depth).rightValue) := by
  exact SourceOperationExecution.originalInput
    (actualCorrectionInputs observation nontrivial half depth).rightTrace

theorem actual_correction_R_binding :
    (actualCorrectionInputs observation nontrivial half depth).leftValue =
      actualValue observation nontrivial half depth 0 := by
  calc
    _ = (runtimePaNativePortCalculationResultAt observation nontrivial depth half 0).2.2.1 :=
      (actualCorrectionInputs observation nontrivial half depth).leftTrace.sound.symm
    _ = _ := (actual_value_runtime observation nontrivial half depth 0).symm

theorem actual_unit_input_binding : (actualUnitInput observation nontrivial half depth).1 =
    (runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1 := by
  exact (actualUnitInput observation nontrivial half depth).2.1.sound.symm

theorem actual_correction_equation : actualValue observation nontrivial half depth 1 =
    actualValue observation nontrivial half depth 0 - JP.unitAction c
      ((runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1) := by
  calc
    _ = (actualCorrectionInputs observation nontrivial half depth).leftValue +
        (actualCorrectionInputs observation nontrivial half depth).rightValue :=
      (actualCorrectionInputs observation nontrivial half depth).total_eq
    _ = actualValue observation nontrivial half depth 0 +
        (-JP.unitAction c) (actualUnitInput observation nontrivial half depth).1 := by
      rw [actual_correction_R_binding, (actualUnitInput observation nontrivial half depth).2.2.down]
    _ = _ := by rw [neg_apply, actual_unit_input_binding, sub_eq_add_neg]

def boundary (field : Fin 2) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 2) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ) -
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)

end OriginalKPaNativePortSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
