import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Trace.Add
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativePortSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleySourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKPaNativeCayleySourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleySourceWriteback
open Complex BurnolPhysicalState RootInquiryCompletion
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
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
  (receipt paNativeCayleySourceBinding paNativeCayleySourceCode
   paNativeCayleySourceTrace pa_native_cayley_source_preserved)
end C
namespace Prog
export OriginalKCombReceiptFeedback (Value Var)
end Prog
namespace JP
export OriginalKPaNativeCayleySourceCalculation (code paAction qAction)
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
local notation "raw" => C.paNativeCayleySourceCode observation nontrivial depth half
local notation "trace" => C.paNativeCayleySourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)
private abbrev emittedAt := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private abbrev environmentAt (field : Fin 3) :=
  (runtimePaNativeCayleyCalculationResultAt observation nontrivial depth half field).1.environment
local notation "occurrence" => emittedAt observation nontrivial depth
local notation "nativeEnv" => environmentAt observation nontrivial half depth

theorem bound_code_value (field : Fin 3) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (JP.code c field).eval (nativeEnv field) := by
  unfold C.paNativeCayleySourceCode
  rw [Expr.eval_subst]
  rfl

def actualValue (field : Fin 3) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 3) : actualValue observation nontrivial half depth field =
    (runtimePaNativeCayleyCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value]
  fin_cases field
  · exact (OriginalKWholeDebtRCalculationFace.pa_native_cayley_result_value observation nontrivial half 0 occurrence).symm
  · exact (OriginalKWholeDebtRCalculationFace.pa_native_cayley_result_value observation nontrivial half 1 occurrence).symm
  · exact (OriginalKWholeDebtRCalculationFace.pa_native_cayley_result_value observation nontrivial half 2 occurrence).symm

def rawPaCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (1 : Fin 2) : OriginalKPaNativeCayleySourceCalculation.E).subst
    (C.paNativeCayleySourceBinding observation nontrivial depth half 0)

def rawRCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (0 : Fin 2) : OriginalKPaNativeCayleySourceCalculation.E).subst
    (C.paNativeCayleySourceBinding observation nontrivial depth half 0)

def scaledRCode : Expr Prog.Value Prog.Var () :=
  .linear (((sourceDamping c : ℂ) • ContinuousLinearMap.id ℂ BurnolL2).toLinearMap.toAddMonoidHom)
    (rawRCode observation nontrivial half depth)

def actualRawTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (.add (rawPaCode observation nontrivial half depth)
      (scaledRCode observation nontrivial half depth))
    (.const (actualValue observation nontrivial half depth 0)) := trace 0

/-- The first U execution supplies both original children with their actual interleaving. -/
def actualRawInputs := Trace.splitAdd (actualRawTrace observation nontrivial half depth)

def actualScaledRInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (rawRCode observation nontrivial half depth) (.const point) ×
      PLift ((sourceDamping c : ℂ) • point =
        (actualRawInputs observation nontrivial half depth).rightValue) := by
  exact SourceOperationExecution.originalInput
    (actualRawInputs observation nontrivial half depth).rightTrace

theorem actual_source_R_binding : (actualScaledRInput observation nontrivial half depth).1 =
    (runtimePaNativePortCalculationResultAt observation nontrivial depth half 0).2.2.1 := by
  exact (actualScaledRInput observation nontrivial half depth).2.1.sound.symm

theorem actual_source_Pa_binding :
    (actualRawInputs observation nontrivial half depth).leftValue =
      (runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1 := by
  exact (actualRawInputs observation nontrivial half depth).leftTrace.sound.symm

theorem actual_raw_equation : actualValue observation nontrivial half depth 0 =
    (runtimeReturnJetCalculationResultAt observation nontrivial depth half 0).2.2.1 +
      (sourceDamping c : ℂ) •
        (runtimePaNativePortCalculationResultAt observation nontrivial depth half 0).2.2.1 := by
  calc
    _ = (actualRawInputs observation nontrivial half depth).leftValue +
        (actualRawInputs observation nontrivial half depth).rightValue :=
      (actualRawInputs observation nontrivial half depth).total_eq
    _ = _ := by
      rw [actual_source_Pa_binding, ← (actualScaledRInput observation nontrivial half depth).2.2.down,
        actual_source_R_binding]

def paInputCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (0 : Fin 2) : OriginalKPaNativeCayleySourceCalculation.E).subst
    (C.paNativeCayleySourceBinding observation nontrivial depth half 1)

def qInputCode : Expr Prog.Value Prog.Var () :=
  (Expr.var (0 : Fin 2) : OriginalKPaNativeCayleySourceCalculation.E).subst
    (C.paNativeCayleySourceBinding observation nontrivial depth half 2)

def actualPaInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (paInputCode observation nontrivial half depth) (.const point) ×
      PLift (JP.paAction point = actualValue observation nontrivial half depth 1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear JP.paAction.toLinearMap.toAddMonoidHom
        (paInputCode observation nontrivial half depth))
      (.const (actualValue observation nontrivial half depth 1)) := trace 1
  exact SourceOperationExecution.originalInput executed

def actualQInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (qInputCode observation nontrivial half depth) (.const point) ×
      PLift (JP.qAction point = actualValue observation nontrivial half depth 2) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear JP.qAction.toLinearMap.toAddMonoidHom
        (qInputCode observation nontrivial half depth))
      (.const (actualValue observation nontrivial half depth 2)) := trace 2
  exact SourceOperationExecution.originalInput executed

theorem actual_pa_input_binding : (actualPaInput observation nontrivial half depth).1 =
    actualValue observation nontrivial half depth 0 := by
  calc
    _ = (runtimePaNativeCayleyCalculationResultAt observation nontrivial depth half 0).2.2.1 :=
      (actualPaInput observation nontrivial half depth).2.1.sound.symm
    _ = _ := (actual_value_runtime observation nontrivial half depth 0).symm

theorem actual_Q_input_binding : (actualQInput observation nontrivial half depth).1 =
    actualValue observation nontrivial half depth 0 := by
  calc
    _ = (runtimePaNativeCayleyCalculationResultAt observation nontrivial depth half 0).2.2.1 :=
      (actualQInput observation nontrivial half depth).2.1.sound.symm
    _ = _ := (actual_value_runtime observation nontrivial half depth 0).symm

theorem actual_pa_equation : actualValue observation nontrivial half depth 1 =
    JP.paAction (actualValue observation nontrivial half depth 0) := by
  rw [← (actualPaInput observation nontrivial half depth).2.2.down, actual_pa_input_binding]

theorem actual_Q_equation : actualValue observation nontrivial half depth 2 =
    JP.qAction (actualValue observation nontrivial half depth 0) := by
  rw [← (actualQInput observation nontrivial half depth).2.2.down, actual_Q_input_binding]

def boundary (field : Fin 3) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 3) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ) -
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)

end OriginalKPaNativeCayleySourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
