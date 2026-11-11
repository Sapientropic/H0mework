import H0mework.Realization.Operations.Execution.LinearInput
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKJointMobiusSourceWriteback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKReturnJordanSourceOccurrences

import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceCalculation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKReturnJordanSourceWriteback
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
  (receipt returnJordanSourceBinding returnJordanSourceCode returnJordanJetCode returnJordanPrefixCode
   returnJordanSourceTrace return_jordan_source_preserved)
end C
namespace Prog
export OriginalKCombReceiptFeedback (Value Var)
end Prog
namespace JP
export OriginalKReturnJordanSourceCalculation (code paAction jetCode prefixCode)
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
local notation "raw" => C.returnJordanSourceCode observation nontrivial depth half
local notation "trace" => C.returnJordanSourceTrace observation nontrivial depth half
local notation "native" => WN.native observation nontrivial half depth ordinal
local notation "factory" => D.factory observation nontrivial half
local notation "frame" => WN.sourceFrame factory native
local notation "base" => WN.sourceBase factory native
local notation "before" => WN.beforeStock native
local notation "oldEnv" => WN.beforeEnvironment native
local notation "packet" => Born.packetAt observation nontrivial half depth (ordinal+1)
private abbrev emittedAt := (runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence
private abbrev environmentAt (field : Fin 2) :=
  (runtimeReturnJordanCalculationResultAt observation nontrivial depth half field).1.environment
local notation "occurrence" => emittedAt observation nontrivial depth
local notation "nativeEnv" => environmentAt observation nontrivial half depth

theorem bound_code_value (field : Fin 2) (environment : Env Prog.Value Prog.Var) :
    (raw field).eval environment = (JP.code c m field).eval (nativeEnv field) := by
  unfold C.returnJordanSourceCode
  rw [Expr.eval_subst]
  rfl

def actualValue (field : Fin 2) : BurnolL2 :=
  (raw field).eval (C.receipt observation nontrivial depth half).1.environment

theorem actual_value_runtime (field : Fin 2) : actualValue observation nontrivial half depth field =
    (runtimeReturnJordanCalculationResultAt observation nontrivial depth half field).2.2.1 := by
  rw [actualValue, bound_code_value]
  fin_cases field
  · exact (OriginalKWholeDebtRCalculationFace.return_jordan_result_value observation nontrivial half 0 occurrence).symm
  · exact (OriginalKWholeDebtRCalculationFace.return_jordan_result_value observation nontrivial half 1 occurrence).symm

/-- Both values are restrictions of the old R execution retained in the literal prefix bundle. -/
def borrowedResponseInput := OriginalKWholeDebtRCalculationFace.jointRResponseInput
  observation nontrivial half occurrence

def borrowedRResult : BurnolL2 :=
  (runtimeJointMobiusRCalculationResultAt observation nontrivial depth half).2.2.1

theorem actual_borrowed_response : nativeEnv 0 () 0 =
    (borrowedResponseInput observation nontrivial half depth).1 := rfl

set_option maxHeartbeats 120000 in
theorem actual_borrowed_result : nativeEnv 0 () 1 = borrowedRResult observation nontrivial half depth := by
  have sourceRaw := congrArg Prod.fst
    (runtimeReturnJordanCalculationResultAt_source observation nontrivial depth half 0)
  have carrier : nativeEnv 0 =
      OriginalKWholeDebtRCalculationFace.returnEnvironment observation nontrivial half occurrence :=
    congrArg (fun source : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
      (Value := OriginalKReturnJordanSourceCalculation.Value)
      (Var := OriginalKReturnJordanSourceCalculation.Var) (sort := ()) => source.environment) sourceRaw
  have bound :
      OriginalKWholeDebtRCalculationFace.returnEnvironment observation nontrivial half occurrence () 1 =
        (OriginalKWholeDebtRCalculationFace.jointResult observation nontrivial half 1 occurrence).2.2.1 := rfl
  have generated := (congrFun (congrFun carrier ()) 1).trans bound
  have oldState := congrArg Prod.snd
    (runtimeJointMobiusRCalculationResultAt_source observation nontrivial depth half)
  have oldValue := congrArg Prod.snd oldState
  have previous : borrowedRResult observation nontrivial half depth =
      (OriginalKWholeDebtRCalculationFace.jointResult observation nontrivial half 1 occurrence).2.2.1 :=
    congrArg Prod.fst oldValue
  exact generated.trans previous.symm

theorem borrowed_response_value : (borrowedResponseInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusUnitSource.response c :=
  (borrowedResponseInput observation nontrivial half depth).2.1.sound.symm.trans
    (OriginalKJointMobiusRSourceCalculation.actual_response_code c)

theorem borrowed_result_value : borrowedRResult observation nontrivial half depth =
    OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half := by
  rw [borrowedRResult, runtimeJointMobiusRCalculationResultAt_source]
  exact (OriginalKWholeDebtRCalculationFace.joint_result_value observation nontrivial half 1 occurrence).trans
    (OriginalKJointMobiusRSourceCalculation.actual_code_field observation nontrivial half)

def actualPaInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.returnJordanJetCode observation nontrivial depth half) (.const point) ×
      PLift (JP.paAction point = actualValue observation nontrivial half depth 0) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear JP.paAction.toLinearMap.toAddMonoidHom
        (C.returnJordanJetCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 0)) := trace 0
  exact SourceOperationExecution.originalInput executed

def actualPrefixInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        (C.returnJordanPrefixCode observation nontrivial depth half) (.const point) ×
      PLift (burnolDirectRightResolventCLM c point = actualValue observation nontrivial half depth 1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (burnolDirectRightResolventCLM c).toLinearMap.toAddMonoidHom
        (C.returnJordanPrefixCode observation nontrivial depth half))
      (.const (actualValue observation nontrivial half depth 1)) := trace 1
  exact SourceOperationExecution.originalInput executed

theorem actual_pa_input_value : (actualPaInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half m := by
  have value := (actualPaInput observation nontrivial half depth).2.1.sound.symm
  change (actualPaInput observation nontrivial half depth).1 =
    (C.returnJordanJetCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.returnJordanJetCode at value
  rw [Expr.eval_subst] at value
  exact value.trans (OriginalKReturnJordanSourceCalculation.actual_jet_code observation nontrivial half
    (nativeEnv 0)
    ((actual_borrowed_response observation nontrivial half depth).trans
      (borrowed_response_value observation nontrivial half depth))
    ((actual_borrowed_result observation nontrivial half depth).trans
      (borrowed_result_value observation nontrivial half depth)) m)

theorem actual_pa_value : actualValue observation nontrivial half depth 0 =
    (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  rw [actualValue, bound_code_value]
  exact OriginalKReturnJordanSourceCalculation.actual_pa_code observation nontrivial half (nativeEnv 0)
    ((actual_borrowed_response observation nontrivial half depth).trans
      (borrowed_response_value observation nontrivial half depth))
    ((actual_borrowed_result observation nontrivial half depth).trans
      (borrowed_result_value observation nontrivial half depth))

theorem actual_prefix_pa : nativeEnv 1 () 0 = actualValue observation nontrivial half depth 0 := by
  calc
    _ = (runtimeReturnJordanCalculationResultAt observation nontrivial depth half 0).2.2.1 := rfl
    _ = _ := (actual_value_runtime observation nontrivial half depth 0).symm

theorem actual_prefix_value : (actualPrefixInput observation nontrivial half depth).1 =
    CombSource.Division.rawIterate observation half.down m
      (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  have value := (actualPrefixInput observation nontrivial half depth).2.1.sound.symm
  change (actualPrefixInput observation nontrivial half depth).1 =
    (C.returnJordanPrefixCode observation nontrivial depth half).eval
      (C.receipt observation nontrivial depth half).1.environment at value
  unfold C.returnJordanPrefixCode at value
  rw [Expr.eval_subst] at value
  exact value.trans (OriginalKReturnJordanSourceCalculation.actual_prefix_code observation nontrivial half
    (nativeEnv 1) ((actual_prefix_pa observation nontrivial half depth).trans
      (actual_pa_value observation nontrivial half depth)))

theorem actual_next_value : actualValue observation nontrivial half depth 1 =
    CombSource.Division.rawIterate observation half.down (m+1)
      (OriginalWholeDebtRJointMobiusReturnJordanSource.paJet observation nontrivial half m : BurnolL2) := by
  rw [actualValue, bound_code_value]
  exact OriginalKReturnJordanSourceCalculation.actual_next_code observation nontrivial half (nativeEnv 1)
    ((actual_prefix_pa observation nontrivial half depth).trans (actual_pa_value observation nontrivial half depth))

private def jetPrefixAt (coordinate : BurnolCompletedMellinCoordinate)
    (environment : Env Prog.Value Prog.Var)
    (binding : ∀ sort, OriginalKReturnJordanSourceCalculation.Var sort → Expr Prog.Value Prog.Var sort)
    (level target : Nat) : target ≤ level → {result : BurnolL2} →
      Trace environment ((JP.jetCode coordinate level).subst binding) (.const result) →
        Σ point : BurnolL2, Trace environment ((JP.jetCode coordinate target).subst binding) (.const point) := by
  induction level with
  | zero =>
    intro within result executed
    have zero : target = 0 := by omega
    subst target
    exact ⟨result, executed⟩
  | succ level previous =>
    intro within result executed
    by_cases equal : target = level+1
    · subst target
      exact ⟨result, executed⟩
    · have bound : target ≤ level := by omega
      have child : Σ point : BurnolL2,
          Trace environment ((JP.jetCode coordinate level).subst binding) (.const point) ×
          PLift ((burnolDirectRightResolventCLM coordinate).adjoint point = result) :=
        SourceOperationExecution.originalInput executed
      exact previous bound child.2.1

/-- Every prefix is eliminated from this execution's actual adjoint-m child. -/
def actualJetPrefix (index : Nat) (within : index ≤ m) :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        ((JP.jetCode c index).subst (C.returnJordanSourceBinding observation nontrivial depth half 0))
        (.const point) :=
  jetPrefixAt c (C.receipt observation nontrivial depth half).1.environment
    (C.returnJordanSourceBinding observation nontrivial depth half 0) m index within
    (actualPaInput observation nontrivial half depth).2.1

theorem actual_jet_prefix_value (index : Nat) (within : index ≤ m) :
    (actualJetPrefix observation nontrivial half depth index within).1 =
      OriginalWholeDebtRJointMobiusReturnJordanSource.jet observation nontrivial half index := by
  have value := (actualJetPrefix observation nontrivial half depth index within).2.sound.symm
  rw [Expr.eval_subst] at value
  exact value.trans (OriginalKReturnJordanSourceCalculation.actual_jet_code observation nontrivial half
    (nativeEnv 0)
    ((actual_borrowed_response observation nontrivial half depth).trans
      (borrowed_response_value observation nontrivial half depth))
    ((actual_borrowed_result observation nontrivial half depth).trans
      (borrowed_result_value observation nontrivial half depth)) index)

def actualDifferenceInput :
    Σ point : BurnolL2,
      Trace (C.receipt observation nontrivial depth half).1.environment
        ((OriginalKReturnJordanSourceCalculation.differenceCode c).subst
          (C.returnJordanSourceBinding observation nontrivial depth half 0)) (.const point) ×
      PLift (OriginalKReturnJordanSourceCalculation.sourceAction c point =
        (actualJetPrefix observation nontrivial half depth 0 (Nat.zero_le m)).1) := by
  have executed : Trace (C.receipt observation nontrivial depth half).1.environment
      (.linear (OriginalKReturnJordanSourceCalculation.sourceAction c).toLinearMap.toAddMonoidHom
        ((OriginalKReturnJordanSourceCalculation.differenceCode c).subst
          (C.returnJordanSourceBinding observation nontrivial depth half 0)))
      (.const (actualJetPrefix observation nontrivial half depth 0 (Nat.zero_le m)).1) :=
    (actualJetPrefix observation nontrivial half depth 0 (Nat.zero_le m)).2
  exact SourceOperationExecution.originalInput executed

theorem actual_difference_value : (actualDifferenceInput observation nontrivial half depth).1 =
    OriginalWholeDebtRJointMobiusReturnJordanSource.returnDifference observation nontrivial half := by
  have value := (actualDifferenceInput observation nontrivial half depth).2.1.sound.symm
  rw [Expr.eval_subst] at value
  exact value.trans (OriginalKReturnJordanSourceCalculation.actual_difference_code observation nontrivial half
    (nativeEnv 0)
    ((actual_borrowed_response observation nontrivial half depth).trans
      (borrowed_response_value observation nontrivial half depth))
    ((actual_borrowed_result observation nontrivial half depth).trans
      (borrowed_result_value observation nontrivial half depth)))

def boundary (field : Fin 2) : Formal ℤ Prog.Value Prog.Var () :=
  relationMap (R := ℤ) (C.receipt observation nontrivial depth half).1.environment (trace field).relationWords

theorem actual_boundary (field : Fin 2) : boundary observation nontrivial half depth field =
    Finsupp.single (raw field) (1 : ℤ) -
      Finsupp.single (.const (actualValue observation nontrivial half depth field)) 1 :=
  (trace field).relation_boundary (R := ℤ)

end OriginalKReturnJordanSourceWriteback
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKReturnJordanSourceWriteback"
