import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.Operations.Closure.Continuation.Cochain.Derived
import H0mework.Versions.R18f91d79.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidSyntaxCompletion
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source

-- These dependent theorems are consumed by name.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_stage_count"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_derived_continuation"

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift

attribute [local instance] relationGroups

open private code_budget from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeSigma.Writeback.Source

namespace Paid
export RootGeneratedDebtActivationJointSource.OwnerFree
  (runtimeCurrent cofinal_tick_derived_write cofinal_tick_terminal_extension)
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (seed)
export OriginalKDirectRCofinalCalculatedSource (original_source_operation source_payload_literal)
export OriginalKCombFullResidualAction.FR (jointCode)
export OriginalKCombFullResidualAction.P (code)
end Paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "source" => sourceRoot observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal
local notation "reader" => sourceReader observation nontrivial half depth ordinal
local notation "frontier" => Calc.originalFrontier observation nontrivial half depth ordinal

private theorem remaining_of_language {A Y Z : Unit → Type} [∀ sort, AddCommGroup (A sort)]
    (language : Y = Z) {first : Expr A Y ()} {second : Expr A Z ()} (same : HEq first second) :
    remaining first = remaining second := by
  cases language
  exact congrArg (fun word : Expr A Y () => remaining word) (eq_of_heq same)

/-- The four original paid stages come from the literal source programme. -/
theorem actual_paid_stage_count : (frontier).stageCount = 4 := by
  let packet := D.packet observation nontrivial half depth ordinal
  have written := (Paid.source_payload_literal observation nontrivial half depth ordinal).1
  have fee := remaining_of_language packet.2.2.2.down written
  have sourceBudget := code_budget (Paid.jointCode (Paid.code observation nontrivial half)) packet.1
  exact fee.trans (sourceBudget.trans (OriginalKCombFullResidualAction.joint_source_budget observation nontrivial half))

private abbrev paidRuntime (index : Nat) := (Paid.seed source origin reader).advance index

private theorem paid_active (index : Fin (frontier).stageCount) :
    0 < SourceOperationExecution.remaining
      (Paid.runtimeCurrent source origin reader (paidRuntime observation nontrivial half depth ordinal index.val)).1 := by
  have budget := (Paid.original_source_operation observation nontrivial half depth ordinal index.castSucc).1
  change SourceOperationExecution.remaining
    (Paid.runtimeCurrent source origin reader (paidRuntime observation nontrivial half depth ordinal index.val)).1 =
    SourceOperationExecution.remaining (frontier).sourcePayload.expression - index.val at budget
  have within : index.val < SourceOperationExecution.remaining (frontier).sourcePayload.expression := index.isLt
  omega

/-- The original literal R programme consumes the cofiber on its own strictly paid material stage. -/
theorem actual_paid_derived_continuation (index : Fin (frontier).stageCount) :
    let runtime := paidRuntime observation nontrivial half depth ordinal index.val
    let stage := (frontier).history.stageAt index.castSucc
    type_of% (Paid.cofinal_tick_derived_write source origin reader runtime) ∧
      type_of% (Paid.cofinal_tick_terminal_extension source origin reader runtime
        (paid_active observation nontrivial half depth ordinal index)) ∧
      type_of% (Paid.original_source_operation observation nontrivial half depth ordinal index.castSucc) ∧
      stage.next = runtime.tick.next := by
  let runtime := paidRuntime observation nontrivial half depth ordinal index.val
  exact ⟨Paid.cofinal_tick_derived_write source origin reader runtime,
    Paid.cofinal_tick_terminal_extension source origin reader runtime
      (paid_active observation nontrivial half depth ordinal index),
    Paid.original_source_operation observation nontrivial half depth ordinal index.castSucc, rfl⟩

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
