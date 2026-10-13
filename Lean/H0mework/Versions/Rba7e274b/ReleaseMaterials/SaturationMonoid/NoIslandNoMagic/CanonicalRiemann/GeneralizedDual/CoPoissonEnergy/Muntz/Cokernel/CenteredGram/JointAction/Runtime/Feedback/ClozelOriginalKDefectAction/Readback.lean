import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Return
export OriginalKFiniteReaction (actualWrite actualWriteRead actual_reaction_write)
end Return
namespace N
export OriginalKFiniteReaction.N (input)
end N
namespace Dynamic
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics (updated_total)
end Dynamic
local instance readbackGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- The actual parent return write, with its own material increment, supplies this child source.
theorem actual_parent_input (ordinal : Nat) :
    actualEnvironment observation nontrivial half depth ordinal () () =
      Prior.actualWriteRead observation nontrivial half depth ordinal := by
  let parent := defectParent observation nontrivial half depth ordinal
  let child := defectPacket observation nontrivial half depth ordinal
  let computed := (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
    (N.input (R.actualMaterial parent.2.1.1 parent.2.2.1)).environment
  have childGrade : child.1 = parent.1 + 1 := by
    unfold child defectPacket
    exact AS.nativeAfterAdmission_grade (defectFactory observation nontrivial half) parent
  have childValue : HEq (child.2.1.1.activeEnvironment () ()) computed := by
    unfold child defectPacket
    exact Dyn.packet_native_value (defectFactory observation nontrivial half) parent ()
  have actual := Dyn.collapse_generated_successor parent.1 child.1 childGrade _ computed childValue
  have source : computed = Return.actualWrite observation nontrivial half depth ordinal := by
    unfold computed
    rw [Return.actual_reaction_write]
    change (R.actualMaterial parent.2.1.1 parent.2.2.1).raw.eval
      ((R.actualMaterial parent.2.1.1 parent.2.2.1).environment+(R.actualMaterial parent.2.1.1 parent.2.2.1).increment) = _
    exact Expr.eval_update (R.actualMaterial parent.2.1.1 parent.2.2.1).raw
      (R.actualMaterial parent.2.1.1 parent.2.2.1).environment
      (R.actualMaterial parent.2.1.1 parent.2.2.1).increment
  change CF.collapseValue child.1 (child.2.1.1.activeEnvironment () (), 0) = _
  exact actual.trans (congrArg (CF.collapseValue parent.1) source)

theorem actual_complete_source_value (ordinal : Nat) :
    CF.collapseValue (defectPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 =
      actionFields (RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal) := by
  rw [actual_admitted_value,actual_parent_input,actual_parent_field]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
