import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalInverseAction.Payment
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Complex MeasureTheory Set Filter
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Prior
export OriginalKCombCofinalInverseAction (inverse inverse_R inversePair actionPair totalBranches)
end Prior
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace L
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower (Value groups)
end L
namespace CF
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.CalculationFactory (collapseValue codeAt code_base_value)
end CF
namespace Full
export OriginalKCombFullResidualAction (branches joint_source_value complete_of_branches)
end Full
namespace P
export OriginalKCombPhysicalAction (R code)
end P
namespace FR
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation (jointCode completeInput)
end FR
local instance levelGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n+1))
variable (half : OriginalKCombCalculation.Half observation)

def inverseAt : (grade : Nat) → PairValue (L.Value (PairValue C.Value) grade) () →+
 PairValue (L.Value (PairValue C.Value) grade) ()
 | 0 => (Prior.actionPair observation nontrivial half).toAddMonoidHom
 | grade+1 => pairLinear (inverseAt grade)

theorem inverseAt_collapse (grade : Nat) (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 CF.collapseValue grade (inverseAt observation nontrivial half grade value) =
 Prior.actionPair observation nontrivial half (CF.collapseValue grade value) := by
 induction grade with
 | zero => rfl
 | succ grade prior =>
  change CF.collapseValue grade ((inverseAt observation nontrivial half grade value.1) +
   (inverseAt observation nontrivial half grade value.2)) = _
  rw [←map_add]
  exact prior _

-- Total is faithful to the complete p+r responsibility, not arbitrary pair presentation.
def totalAt (grade : Nat) (value : PairValue (L.Value (PairValue C.Value) grade) ()) : BurnolL2 :=
 Prior.totalBranches (CF.collapseValue grade value)

theorem inverseAt_total (grade : Nat) (value : PairValue (L.Value (PairValue C.Value) grade) ()) :
 totalAt grade (inverseAt observation nontrivial half grade value) =
 Prior.inverse observation nontrivial half (totalAt grade value) := by
 unfold totalAt
 rw [inverseAt_collapse]
 change (Prior.inversePair observation nontrivial half (CF.collapseValue grade value).1).1 +
  (Prior.inversePair observation nontrivial half (CF.collapseValue grade value).1).2 +
  ((Prior.inversePair observation nontrivial half (CF.collapseValue grade value).2).1 +
  (Prior.inversePair observation nontrivial half (CF.collapseValue grade value).2).2) = _
 rw [OriginalKCombCofinalInverseAction.inverse_pair_total,
  OriginalKCombCofinalInverseAction.inverse_pair_total, ←map_add]
 rfl

theorem R_code_total (environment : Env (PairValue (PairValue C.Value)) C.Var) :
 Prior.totalBranches ((FR.jointCode (P.code observation nontrivial half)).eval environment) =
 P.R observation nontrivial half (Prior.totalBranches (environment () ())) := by
 have generated := Full.complete_of_branches observation nontrivial half _ _
  (Full.joint_source_value observation nontrivial half environment)
 exact generated.2.2.1.trans (congrArg (P.R observation nontrivial half) (by
  change ((environment () ()).1.1 + (environment () ()).2.1) +
   ((environment () ()).1.2 + (environment () ()).2.2) = _
  unfold Prior.totalBranches
  abel))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalRResidualInverse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
