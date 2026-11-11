import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.ExactCurrent
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open BurnolPhysicalState
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
 (admission_native_full admission_native_distance nativePresentation)
end AS
namespace Admissions
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.Admissions
 (startAt index index_eq_stop distance)
end Admissions
namespace Dyn
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullSourceDynamics
 (cofinal_next_active)
end Dyn
namespace D
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg packet input raw raw_successor)
end D
namespace Div
export OriginalKDirectRCofinalDivision
 (sourceResponse source_response_positionGap actual_R_source_split)
export OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_source_scalar_action_generated)
end Div
namespace Pa
export OriginalKCombCofinalPaAction (invisible)
end Pa
namespace Pricing
export BurnolPhysicalState.CombSource.Pricing (ambient_R_scalar_action)
end Pricing
namespace P
export OriginalKCombPhysicalAction (R)
end P
local instance exactGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
local instance exactComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

theorem original_selected_current :
 ((originalRuntime observation nontrivial half depth).stateAt
  (originalBirthTick observation nontrivial half depth ordinal)).engine.node=
 .active (AS.nativePresentation (originalNative observation nontrivial half depth ordinal)
  (AS.localNativeReceipt (originalNative observation nontrivial half depth ordinal)).1) := by
 have stopIndex:=Admissions.index_eq_stop (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal
 have distance:=AS.admission_native_distance (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
  (Admissions.startAt (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)
 rw [← stopIndex] at distance
 have full:=AS.admission_native_full (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
  (Admissions.startAt (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)
  (AS.localNativeReceipt (originalNative observation nontrivial half depth ordinal)).1 (Nat.le_refl _)
 rw [← stopIndex] at full
 have lengthEq : Admissions.distance (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
  (Admissions.index (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal+1)=
  (AS.localNativeReceipt (originalNative observation nontrivial half depth ordinal)).1+1 := distance
 have indexStep : originalBirthIndex observation nontrivial half depth ordinal=
  Admissions.index (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal+1+
  Admissions.distance (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
   (Admissions.index (D.factory observation nontrivial half)
    (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal+1) := rfl
 have atTick : originalBirthTick observation nontrivial half depth ordinal=
  Admissions.index (D.factory observation nontrivial half)
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal+1+
  (AS.localNativeReceipt (originalNative observation nontrivial half depth ordinal)).1 := by
  change originalBirthIndex observation nontrivial half depth ordinal-1=_
  omega
 have atCurrent := (Family.actual_node (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl
  (originalBirthTick observation nontrivial half depth ordinal))
 rw [← atTick] at full
 exact atCurrent.trans (congrArg RootInquiryProcessNode.active full)

/-- The native source acts on the original complete input, with the true cofinal index shift. -/
theorem original_action_input_successor :
 originalActionInput observation nontrivial half depth (ordinal+1)=D.input observation nontrivial half depth ordinal :=
 congrArg (fun env =>
  SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.FullResidualCalculation.completeInput
   (fun target name => CF.collapseValue (D.packet observation nontrivial half depth ordinal).1
    (env target name,0)) () ())
 (Dyn.cofinal_next_active (D.factory observation nontrivial half)
  (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)

abbrev literalBornBranches := CF.collapseValue
 (originalNative observation nontrivial half depth (ordinal+1)).1
 ((writerBorn observation nontrivial half depth (ordinal+1)).activeEnvironment () (),0)
def literalBorn : BurnolL2 :=
 let branches:=literalBornBranches observation nontrivial half depth ordinal
 (branches.1.1+branches.1.2)+(branches.2.1+branches.2.2)

theorem literal_born_R :
 literalBorn observation nontrivial half depth ordinal=
 P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal) := by
 have branches:=(original_born_full_R observation nontrivial half depth (ordinal+1)).trans
  (congrArg (Full.branches observation nontrivial half)
   (original_action_input_successor observation nontrivial half depth ordinal))
 exact (Full.complete_of_branches observation nontrivial half _ _ branches).2.2.1

/-- The paid original R equation and response gap are consumed on the literal writer birth. -/
theorem actual_native_writer_action (w : ℂ) (wRight : 1/4<w.re) (wBelow : w.re<1/2) :
 let read:=burnolAmbientCompletedMellinEvaluator
  (burnolDivisionCompletedMellinCoordinate w wRight wBelow)
 read (literalBorn observation nontrivial half depth ordinal)=
  (-(1/(observation.coordinate/2+w-(1/2:ℂ))))*read (D.raw observation nontrivial half depth ordinal) ∧
 read (P.R observation nontrivial half (literalBorn observation nontrivial half depth ordinal))=
  (-(1/(observation.coordinate/2+w-(1/2:ℂ))))*
   read (Div.sourceResponse observation nontrivial half depth ordinal : BurnolL2)+
  read (P.R observation nontrivial half (P.R observation nontrivial half
   (Pa.invisible (D.raw observation nontrivial half depth ordinal)))) ∧
 type_of% (original_selected_current observation nontrivial half depth (ordinal+1)) ∧
 type_of% (original_runtime_next observation nontrivial half depth (ordinal+1)) ∧
 type_of% (original_runtime_whole observation nontrivial half depth (ordinal+1)) ∧
 type_of% (original_query_trace_written observation nontrivial half depth (ordinal+1)) := by
 intro read
 have bornRaw : literalBorn observation nontrivial half depth ordinal=
  D.raw observation nontrivial half depth (ordinal+1) :=
  (literal_born_R observation nontrivial half depth ordinal).trans
   (D.raw_successor observation nontrivial half depth ordinal).symm
 have equation := (congrArg read bornRaw).trans
  (Div.actual_source_scalar_action_generated observation nontrivial half depth ordinal w wRight wBelow)
 have split:=bornRaw.trans (Div.actual_R_source_split observation nontrivial half depth ordinal)
 have responseEquation :
  read (P.R observation nontrivial half (Div.sourceResponse observation nontrivial half depth ordinal : BurnolL2))=
   (-(1/(observation.coordinate/2+w-(1/2:ℂ))))*
    read (Div.sourceResponse observation nontrivial half depth ordinal : BurnolL2) := by
  rw [OriginalKCombCofinalRAction.original_R_direct]
  exact Pricing.ambient_R_scalar_action (observation.coordinate/2)
   (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) _
   (Div.source_response_positionGap observation nontrivial half depth ordinal) w wRight wBelow
 have nextEquation:=congrArg (fun value : BurnolL2 => read (P.R observation nontrivial half value)) split
 rw [map_add,map_add,responseEquation] at nextEquation
 exact ⟨equation,nextEquation,original_selected_current observation nontrivial half depth (ordinal+1),
  original_runtime_next observation nontrivial half depth (ordinal+1),
  original_runtime_whole observation nontrivial half depth (ordinal+1),
  original_query_trace_written observation nontrivial half depth (ordinal+1)⟩

/-- The original disposition's dependent output accompanies the same actual action and tick. -/
def actual_native_writer_material (w : ℂ) (wRight : 1/4<w.re) (wBelow : w.re<1/2) :=
 (originalOutput observation nontrivial half depth (ordinal+1),
  PLift.up (actual_native_writer_action observation nontrivial half depth ordinal w wRight wBelow))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.ExactCurrent
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
