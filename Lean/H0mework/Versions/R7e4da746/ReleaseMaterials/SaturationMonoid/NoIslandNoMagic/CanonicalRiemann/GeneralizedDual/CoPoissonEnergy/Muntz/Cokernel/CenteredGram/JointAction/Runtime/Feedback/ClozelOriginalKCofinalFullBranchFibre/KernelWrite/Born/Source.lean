import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Installation

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
attribute [local irreducible] AS.localNativeReceipt
section Original
local instance originalGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev bornInstallation := actualJointInstallation (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)
def bornRootRead := actualRootRead (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)
theorem born_root_read : type_of% (actual_root_read
 (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal)
 (writerBorn observation nontrivial half depth ordinal)) :=
 actual_root_read (FR.jointCode (RSource.code observation nontrivial half))
  (D.factory observation nontrivial half) rfl
  (originalPredecessor observation nontrivial half depth ordinal)
  (writerBorn observation nontrivial half depth ordinal)

abbrev bornJointMaterial := (bornRootRead observation nontrivial half depth ordinal).1
abbrev installedPhase := actualPhase (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)
abbrev installedQuery := actualQuery (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)
abbrev installedWritten := actualWritten (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)

theorem installed_phase : type_of% (actual_phase (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)) :=
 actual_phase (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)

theorem installed_query : type_of% (actual_query (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)) :=
 actual_query (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)

theorem installed_written : type_of% (actual_written (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)) :=
 actual_written (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)

/-- The born query's actual paid trace is read into that same installed material. -/
theorem installed_paid_trace :
 ∀ event ∈ (SourceOperationPaidRelations.exposure
  (J.queryResult (writerSeed observation nontrivial half depth ordinal)
   (A.epoch (writerBorn observation nontrivial half depth ordinal))
   (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))).2.1.2).trace,
 event ∈ (installedWritten observation nontrivial half depth ordinal).trace := by
 intro event present
 exact Eq.mpr
  (congrArg (fun inventory => event ∈ inventory.trace)
   (installed_written observation nontrivial half depth ordinal))
  (J.complete_query_trace (writerSeed observation nontrivial half depth ordinal)
   (A.epoch (writerBorn observation nontrivial half depth ordinal))
   (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal)) event present)
end Original

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
