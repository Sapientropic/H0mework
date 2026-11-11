import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.Born.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.RelationAction.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.Effect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
attribute [local irreducible] AS.localNativeReceipt
namespace RA
export RelationAction
 (bornRaw bornPhase bornResult sourceBoundary currentEnvironment sourceIncrement effectValue
  born_boundary_evaluator actual_born_inverse_fibre actual_kernel_same_word_effect
  actual_kernel_born_evaluator actual_born_disposition_consumer)
end RA
local instance effectGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev installedRaw := actualRaw (FR.jointCode (RSource.code observation nontrivial half))
 (D.factory observation nontrivial half) rfl
 (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)
theorem installed_raw : installedRaw observation nontrivial half depth ordinal=
 RA.bornRaw observation nontrivial half depth ordinal :=
 actual_raw (FR.jointCode (RSource.code observation nontrivial half))
  (D.factory observation nontrivial half) rfl
  (originalPredecessor observation nontrivial half depth ordinal) (writerBorn observation nontrivial half depth ordinal)

def installedEffect :=
 (residualEquivRange (evaluation (R:=ℤ) (installedRaw observation nontrivial half depth ordinal).environment)
  (canonicalResidual (evaluation (R:=ℤ) (installedRaw observation nontrivial half depth ordinal).environment)
   (RA.sourceBoundary observation nontrivial half depth ordinal))).val

theorem installed_effect : installedEffect observation nontrivial half depth ordinal=
 RA.effectValue observation nontrivial half depth ordinal := by
 unfold installedEffect
 rw [installed_raw]
 exact RA.actual_born_inverse_fibre observation nontrivial half depth ordinal

theorem installed_boundary_effect :
 evaluation (R:=ℤ) (installedRaw observation nontrivial half depth ordinal).environment
  (RA.sourceBoundary observation nontrivial half depth ordinal)=
 installedEffect observation nontrivial half depth ordinal := by
 rw [installed_effect,installed_raw]
 exact RA.born_boundary_evaluator observation nontrivial half depth ordinal

abbrev queryWritten := ∀ event ∈ (SourceOperationPaidRelations.exposure
 (RA.bornResult observation nontrivial half depth ordinal).2.1.2).trace,
 event ∈ (installedWritten observation nontrivial half depth ordinal).trace


section SameKernel
variable (sound : GeneratedRelationSoundnessAt (writerFace observation nontrivial half depth ordinal))
variable (obstruction : GeneratedCoverageResidualObstructionAt (writerFace observation nontrivial half depth ordinal) sound)
variable (coordinate : GeneratedKernelResidualCoordinateAt (writerFace observation nontrivial half depth ordinal) sound)
variable (selected : writerPhase observation nontrivial half depth ordinal=.kernelResidual sound obstruction coordinate)
include obstruction selected in
theorem installed_same_word_effect : installedEffect observation nontrivial half depth ordinal=
 effectEvaluator (R:=ℤ) (RA.currentEnvironment observation nontrivial half depth ordinal)
  (RA.sourceIncrement observation nontrivial half depth ordinal)
  (writerWord observation nontrivial half depth ordinal sound coordinate).val :=
 (installed_effect observation nontrivial half depth ordinal).trans
  (RA.actual_kernel_same_word_effect observation nontrivial half depth ordinal sound obstruction coordinate selected)

include obstruction selected in
theorem installed_kernel_read :
 evaluation (R:=ℤ) (installedRaw observation nontrivial half depth ordinal).environment
  (writerWord observation nontrivial half depth ordinal sound coordinate).val=
 installedEffect observation nontrivial half depth ordinal := by
 rw [installed_effect,installed_raw]
 exact RA.actual_kernel_born_evaluator observation nontrivial half depth ordinal sound obstruction coordinate selected
end SameKernel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.BornInstalledJoint.Effect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
