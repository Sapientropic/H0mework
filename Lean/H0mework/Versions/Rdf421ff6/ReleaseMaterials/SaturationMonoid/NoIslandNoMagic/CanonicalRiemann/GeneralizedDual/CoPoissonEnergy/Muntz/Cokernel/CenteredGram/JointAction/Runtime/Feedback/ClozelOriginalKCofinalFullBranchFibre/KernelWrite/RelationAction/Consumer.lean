import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.RelationAction.Kernel

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.RelationAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open SourceGeneratedScalarDifferentialResidual
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
attribute [local irreducible] AS.localNativeReceipt
local instance relationDispositionGroups (grade:Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)

private theorem effect_zero_on_generated_sound
 (sound:GeneratedRelationSoundnessAt (bornFace observation nontrivial half depth ordinal)) :
 effectValue observation nontrivial half depth ordinal=0 := by
 have killed:=sound.sound (actual_boundary_in_born observation nontrivial half depth ordinal)
 change (bornFace observation nontrivial half depth ordinal).freeEvaluation
  (sourceBoundary observation nontrivial half depth ordinal)=0 at killed
 have read:=J.query_word_read (writerSeed observation nontrivial half depth ordinal)
  (A.epoch (writerBorn observation nontrivial half depth ordinal))
  (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))
  (sourceBoundary observation nontrivial half depth ordinal)
 exact (born_boundary_evaluator observation nontrivial half depth ordinal).symm.trans (read.symm.trans killed)

section DispositionRead
variable {PhysicalValue PhysicalVar:Unit→Type} [∀ target,AddCommGroup (PhysicalValue target)]
private theorem generated_disposition_consumer
 (seed:RootedAccountedUnfolding (PresentedRelationEventAt (Expr PhysicalValue PhysicalVar ())))
 (frame:A.M.Frame (Value:=PhysicalValue) (Var:=PhysicalVar) (sort:=()))
 {current:RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.Current frame.registered}
 (occurrence:SourceOperationInquiry.Context.Installation.Occurrence frame (current:=current))
 (effect result:PairValue PhysicalValue ())
 (read:result=(J.queryRaw seed frame occurrence (J.disposition seed frame occurrence)).expression.eval
  (PR.raw seed frame occurrence).environment)
 (zero:∀ _sound:GeneratedRelationSoundnessAt (J.face seed frame occurrence),effect=0) :
 match J.disposition seed frame occurrence with
 | .faithful _ _ _ => effect=0 ∧ result=(PR.raw seed frame occurrence).expression.eval
   (PR.raw seed frame occurrence).environment
 | .kernelResidual _ _ _ => effect=0 ∧ result=0
 | .unsound _ coordinate => result=coordinate.coordinate ∧ result≠0
 | .coverageResidual _ _ coordinate => effect=0 ∧ result=coordinate.representative ∧
   (type_of% coordinate.representative_not_mem_range) := by
 generalize selected:J.disposition seed frame occurrence=phase
 cases phase with
 | faithful sound coverage realization =>
  have query:=read.trans (congrArg (fun phase=>(J.queryRaw seed frame occurrence phase).expression.eval
   (PR.raw seed frame occurrence).environment) selected)
  exact ⟨zero sound,query⟩
 | kernelResidual sound obstruction coordinate =>
  have query:=read.trans (congrArg (fun phase=>(J.queryRaw seed frame occurrence phase).expression.eval
   (PR.raw seed frame occurrence).environment) selected)
  refine ⟨zero sound,query.trans ?_⟩
  change (Coefficients.expression (KernelWrite.J.kernelWord seed frame occurrence sound coordinate).val).eval
   (PR.raw seed frame occurrence).environment=0
  exact (Coefficients.expression_eval _ _).trans (KernelWrite.J.kernel_word_value _ _ _ sound coordinate)
 | unsound obstruction coordinate =>
  have query:=read.trans (congrArg (fun phase=>(J.queryRaw seed frame occurrence phase).expression.eval
   (PR.raw seed frame occurrence).environment) selected)
  have witness:result=coordinate.coordinate := query.trans
   ((Coefficients.expression_eval _ _).trans
    ((J.query_word_read seed frame occurrence coordinate.relation).symm.trans coordinate.coordinate_eq.symm))
  exact ⟨witness,fun vanishes=>coordinate.coordinate_ne_zero (witness.symm.trans vanishes)⟩
 | coverageResidual sound obstruction coordinate =>
  have query:=read.trans (congrArg (fun phase=>(J.queryRaw seed frame occurrence phase).expression.eval
   (PR.raw seed frame occurrence).environment) selected)
  exact ⟨zero sound,query,coordinate.representative_not_mem_range⟩
end DispositionRead

/-- Consume the original born disposition, retaining its actual unsound and coverage queries. -/
theorem actual_born_disposition_consumer : type_of% (generated_disposition_consumer
 (writerSeed observation nontrivial half depth ordinal)
 (A.epoch (writerBorn observation nontrivial half depth ordinal))
 (S.actualOccurrence (writerBorn observation nontrivial half depth ordinal))
 (effectValue observation nontrivial half depth ordinal)
 (bornResult observation nontrivial half depth ordinal).2.2.1
 (actual_born_query_value observation nontrivial half depth ordinal)
 (effect_zero_on_generated_sound observation nontrivial half depth ordinal)) :=
 generated_disposition_consumer _ _ _ _ _
  (actual_born_query_value observation nontrivial half depth ordinal)
  (effect_zero_on_generated_sound observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCofinalFullBranchFibre.KernelWrite.RelationAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
