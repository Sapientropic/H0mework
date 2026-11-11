import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal.Phase

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace Joint
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (queryRaw query_word_read queryReader queryResult complete_query_trace)
end Joint
local instance residualGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

def nativeQuery (native : NativeSigma.NativePacket)
 (phase : ResidualDispositionOutcome (WB.nativeFace native)) :=
 Joint.queryRaw native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1) phase

private theorem unsound_query_value (native : NativeSigma.NativePacket)
 (obstruction : GeneratedUnsoundRelationObstructionAt (WB.nativeFace native))
 (coordinate : GeneratedRelationResidualCoordinateAt (WB.nativeFace native)) :
 (nativeQuery native (.unsound obstruction coordinate)).expression.eval
  (nativeQuery native (.unsound obstruction coordinate)).environment=coordinate.coordinate := by
 change (Coefficients.expression coordinate.relation).eval _=coordinate.coordinate
 exact (Coefficients.expression_eval coordinate.relation _).trans
  ((Joint.query_word_read native.2.1.2 (A.epoch native.2.1.1) (S.actualOccurrence native.2.1.1)
    coordinate.relation).symm.trans coordinate.coordinate_eq.symm)

private theorem unsound_query_nonzero (native : NativeSigma.NativePacket)
 (phase : ResidualDispositionOutcome (WB.nativeFace native))
 (selected : ∃ (obstruction : GeneratedUnsoundRelationObstructionAt (WB.nativeFace native))
   (coordinate : GeneratedRelationResidualCoordinateAt (WB.nativeFace native)),
   phase=.unsound obstruction coordinate) :
 (nativeQuery native phase).expression.eval (nativeQuery native phase).environment≠0 := by
 obtain ⟨obstruction,coordinate,actual⟩:=selected
 rw [actual,unsound_query_value]
 exact coordinate.coordinate_ne_zero

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

/-- The actual installed residual supplies a nonzero source query, with its original coordinate. -/
theorem actual_next_query_nonzero : type_of% (unsound_query_nonzero _ _
 (actual_next_phase_unsound observation nontrivial half depth ordinal)) :=
 unsound_query_nonzero _ _ (actual_next_phase_unsound observation nontrivial half depth ordinal)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
