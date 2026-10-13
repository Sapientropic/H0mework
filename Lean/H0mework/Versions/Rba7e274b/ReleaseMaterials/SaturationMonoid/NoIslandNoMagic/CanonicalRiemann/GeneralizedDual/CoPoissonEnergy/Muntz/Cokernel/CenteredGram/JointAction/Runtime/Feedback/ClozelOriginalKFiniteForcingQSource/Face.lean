import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturnGramAction.Primitive
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedResponseGramAction.Boundary
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance faceAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
namespace Paid
export OriginalKSourceScaledMaximalResponse (originalForcingPair actual_original_K_finite_pair)
export OriginalKPairedResponseGramAction (rawQ rawPa originalOutside actual_original_boundary_forcing originalGeneratedPaBoundary)
end Paid
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

private theorem original_Q_K :
 Q (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)=
 burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) := by
 have physical : P (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)=
   burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) :=
   by
    apply Subtype.ext
    exact Submodule.starProjection_eq_self_iff.mpr
     (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)).property
 change OP (P (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))=_
 rw [physical]
 exact Submodule.starProjection_eq_self_iff.mpr
   (riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal _ observation.mathlibZero)

private theorem original_boundary_Q_read (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Paid.originalGeneratedPaBoundary observation nontrivial half h nonnegative bounded=
 pairedMellinTranslationCharacter observation.coordinate h •
   burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)-
 Q (pairedBurnolMultiplicativeDilation h
   (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)) := by
 unfold OriginalKPairedResponseGramAction.originalGeneratedPaBoundary
 rw [OriginalKPairedResponseGramAction.BoundarySource.generated_boundary_realizes_original _ observation.mathlibZero h nonnegative bounded]
 unfold burnolZeroPairedFixedAnnulusBoundary
 rw [map_sub,map_smul]
 have kernel:=riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
   (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) observation.mathlibZero
 change pairedMellinTranslationCharacter (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half).value h •
   OP (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half))-
   OP (burnolPairedAmbientCompression h
    (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)))=_
 rw [Submodule.starProjection_eq_self_iff.mpr kernel,OriginalKCombCofinalTwoDirection.coordinate_value]
 unfold burnolPairedAmbientCompression evenBurnolMultiplicativeCompression SourceGeneratedCompressedUnitaryDefectPort.compression
 unfold pairedBurnolMultiplicativeDilation
 simp only [smul_apply,add_apply,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,map_smul,map_add]
 rfl

/-- The literal full C-and-two-mean source and the original K finite forcing are restrictions of the same generated source equation. -/
theorem actual_complete_finite_forcing_face (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 Q (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)=
 -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
 Q (Paid.originalForcingPair observation nontrivial half h) := by
 rw [Paid.actual_original_boundary_forcing observation nontrivial half h nonnegative bounded,
   original_boundary_Q_read,Paid.actual_original_K_finite_pair,map_add,map_smul,map_smul,original_Q_K]
 module


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
