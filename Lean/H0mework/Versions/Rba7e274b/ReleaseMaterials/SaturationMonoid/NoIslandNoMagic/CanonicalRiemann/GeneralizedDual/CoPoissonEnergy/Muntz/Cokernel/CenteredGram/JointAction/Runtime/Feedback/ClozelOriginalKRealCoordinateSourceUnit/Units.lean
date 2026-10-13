import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Source
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

include nontrivial half

/-- The exact original source difference is qualified by the actual real-face Abel action. -/
theorem actual_original_source_difference_ne_zero:star observation.coordinate-observation.coordinate≠0 :=by
 intro zero
 have read:=congrArg Complex.im zero
 simp only [Complex.sub_im,Complex.star_def,Complex.conj_im,Complex.zero_im] at read
 apply actual_original_zero_coordinate_im_ne_zero observation nontrivial half
 linarith

/-- The return source scalar becomes a unit only after the original branch has been generated. -/
theorem actual_original_return_sourceA_ne_zero:OriginalKSourceScaledMaximalResponse.Return.sourceA observation≠0 :=by
 unfold OriginalKSourceScaledMaximalResponse.Return.sourceA
 exact div_ne_zero (actual_original_source_difference_ne_zero observation nontrivial half) (by norm_num)

/-- The same original physical response factor consumes its two true source units; no extra response weight is introduced. -/
theorem actual_original_response_kappa_ne_zero:OriginalKCoupledPhysicalRFieldSource.actualResponseKappa c≠0 :=by
 rw [OriginalKCoupledPhysicalRFieldSource.actual_response_kappa_source]
 have first:star (c).value-(c).value≠0:=actual_original_source_difference_ne_zero observation nontrivial half
 have second:star (c).value+(c).value-1≠0:=by
  have paid:=OriginalRieszSourceGreen.source_cross_parameter_ne_zero c c
  simpa only [add_comm] using paid
 exact mul_ne_zero first second

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKRealCoordinateSourceUnit
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
