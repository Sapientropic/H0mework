import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.SeedFourier
import H0mework.Arithmetic.Muntz.CoPoissonMuntzFactorization
import H0mework.Versions.R7e4da746.Arithmetic.BurnolMellin.SourceStripMellinConvergence

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Homogeneous
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology
open private half_integral_even from
  H0mework.Versions.R7e4da746.Arithmetic.RemainderSource.FaithfulForward

def homogeneousRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ):ℂ:=
  ((|x|:ℝ):ℂ)^(star c.value-1)

theorem actual_homogeneous_remainder_integrable (c:BurnolCompletedMellinCoordinate)
    (test:SchwartzMap ℝ ℂ):
    Integrable (fun x:ℝ=>homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|):=by
  let f:ℝ→ℂ:=fun x=>homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|
  have positive:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
  have below:(star c.value).re<1:=by simpa only [star_def,conj_re] using c.belowOne
  have native:=coPoissonMuntzScaleRemainder_mellinConvergent_strip test (star c.value) positive below
  have positiveDomain:IntegrableOn f (Ioi (0:ℝ)):=by
    apply native.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x pos
    change 0<x at pos
    simp only [f,homogeneousRaw,abs_of_pos pos,smul_eq_mul]
  have full:Integrable ((Ioi (0:ℝ)).indicator f):=positiveDomain.integrable_indicator measurableSet_Ioi
  have reflected:Integrable (fun x:ℝ=>(Ioi (0:ℝ)).indicator f (-x)):=
    (negMeasurePreserving.integrable_comp full.aestronglyMeasurable).mpr full
  apply (full.add reflected).congr
  filter_upwards [volume.ae_ne (0:ℝ)] with x nonzero
  change (Ioi (0:ℝ)).indicator f x+(Ioi (0:ℝ)).indicator f (-x)=f x
  by_cases pos:0<x
  · rw [indicator_of_mem (show x∈Ioi (0:ℝ) from pos),
      indicator_of_notMem (show -x∉Ioi (0:ℝ) by simp only [mem_Ioi];linarith),add_zero]
  · have negpos:0< -x:=by
      have negative:x<0:=lt_of_le_of_ne (le_of_not_gt pos) nonzero
      linarith
    rw [indicator_of_notMem (show x∉Ioi (0:ℝ) from pos),
      indicator_of_mem (show -x∈Ioi (0:ℝ) from negpos),zero_add]
    simp only [f,homogeneousRaw,abs_neg]

/-- The original homogeneous field has a genuine full comb-remainder read; no L2 qualification is used. -/
theorem actual_homogeneous_remainder (c:BurnolCompletedMellinCoordinate) (test:SchwartzMap ℝ ℂ):
    (1/2:ℂ)*(∫x:ℝ,homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|)=
      riemannZeta (star c.value)*coPoissonMuntzEvenSourceMellin test (star c.value):=by
  rw [half_integral_even _ (actual_homogeneous_remainder_integrable c test)
    (fun x=>by simp only [homogeneousRaw,abs_neg])]
  have positive:0<(star c.value).re:=by simp only [star_def,conj_re];linarith [c.rightHalf]
  have below:(star c.value).re<1:=by simpa only [star_def,conj_re] using c.belowOne
  rw [←coPoissonMuntzScaleRemainder_mellin_factorization test positive below]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x pos
  change 0<x at pos
  simp only [homogeneousRaw,abs_of_pos pos,smul_eq_mul]

/-- The zero is the original conjugate occurrence, so its entire homogeneous action vanishes. -/
theorem actual_original_homogeneous_action_zero (c:BurnolCompletedMellinCoordinate)
    (zero:riemannZeta c.value=0) (test:SchwartzMap ℝ ℂ):
    (1/2:ℂ)*(∫x:ℝ,homogeneousRaw c x*coPoissonMuntzScaleRemainder test |x|)=0:=by
  have reflected:riemannZeta (star c.value)=0:=
    (conjugateZeroObservation (burnolPaZeroObservation c zero)).mathlibZero
  rw [actual_homogeneous_remainder,reflected,zero_mul]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Homogeneous
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
