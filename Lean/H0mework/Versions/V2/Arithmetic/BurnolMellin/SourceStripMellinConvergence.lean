import H0mework.Versions.V2.Arithmetic.BurnolMellin.CompletedMellinPrimaryGenerator

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open Complex MeasureTheory Set

noncomputable section

theorem coPoissonMuntzScaleRemainder_mellinConvergent_strip
    (test : SchwartzMap ℝ ℂ) (s : ℂ)
    (positive : 0 < s.re) (belowOne : s.re < 1) :
    MellinConvergent (coPoissonMuntzScaleRemainder test) s := by
  have quarter :=
    positiveMellinExtension_coPoissonQuarterMellinMap_mellinConvergent
      (s / 2)
      (by rw [Complex.div_re]; norm_num; linarith)
      (by rw [Complex.div_re]; norm_num; linarith)
      test
  rw [positiveMellinExtension_quarter_eq_scaleRemainder_rpow] at quarter
  have source := (MellinConvergent.comp_rpow
    (f := coPoissonMuntzScaleRemainder test)
    (s := s / 2) (a := (1 / 2 : ℝ)) (by norm_num)).mp quarter
  convert source using 1
  norm_num
  ring

theorem burnolCompactAdditiveMellin_integrableOn_strip
    (source : burnolCompactAnnulusSource) (s : ℂ)
    (positive : 0 < s.re) (belowOne : s.re < 1) :
    IntegrableOn (fun t : ℝ =>
      (t : ℂ) ^ (-s) * burnolCompactAdditiveCoSum source t) (Ioi 0) := by
  have base := coPoissonMuntzScaleRemainder_mellinConvergent_strip
    source.1 s positive belowOne
  have reciprocal : MellinConvergent
      (fun t : ℝ => coPoissonMuntzScaleRemainder source.1
        (t ^ (-1 : ℝ))) (-s) := by
    apply (MellinConvergent.comp_rpow
      (f := coPoissonMuntzScaleRemainder source.1)
      (s := -s) (a := (-1 : ℝ)) (by norm_num)).mpr
    convert base using 1
    norm_num
  have divided := reciprocal.div_const (2 : ℂ)
  unfold MellinConvergent at divided
  apply divided.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t positiveT
  have tne : (t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt positiveT)
  rw [show t ^ (-1 : ℝ) = t⁻¹ by
    rw [Real.rpow_neg (le_of_lt positiveT), Real.rpow_one]]
  rw [coPoissonMuntzScaleRemainder_reciprocal_eq_compactAdditiveCoSum
    source positiveT]
  simp only [smul_eq_mul]
  rw [show (-s) - 1 = -s + (-1) by ring,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positiveT.ne')]
  rw [show (t : ℂ) ^ (-1 : ℂ) = (t : ℂ)⁻¹ by
    rw [Complex.cpow_neg, Complex.cpow_one]]
  push_cast
  field_simp [tne]

end

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
