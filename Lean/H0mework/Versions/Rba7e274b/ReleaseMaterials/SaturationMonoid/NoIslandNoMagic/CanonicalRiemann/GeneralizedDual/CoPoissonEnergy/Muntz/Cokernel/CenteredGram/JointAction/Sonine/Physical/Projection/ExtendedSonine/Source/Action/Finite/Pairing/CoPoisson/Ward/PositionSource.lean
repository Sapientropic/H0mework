import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.InverseTail
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientMellin

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionSource

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource
noncomputable section
local notation "q" => (1 / 4 : ℝ)

private theorem power_integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-star coordinate.value)) (Ioc 0 q) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ q)).mp
  apply intervalIntegral.intervalIntegrable_cpow'
  simp only [neg_re, star_def, conj_re]
  linarith [coordinate.belowOne]

/-- The original position profile has a genuine integral through its singular origin. -/
theorem integrable (coordinate : BurnolCompletedMellinCoordinate) :
    IntegrableOn (positionSource coordinate) (Ioc 0 q) := by
  exact (((power_integrable coordinate).const_mul (1 / 2 : ℂ)).sub
    (continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self)).sub
      ((burnolRieszReturnRaw_continuous coordinate).integrableOn_Icc.mono_set Ioc_subset_Icc_self)

private theorem return_positive_mass (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioc 0 q, burnolRieszReturnRaw coordinate x) = 0 := by
  have reflected := intervalIntegral.integral_comp_neg
    (f := burnolRieszReturnRaw coordinate) (a := -q) (b := 0)
  simp only [return_raw_even, neg_zero, neg_neg] at reflected
  have left : IntervalIntegrable (burnolRieszReturnRaw coordinate) volume (-q) 0 :=
    (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable (-q) 0
  have right : IntervalIntegrable (burnolRieszReturnRaw coordinate) volume 0 q :=
    (burnolRieszReturnRaw_continuous coordinate).intervalIntegrable 0 q
  have whole := intervalIntegral.integral_add_adjacent_intervals left right
  rw [reflected, Constructor.return_integral_zero] at whole
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ q)]
  linear_combination whole / 2

private theorem power_mass (coordinate : BurnolCompletedMellinCoordinate) :
    (1 / 2 : ℂ) * (∫ x : ℝ in Ioc 0 q, (x : ℂ) ^ (-star coordinate.value)) =
      (q : ℂ) * GapEuler.gapMean q coordinate := by
  have below : (star coordinate.value).re < 1 := by
    simpa only [star_def, conj_re] using coordinate.belowOne
  have source := integral_cpow_neg_on_burnolGap (star coordinate.value) below
  change (∫ x : ℝ in Ioc 0 q, (x : ℂ) ^ (-star coordinate.value)) =
    (q : ℂ) ^ (1 - star coordinate.value) / (1 - star coordinate.value) at source
  rw [source]
  have notZero : 1 - star coordinate.value ≠ 0 := by
    intro h
    have re := congrArg Complex.re (sub_eq_zero.mp h)
    simp only [one_re, star_def, conj_re] at re
    linarith [coordinate.belowOne]
  have power : (q : ℂ) ^ (1 - star coordinate.value) =
      (q : ℂ) ^ (-star coordinate.value) * (q : ℂ) := by
    rw [show 1 - star coordinate.value = -star coordinate.value + 1 by ring,
      Complex.cpow_add _ _ (by norm_num : (q : ℂ) ≠ 0), Complex.cpow_one]
  apply mul_left_cancel₀ notZero
  calc
    _ = (1 / 2 : ℂ) * (q : ℂ) ^ (1 - star coordinate.value) := by field_simp
    _ = _ := by
      rw [mul_left_comm (1 - star coordinate.value) (q : ℂ),
        GapEuler.gapMean_primitive q (by norm_num), power]
      ring

/-- Original gap normalization and the original return mass pay the whole position mean. -/
theorem positive_mass_zero (coordinate : BurnolCompletedMellinCoordinate) :
    (∫ x : ℝ in Ioc 0 q, positionSource coordinate x) = 0 := by
  have first := (power_integrable coordinate).const_mul (1 / 2 : ℂ)
  have constant : IntegrableOn (fun _ : ℝ => GapEuler.gapMean q coordinate) (Ioc 0 q) :=
    continuous_const.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have returned : IntegrableOn (burnolRieszReturnRaw coordinate) (Ioc 0 q) :=
    (burnolRieszReturnRaw_continuous coordinate).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  change (∫ x : ℝ in Ioc 0 q, (1 / 2 : ℂ) * (x : ℂ) ^ (-star coordinate.value) -
    GapEuler.gapMean q coordinate - burnolRieszReturnRaw coordinate x) = 0
  have firstSplit := integral_sub first constant
  have fullSplit := integral_sub (first.sub constant) returned
  simp only [Pi.sub_apply] at firstSplit fullSplit
  rw [fullSplit, firstSplit,
    integral_const_mul, power_mass, return_positive_mass, integral_const]
  norm_num [Real.volume_Ioc, Complex.real_smul]

theorem derivative (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) (positive : 0 < x) :
    HasDerivAt (positionSource coordinate) (positionExteriorDerivative coordinate x) x :=
  (((burnolMellinTailPower_hasDerivAt (star coordinate.value) positive).const_mul
    (1 / 2 : ℂ)).sub_const (GapEuler.gapMean q coordinate)).sub
      (burnolRieszReturnRaw_hasDerivAt coordinate x)

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
