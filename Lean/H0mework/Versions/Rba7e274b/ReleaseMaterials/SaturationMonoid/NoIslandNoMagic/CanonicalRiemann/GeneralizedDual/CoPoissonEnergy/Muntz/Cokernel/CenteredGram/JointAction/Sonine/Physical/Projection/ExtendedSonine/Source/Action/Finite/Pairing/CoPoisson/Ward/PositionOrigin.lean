import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.PositionSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.PositionOrigin

open Complex Filter MeasureTheory Set
open scoped Topology
open OriginalRieszSource
noncomputable section

theorem power_exponent_positive (coordinate : BurnolCompletedMellinCoordinate) :
    0 < (1 - star coordinate.value).re := by
  simp only [sub_re, one_re, star_def, conj_re]
  linarith [coordinate.belowOne]

theorem power_exponent_nonzero (coordinate : BurnolCompletedMellinCoordinate) :
    1 - star coordinate.value ≠ 0 := by
  intro zero
  have positive := power_exponent_positive coordinate
  rw [zero] at positive
  exact (lt_irrefl (0 : ℝ)) positive

theorem weighted_power_continuous (coordinate : BurnolCompletedMellinCoordinate) :
    Continuous (fun x : ℝ => (x : ℂ) ^ (1 - star coordinate.value)) :=
  continuous_iff_continuousAt.mpr (fun x =>
    Complex.continuousAt_ofReal_cpow_const x _ (Or.inl (power_exponent_positive coordinate)))

theorem weighted_source (coordinate : BurnolCompletedMellinCoordinate) (x : ℝ) :
    (x : ℂ) * positionSource coordinate x =
      (1 / 2 : ℂ) * (x : ℂ) ^ (1 - star coordinate.value) -
        (x : ℂ) * GapEuler.gapMean (1 / 4 : ℝ) coordinate -
        (x : ℂ) * burnolRieszReturnRaw coordinate x := by
  by_cases zero : x = 0
  · subst x
    simp only [ofReal_zero, zero_mul, zero_cpow (power_exponent_nonzero coordinate), mul_zero, sub_zero]
  have power : (x : ℂ) * (x : ℂ) ^ (-star coordinate.value) =
      (x : ℂ) ^ (1 - star coordinate.value) := by
    rw [show 1 - star coordinate.value = 1 + (-star coordinate.value) by ring,
      Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr zero), cpow_one]
  unfold positionSource
  rw [mul_sub, mul_sub, ← mul_assoc, mul_comm (x : ℂ) (1 / 2 : ℂ), mul_assoc, power]

/-- The original singular position source has zero weighted origin flux. -/
theorem weighted_origin_zero (coordinate : BurnolCompletedMellinCoordinate) :
    Tendsto (fun x : ℝ => (x : ℂ) * positionSource coordinate x) (𝓝 0) (𝓝 0) := by
  have regular : Continuous (fun x : ℝ =>
      (1 / 2 : ℂ) * (x : ℂ) ^ (1 - star coordinate.value) -
      (x : ℂ) * GapEuler.gapMean (1 / 4 : ℝ) coordinate -
      (x : ℂ) * burnolRieszReturnRaw coordinate x) :=
    ((continuous_const.mul (weighted_power_continuous coordinate)).sub
      (Complex.continuous_ofReal.mul continuous_const)).sub
      (Complex.continuous_ofReal.mul (burnolRieszReturnRaw_continuous coordinate))
  have source := regular.tendsto (0 : ℝ)
  simp only [ofReal_zero, zero_cpow (power_exponent_nonzero coordinate), mul_zero, zero_mul, sub_self] at source
  exact source.congr' (Eventually.of_forall (fun x => (weighted_source coordinate x).symm))

end
end OriginalRieszFinitePairing.CoPoisson.Ward.PositionOrigin
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
