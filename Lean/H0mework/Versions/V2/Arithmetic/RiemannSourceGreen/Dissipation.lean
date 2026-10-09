import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.GreenClosedRange

/-! Every nonzero original Pa source has strictly negative Green pairing with its generated correction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section
private theorem source_reflects_zero (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) (zero : burnolMobiusSourceL2 p = 0) : p = 0 := by
  apply Subtype.ext
  apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ) (μ := volume))
  ext test
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (p : BurnolL2)) test =
    (Lp.toTemperedDistributionCLM ℂ volume 2 (0 : BurnolL2)) test
  rw [map_zero]
  have read := burnolRemainderSourceRead_Pa p inside test
  rw [zero, ← burnolRemainderSourceReadCLM_apply, map_zero] at read
  simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul, map_zero, zero_apply] using read.symm

theorem burnolPaSourceGreen_strict_dissipation (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) (nonzero : p ≠ 0) :
    (inner ℂ (burnolTateReciprocalL2 (burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩)))
      (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re < 0 := by
  let c := burnolPaSourceCorrection coordinate ⟨p, inside⟩
  let psi := burnolTateReciprocalL2 (burnolMobiusSourceL2 c)
  let boundary := ((1 / 4 : ℝ) : ℂ) ^ (coordinate.value - 1) *
    burnolPaResolventSourceCoefficient coordinate p
  have energy := burnolPaSourceGreen coordinate p inside
  change -4 * (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re =
    (2 * coordinate.value.re - 1) * ‖psi‖ ^ 2 + (1 / 2 : ℝ) * ‖boundary‖ ^ 2 at energy
  by_contra notNegative
  have sign : 0 < 2 * coordinate.value.re - 1 := by linarith [coordinate.rightHalf]
  have lhs : 0 ≤ (inner ℂ psi (burnolTateReciprocalL2 (burnolMobiusSourceL2 p))).re :=
    le_of_not_gt notNegative
  have energyZero : ‖psi‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖boundary‖, sq_nonneg ‖psi‖]
  have boundaryZero : ‖boundary‖ ^ 2 = 0 := by nlinarith
  have psiZero : psi = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg psi])
  have coefficientZero : burnolPaResolventSourceCoefficient coordinate p = 0 := by
    have zero : boundary = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg boundary])
    exact (mul_eq_zero.mp zero).resolve_left
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num : (((1 / 4 : ℝ) : ℂ)) ≠ 0)))
  have sourceZero : burnolMobiusSourceL2 c = 0 := by
    have twice := congrArg burnolTateReciprocalL2 psiZero
    simpa only [psi, burnolTateReciprocalL2_involutive, map_zero] using twice
  have cZero := source_reflects_zero c (burnolPaSourceCorrection_mem coordinate ⟨p, inside⟩) sourceZero
  have resolventZero : burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) = 0 := by
    have raw := congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2)) cZero
    change burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) -
      burnolPaResolventSourceCoefficient coordinate p • burnolUnitTailResponse coordinate 4 = 0 at raw
    simpa only [coefficientZero, zero_smul, sub_zero] using raw
  apply nonzero
  apply Subtype.ext
  exact burnolDirectRightResolvent_reflects_zero (coordinate.value / 2)
    (by rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf]) (p : BurnolL2) resolventZero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
