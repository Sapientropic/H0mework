import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementDivisionPhysicality

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Jets
open Complex MeasureTheory Set Filter Function
open NoIslandNoMagic.CanonicalRiemann
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open SourceGeneratedComplexFeaturePerfectification
open scoped InnerProductSpace Topology
noncomputable section

/-- The complete Xi factor is generated for any actual compact/Tate test;
no normalized-source equality or normalizer premise is used. -/
theorem actual_compact_full_Xi_factor {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (source : burnolCompactAnnulusSource) (w : ℂ)
    (positive : 0 < w.re) (belowHalf : w.re < 1 / 2) :
    mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) w =
      (2 * w - (1 - observation.coordinate)) ^
        generatedRiemannXiZeroOrder owner observation.coordinate *
      (2 * generatedRiemannBareZeroLocalizedSpectrum owner
        (1 - observation.coordinate) (2 * w) *
        coPoissonMuntzEvenSourceMellin source.1 (2 * w)) := by
  have doubledPositive : 0 < (2 * w).re := by simp only [mul_re]; norm_num; linarith
  have doubledBelow : (2 * w).re < 1 := by simp only [mul_re]; norm_num; linarith
  have neZero : 2 * w ≠ 0 := ne_of_apply_ne Complex.re (by simpa using ne_of_gt doubledPositive)
  have neOne : 2 * w ≠ 1 := ne_of_apply_ne Complex.re (by simpa using ne_of_lt doubledBelow)
  rw [positiveMellinExtension_coPoissonQuarterMellinMap_factorization source.1 positive belowHalf,
    ← generatedRiemannZeta_eq_mathlib owner,
    generatedRiemannZeta_zero_factorization owner (1 - observation.coordinate)
      (2 * w) neZero neOne (Gammaℝ_ne_zero_of_re_pos doubledPositive),
    generatedRiemannXiZeroOrder_one_sub]
  unfold coPoissonQuarterMuntzSourceMellin
  ring

/-- The actual compact source has a full generated Mellin jet inventory
at the same complement center.  The normalized source stays a distinct
reference source, whose actual nonzero source read is consumed internally. -/
theorem actual_compact_full_jet {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (source : burnolCompactAnnulusSource) :
    ∀ i < generatedRiemannXiZeroOrder owner observation.coordinate,
      iteratedDeriv i (fun w : ℂ =>
        mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) w)
        (burnolAnalyticComplementDivisionCenter observation) = 0 := by
  let center := burnolAnalyticComplementDivisionCenter observation
  let m := generatedRiemannXiZeroOrder owner observation.coordinate
  let f := fun w : ℂ => mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) w
  let reference := burnolAnalyticComplementNormalizedSource observation
  let A := fun w : ℂ => coPoissonMuntzEvenSourceMellin source.1 (2 * w)
  let N := fun w : ℂ => coPoissonMuntzEvenSourceMellin reference.1 (2 * w)
  let G := fun w : ℂ =>
    (burnolAnalyticComplementDivisionJet owner observation m w * A w) /
      (((-1 : ℂ) ^ m) * N w)
  have centerPositive : 0 < center.re := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith [observation.coordinate_re_lt_one]
  have centerBelow : center.re < 1 / 2 := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    simp only [Complex.sub_re, Complex.div_re, Complex.one_re]
    norm_num
    linarith
  have centerMem : center ∈ burnolPhysicalHeatMellinStrip := ⟨centerPositive, centerBelow⟩
  have sourceAnalytic (test : SchwartzMap ℝ ℂ) :
      AnalyticAt ℂ (fun w : ℂ => coPoissonMuntzEvenSourceMellin test (2 * w)) center := by
    have analytic : AnalyticOnNhd ℂ
        (fun w : ℂ => coPoissonMuntzEvenSourceMellin test (2 * w)) {w : ℂ | 0 < w.re} := by
      apply DifferentiableOn.analyticOnNhd
      · intro w hw
        change 0 < w.re at hw
        apply DifferentiableAt.differentiableWithinAt
        apply (coPoissonMuntzEvenSourceMellin_differentiableAt test (2 * w) ?_).comp w
        · exact (differentiableAt_const (2 : ℂ)).mul differentiableAt_id
        · simp only [Complex.mul_re]
          norm_num
          linarith
      · exact isOpen_Ioi.preimage Complex.continuous_re
    exact analytic center centerPositive
  have Aanalytic : AnalyticAt ℂ A center := sourceAnalytic source.1
  have Nanalytic : AnalyticAt ℂ N center := sourceAnalytic reference.1
  have doubledCenter : 2 * center = 1 - observation.coordinate := by
    dsimp only [center, burnolAnalyticComplementDivisionCenter]
    ring
  have Nne : N center ≠ 0 := by
    dsimp only [N]
    rw [doubledCenter]
    exact burnolCoordinateNormalizedAnnulusSource_mellin_ne_zero (1 - observation.coordinate)
  have scalarNe : (-1 : ℂ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have jetAnalytic := burnolAnalyticComplementDivisionJet_analyticOn observation m center centerMem
  have Ganalytic : AnalyticAt ℂ G center :=
    (jetAnalytic.mul Aanalytic).div ((analyticAt_const).mul Nanalytic) (mul_ne_zero scalarNe Nne)
  have germ : f =ᶠ[𝓝 center] fun w : ℂ => (w - center) ^ m * G w := by
    filter_upwards [burnolPhysicalHeatMellinStrip_isOpen.mem_nhds centerMem,
      Nanalytic.continuousAt.eventually_ne Nne] with w hw NwNe
    have wp : 0 < w.re := hw.1
    have wb : w.re < 1 / 2 := hw.2
    have doubledPositive : 0 < (2 * w).re := by simp only [mul_re]; norm_num; linarith
    have doubledBelow : (2 * w).re < 1 := by simp only [mul_re]; norm_num; linarith
    have neZero : 2 * w ≠ 0 := ne_of_apply_ne Complex.re (by simpa using ne_of_gt doubledPositive)
    have neOne : 2 * w ≠ 1 := ne_of_apply_ne Complex.re (by simpa using ne_of_lt doubledBelow)
    have cross : f w * N w =
        mellin (positiveMellinExtension (coPoissonQuarterMellinMap reference.1)) w * A w := by
      dsimp only [f, A, N]
      rw [actual_compact_full_Xi_factor observation source w wp wb,
        actual_compact_full_Xi_factor observation reference w wp wb]
      ring
    have originalFactor := burnolAnalyticComplementQuarter_factorization observation w
      doubledPositive doubledBelow neZero neOne (Gammaℝ_ne_zero_of_re_pos doubledPositive)
    change mellin (positiveMellinExtension (coPoissonQuarterMellinMap reference.1)) w =
      (w - center) ^ m * burnolAnalyticComplementQuarterQuotient owner observation w at originalFactor
    calc
      f w = (mellin (positiveMellinExtension (coPoissonQuarterMellinMap reference.1)) w * A w) / N w :=
        (eq_div_iff NwNe).2 cross
      _ = ((w - center) ^ m * burnolAnalyticComplementQuarterQuotient owner observation w * A w) / N w := by
        rw [originalFactor]
      _ = (w - center) ^ m * G w := by
        dsimp only [G, m]
        simp only [burnolAnalyticComplementDivisionJet, Nat.sub_self, pow_zero, mul_one]
        field_simp [scalarNe]
  have fanalytic : AnalyticAt ℂ f center :=
    (((analyticAt_id.sub analyticAt_const).pow m).mul Ganalytic).congr germ.symm
  have order : (m : ℕ∞) ≤ analyticOrderAt f center :=
    (natCast_le_analyticOrderAt fanalytic).2
      ⟨G, Ganalytic, by
        filter_upwards [germ] with w hw
        simpa only [smul_eq_mul] using hw⟩
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero fanalytic).1 order


end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.CombSource.Jets
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
