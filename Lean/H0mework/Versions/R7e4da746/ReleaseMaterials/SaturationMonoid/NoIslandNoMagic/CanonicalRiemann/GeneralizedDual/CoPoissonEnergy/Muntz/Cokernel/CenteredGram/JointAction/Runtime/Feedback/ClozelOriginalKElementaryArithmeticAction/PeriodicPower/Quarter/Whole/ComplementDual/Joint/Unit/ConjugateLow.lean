import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.MovingInput.Clock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKRealCoordinateSourceUnit.Source
import H0mework.Versions.R7e4da746.Arithmetic.BurnolMellin.FourierSiblingComplementZero

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource CombSource.Division
open OriginalKFiniteOrderRelease OriginalKFiniteOrderRelease.UnitPowerSource
open OriginalKRealCoordinateSourceUnit
open scoped InnerProductSpace Topology
open private pa_le_closed generator_raw from H0mework.Versions.R7e4da746.Arithmetic.RiemannBandResponse.Source.Division.Whole
open private comb_coefficient_ne from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitPowerSource
local notation "q" => burnolUnscaledCommonGapRadius
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "w" => (1-star observation.coordinate)/2
include nontrivial half

private theorem probe_mem : w ∈ burnolPhysicalHeatMellinStrip := by
  have below := observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial |>.2
  change 0 < ((1-star observation.coordinate)/2).re ∧ ((1-star observation.coordinate)/2).re < 1/2
  simp only [Complex.div_re, Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
  norm_num
  constructor <;> linarith [half.down]

private theorem probe_apart : w ≠ burnolAnalyticComplementDivisionCenter observation := by
  intro same
  have nonreal := actual_original_zero_coordinate_im_ne_zero observation nontrivial half
  have equal : observation.coordinate = star observation.coordinate := by
    dsimp only [burnolAnalyticComplementDivisionCenter, selectedCoPoissonMuntzParameter] at same
    linear_combination 2*same
  have part := congrArg Complex.im equal
  simp only [Complex.star_def, Complex.conj_im] at part
  exact nonreal (by linarith)

private theorem probe_jet_zero (source : burnolCompactAnnulusSource) (k : ℕ) (atMost : k ≤ m) :
    jet observation source k w = 0 := by
  have initial : sourceMellin source w = 0 := by
    have reflected := riemannZeta_one_sub_eq_zero_of_rightHalfZero (barC c) observation.conjugate_mathlibZero
    have factor := positiveMellinExtension_coPoissonQuarterMellinMap_factorization source.1
      (probe_mem observation nontrivial half).1 (probe_mem observation nontrivial half).2
    change mellin (positiveMellinExtension (coPoissonQuarterMellinMap source.1)) w = _ at factor
    rw [show 2*w = 1-(barC c).value by change 2*((1-star observation.coordinate)/2) = 1-star observation.coordinate; ring,
      reflected, zero_mul] at factor
    exact factor
  induction k with
  | zero => simpa only [jet, pow_zero, Function.iterate_zero_apply, one_mul] using initial
  | succ k previous =>
    rw [← jet_succ observation half.down source k (by omega) w (probe_apart observation nontrivial half),
      previous (by omega), mul_zero]

private theorem compact_cross_fourier_zero (source : burnolCompactAnnulusSource) (k : ℕ) (atMost : k ≤ m) :
    inner ℂ (fourierL2 (K (barC c) : BurnolL2))
      (rawIterate observation half.down k (burnolCompactAdditiveL2 source)) = 0 := by
  have physical := compact_physical observation nontrivial half.down source k atMost
  let value : BurnolPaAmbientCarrier :=
    ⟨quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k), physical⟩
  have heat := heat_jet observation nontrivial half.down source k atMost physical
    (probe_mem observation nontrivial half)
  rw [probe_jet_zero observation nontrivial half source k atMost] at heat
  have gamma : Gammaℝ (2*w) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by
    rw [show 2*w = 1-star observation.coordinate by ring]
    simp only [Complex.sub_re, Complex.one_re, Complex.star_def, Complex.conj_re]
    have below := (observation.coordinate_mem_openCriticalStrip_of_nontrivial nontrivial).2
    linarith)
  have rawHeat : mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) w = 0 := by
    change (Gammaℝ (2*w))⁻¹ * mellin (burnolGenericGaussianHeatPairTotal (value : BurnolL2)) w = 0 at heat
    exact (mul_eq_zero.mp heat).resolve_left (inv_ne_zero gamma)
  have bridge := burnolGenericHomogeneousGammaMellinBridge (evenFaceFourier q value) (barC c)
  have fourier := burnolGenericGaussianFourierHomogeneousIdentity value (barC c).value
  change Gammaℝ (barC c).value * burnolCompletedMellinEvaluator (barC c) (evenFaceFourier q value) =
    (1/2 : ℂ)*mellin (burnolGenericGaussianHeatPairTotal (fourierL2 (value : BurnolL2))) ((barC c).value/2) at bridge
  rw [fourier] at bridge
  have coordinate : (barC c).value = star observation.coordinate := rfl
  rw [coordinate, rawHeat, mul_zero] at bridge
  have read : burnolCompletedMellinEvaluator (barC c) (evenFaceFourier q value) = 0 :=
    (mul_eq_zero.mp bridge).resolve_left (Gammaℝ_ne_zero_of_re_pos (by
      simpa only [Complex.star_def, Complex.conj_re] using (lt_trans (by norm_num : (0 : ℝ)<1/2) half.down)))
  have riesz := burnolCompletedMellinRieszVector_readback (barC c) (evenFaceFourier q value)
  have paired := (evenFaceFourierEquiv q).inner_map_map (K (barC c))
    (evenFaceFourier q value)
  change inner ℂ (evenFaceFourier q (K (barC c))) (evenFaceFourier q (evenFaceFourier q value)) =
    inner ℂ (K (barC c)) (evenFaceFourier q value) at paired
  rw [evenFaceFourier_involutive q value] at paired
  rw [riesz, read] at paired
  change inner ℂ (fourierL2 (K (barC c) : BurnolL2))
    (quarterMellinFeatureCompletionEvenAdditive (selectedCoPoissonMuntzParameter observation)
      (state observation nontrivial source k)) = 0 at paired
  rw [state_raw observation nontrivial half.down source k, inner_smul_right] at paired
  exact (mul_eq_zero.mp paired).resolve_left (by norm_num)

/-- The different conjugate Fourier probe reads every actual original Pa R-power through the whole physical range. -/
theorem actual_conjugate_FK_Pa_power_low (p : BurnolPaAmbientCarrier)
    (inside : p ∈ burnolCompactCoPoissonClosedRange) (k : ℕ) (atMost : k ≤ m) :
    inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (rawIterate observation half.down k (p : BurnolL2)) = 0 := by
  let closed : ClosedSubmodule ℂ BurnolPaAmbientCarrier :=
    (⊥ : ClosedSubmodule ℂ ℂ).comap
      ((innerSL ℂ (fourierL2 (K (barC c) : BurnolL2))).comp
        ((rawIterate observation half.down k).comp
          (Submodule.subtypeL (evenBurnolClosedFace q).toSubmodule)))
  have member : p ∈ closed := (pa_le_closed (closed := closed) (by
    intro index
    obtain ⟨source,same⟩ := generator_raw (index := index)
    change inner ℂ (fourierL2 (K (barC c) : BurnolL2))
      (rawIterate observation half.down k (burnolCompactCoPoissonGenerator index : BurnolL2)) ∈ (⊥ : ClosedSubmodule ℂ ℂ)
    rw [same]
    simpa only [ClosedSubmodule.mem_bot] using compact_cross_fourier_zero observation nontrivial half source k atMost)) inside
  exact member

/-- All original Unit4 low fields, including j=m-1, are generated from the same conjugate Fourier zero. -/
theorem actual_conjugate_FK_unit_low (j : ℕ) (before : j < m) :
    inner ℂ (fourierL2 (K (barC c) : BurnolL2)) (unitPower observation half j) = 0 := by
  have split := congrArg (inner ℂ (fourierL2 (K (barC c) : BurnolL2)))
    (actual_Pa_power_split observation half (burnolPaCombApproximation 0) (burnolPaCombApproximation_mem 0) j)
  rw [inner_add_right,inner_smul_right,
    actual_conjugate_FK_Pa_power_low observation nontrivial half _ (burnolPaCombApproximation_mem 0) (j+1) (by omega),
    actual_conjugate_FK_Pa_power_low observation nontrivial half _ (burnolPaSourceCorrection_mem c _) j (by omega),
    zero_add] at split
  exact (mul_eq_zero.mp split.symm).resolve_left (comb_coefficient_ne observation nontrivial half)

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.ConjugateLow
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
