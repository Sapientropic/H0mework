import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiUDClockPayment
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.FirstCurrentPayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourcePhysicalKineticSquare
open SourceClockPhiCombinedScalePressure SourceClockPhiNormalizedScalarBudget
open SourceClockPhiMatchedDiffusionSource SourceClockPhiNativeMatchedSource FinitePhysicalSource
open MeasureTheory
open scoped InnerProductSpace
private abbrev A := combinedConjugate
private abbrev U := inverseVolumeAction
private abbrev D := combinedGenerator
private abbrev C := SourceScalarDoubleCurrent.bracket diagonalAction A
private abbrev n : ℝ := sourceTime 0
attribute [local irreducible] diagonalAction embed
private theorem n_positive : 0 < n := by
  change 0 < sourceTime 0
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem first_current_square (w : QuantumTest) :
    2*(sourcePair (A w) (C w)).re =
      (n/1152)*‖embed (A w)‖^2 + (576/n)*(sourcePair w (conditionalHamiltonianSquare w)).re -
      (n/1152)*‖embed (A w)-((1152/n:ℝ):ℂ) • embed (C w)‖^2 := by
  rw [actual_full_conditional_carre]
  have hc : 0 ≤ 1152/n := div_nonneg (by norm_num) n_positive.le
  have hs := norm_sub_sq (𝕜:=ℂ) (embed (A w)) (((1152/n:ℝ):ℂ) • embed (C w))
  simp only [inner_smul_right,RCLike.re_eq_complex_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,norm_smul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hc] at hs
  change 2*(inner ℂ (embed (A w)) (embed (C w))).re = _
  rw [hs]
  field_simp [n_positive.ne']
  ring

/-- The actual finite-clock UD debit pays the original normalized first-current A leg.
The full conditional current and both completed negative squares remain in the signed balance. -/
theorem actual_normalized_first_current_clock_payment
    (T : ℝ) (hT : 0 < T) (ξ η : ℝ)
    (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im ≠ 0) (g : diagonal.domain) :
    let w := normalizedState m ell F z hz g
    let f := normalizedForcing m ell F z hz g
    firstCurrentJointRemainder m ell F z hz g -
      (n/96)*(∫ s in (0:ℝ)..T, actualClockUDSquare s ξ η w) =
      (n/1152)*(clockPotential T hT w).re +
      (576/n)*(sourcePair w (conditionalHamiltonianSquare w)).re -
      (n/1152)*‖embed (A w)-((1152/n:ℝ):ℂ) • embed (C w)‖^2 +
      matchedField w + (432/n)*‖embed f‖^2 -
      (n/48)*‖embed (matchedTester w)+((144/n:ℝ):ℂ) • embed f‖^2 -
      (n/96)*‖embed (U (D w))‖^2 := by
  dsimp only
  have ht := (actual_finite_clock_UD_payment T hT ξ η (normalizedState m ell F z hz g)).2
  have hs := first_current_square (normalizedState m ell F z hz g)
  unfold firstCurrentJointRemainder
  dsimp only
  linear_combination (norm:=ring) hs - (n/1152)*ht
end LowEnergy.FirstCurrentPayer
