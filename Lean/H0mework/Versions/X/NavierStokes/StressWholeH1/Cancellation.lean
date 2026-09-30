import H0mework.Versions.X.NavierStokes.StressWholeH1.Approximation
import H0mework.Versions.X.NavierStokes.StressWholeH1.Pairing

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeWholeH1Cancellation

open Set Filter
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing NativeEndpointVelocityCarrier
open NativeCommonAdvectorAction NativeTimeJetCarrier NativeHigherTimeJets NativeConvectionFlux
open NativeWholeH1Mixed NativeWholeH1Approximation NativeWholeH1Pairing

noncomputable section

theorem gradient_project_tendsto (value : wholePhysical) (regular : H1 value) :
    Tendsto (fun radius => gradientValue (project radius value) (H1_project radius value)) atTop
      (𝓝 (gradientValue value regular)) := by
  have error : Tendsto (fun radius => gradientValue (value - project radius value)
      (H1_sub value _ regular (H1_project radius value))) atTop (𝓝 0) := by
    apply normSquare_tendsto_zero _ (fun radius => (2 * Real.pi) ^ 2 * gradientMass (value - project radius value))
      (fun radius => (gradientValue_norm_sq _ _).le)
    simpa only [mul_zero] using (difference_mass_tendsto value regular).const_mul ((2 * Real.pi) ^ 2)
  have result := (tendsto_const_nhds (x := gradientValue value regular)).sub error
  simp only [sub_zero] at result
  apply result.congr'
  apply Eventually.of_forall
  intro radius
  dsimp only
  rw [gradientValue_sub value (project radius value) regular (H1_project radius value)]
  abel

theorem row_real_inner (first last : ComplexCoordinateVector) :
    inner ℝ (euclideanCoordinateRow first) (euclideanCoordinateRow last) = complexCoordinateRealInner first last := by
  have realNorm := norm_add_sq_real (euclideanCoordinateRow first) (euclideanCoordinateRow last)
  have complexNorm := norm_add_sq (𝕜 := ℂ) (euclideanCoordinateRow first) (euclideanCoordinateRow last)
  change ‖euclideanCoordinateRow first + euclideanCoordinateRow last‖ ^ 2 =
    ‖euclideanCoordinateRow first‖ ^ 2 + 2 * (inner ℂ (euclideanCoordinateRow first) (euclideanCoordinateRow last)).re +
      ‖euclideanCoordinateRow last‖ ^ 2 at complexNorm
  rw [euclideanCoordinateRow_re_inner] at complexNorm
  linarith

theorem curlLift_velocity (F : Finset IntegerWavevector) (zero : 0 ∉ F) (value : physicalSpace F) :
    wholeBiotSavartVelocityState (curlLift F value.1) = value.1 := by
  apply lp.ext
  funext wave
  change finiteStateVelocityCoefficient (curlLift F value.1) wave = value.1 wave
  by_cases member : wave ∈ F
  · exact curlLift_reads F zero value.1 (physical_transverse value) wave member
  · simp [finiteStateVelocityCoefficient, curlLift, finiteComplexVorticityState_apply, member,
      physical_supported value wave member, biotSavartVelocityCoefficient]

theorem finite_cancellation (F : Finset IntegerWavevector) (zero : 0 ∉ F)
    (closed : FiniteModeNegClosed F) (nu : Viscosity) (first last : physicalSpace F) :
    (∑ wave ∈ F, complexCoordinateRealInner (last.1 wave)
      (projectedDivergenceCLM wave (mixedFlux first.1 last.1 wave))) = 0 := by
  have dissipated := cross_dissipation F zero closed nu (curlLift F first.1) last.1 last.1
    (physical_transverse last) (physical_transverse last)
    (physical_reality (fun {_} member => closed _ member) last)
    (physical_reality (fun {_} member => closed _ member) last)
  have action : velocityPair F last.1 (frozenOperator F nu (curlLift F first.1) last.1) =
      (∑ wave ∈ F, complexCoordinateRealInner (last.1 wave)
        (projectedDivergenceCLM wave (mixedFlux first.1 last.1 wave))) - nu.coeff * curlPair F last.1 last.1 := by
    rw [velocityPair, curlPair, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro wave member
    have nonzero : wave ≠ 0 := fun same => zero (same ▸ member)
    rw [operator_stress_row F nu (curlLift F first.1) last.1
      (fun k outside => by simp [curlLift, finiteComplexVorticityState_apply, outside])
      (physical_supported last) (physical_transverse last) wave member nonzero,
      curlLift_velocity F zero first, complexCoordinateRealInner_sub_right,
      complexCoordinateRealInner_real_smul_right,
      ← curl_pair_row wave nonzero _ _ (physical_transverse last wave member) (physical_transverse last wave member)]
    ring
  rw [action] at dissipated
  linarith

theorem projected_pairing (radius : ℕ) (first last : wholePhysical) :
    inner ℝ (negativeAction (project radius first) (project radius last)
      (H1_project radius first) (H1_project radius last))
      (gradientValue (project radius last) (H1_project radius last)) =
    ∑ wave ∈ modes radius, complexCoordinateRealInner ((restrict radius last).1 wave)
      (finiteRow radius first last wave) := by
  rw [lp.inner_eq_tsum]
  have paired (wave : NativeResolventCompactness.Wave) :
      inner ℝ (negativeAction (project radius first) (project radius last)
        (H1_project radius first) (H1_project radius last) wave)
        (gradientValue (project radius last) (H1_project radius last) wave) =
      complexCoordinateRealInner ((restrict radius last).1 wave.1) (finiteRow radius first last wave.1) := by
    change inner ℝ ((Real.sqrt (integerWaveViscousMultiplier wave.1))⁻¹ •
        euclideanCoordinateRow (row (project radius first) (project radius last) wave.1))
      (Real.sqrt (integerWaveViscousMultiplier wave.1) • euclideanCoordinateRow ((restrict radius last).1 wave.1)) = _
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_pos.mpr (multiplier_positive wave)).ne', one_mul,
      real_inner_comm]
    have same : row (project radius first) (project radius last) wave.1 = finiteRow radius first last wave.1 := by
      rw [row, project_whole, project_whole]
      rfl
    exact (row_real_inner _ _).trans (congrArg (complexCoordinateRealInner ((restrict radius last).1 wave.1)) same)
  simp_rw [paired]
  let density (wave : IntegerWavevector) := complexCoordinateRealInner ((restrict radius last).1 wave)
    (finiteRow radius first last wave)
  change (∑' wave : NativeResolventCompactness.Wave, density wave.1) = _
  have finite : (∑' wave : NativeResolventCompactness.Wave, density wave.1) =
      ∑ wave ∈ (modes radius).subtype (fun wave => wave ≠ 0), density wave.1 :=
    tsum_eq_sum (fun wave outside => by
    have excluded : wave.1 ∉ modes radius := by simpa only [Finset.mem_subtype] using outside
    dsimp only [density]
    rw [physical_supported _ _ excluded]
    simp [complexCoordinateRealInner])
  exact finite.trans (Finset.sum_subtype_of_mem density (fun wave member same => modes_zero radius (same ▸ member)))

/-- Whole self-pairing vanishes through the same finite convection and its strong negative-one limit. -/
theorem whole_cancellation (nu : Viscosity) (first last : wholePhysical) (firstH1 : H1 first) (lastH1 : H1 last) :
    inner ℝ (negativeAction first last firstH1 lastH1) (gradientValue last lastH1) = 0 := by
  have limit := (negativeAction_project_tendsto first last firstH1 lastH1).inner (𝕜 := ℝ)
    (gradient_project_tendsto last lastH1)
  have generated : ∀ radius,
      inner ℝ (negativeAction (project radius first) (project radius last)
        (H1_project radius first) (H1_project radius last))
        (gradientValue (project radius last) (H1_project radius last)) = 0 := by
    intro radius
    rw [projected_pairing]
    exact finite_cancellation (modes radius) (modes_zero radius) (modes_closed radius) nu _ _
  simp only [generated] at limit
  exact tendsto_nhds_unique limit tendsto_const_nhds

end
end SaturationMonoid.NavierStokes.NativeWholeH1Cancellation
