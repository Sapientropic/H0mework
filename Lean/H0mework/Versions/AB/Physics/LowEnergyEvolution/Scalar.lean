import H0mework.Versions.AB.Physics.LowEnergyEvolution.Fields

/-! The actual scalar Euler channel of the generated coupled field. All
momenta remain derivatives of the original holonomic configuration. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeConnectionActionVariation
open StageNineScalarVariation StageNineScalarPointwiseEquation
open StageNineDiracDualFormNativeScalarVariation Stage9C.Material.SpinPair
open SU7MotherGaugeTheory
open Response.Radial
open scoped Topology
noncomputable section

private theorem pairing_symmetric (u v : ScalarCoordinateCarrier) :
    scalarCoordinatePairingRe u v = scalarCoordinatePairingRe v u := by
  apply Finset.sum_congr rfl
  intro index _
  simp [Complex.mul_re]
  ring

private theorem pairing_zero_left (v : ScalarCoordinateCarrier) : scalarCoordinatePairingRe 0 v = 0 := by
  simp [scalarCoordinatePairingRe]

theorem Solution.scalar_kinetic_first {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : LorentzianIndex → ScalarCoordinateCarrier) :
    scalarGaugeConnectionKineticFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) variation =
      -flow.pointState point 5 / clock (flow.pointState point) *
        scalarCoordinatePairingRe (variation 0) direction := by
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  have hn : clock (flow.pointState point) ≠ 0 := ne_of_gt (clock_positive _ h)
  have ha : flow.pointState point 0 ≠ 0 := ne_of_gt h.1
  have covariant : holonomicScalarCovariantDerivative flow.configuration point =
      fun mu => (if mu = 0 then clock (flow.pointState point) * flow.pointState point 5 else 0) • direction :=
    funext (flow.scalar_covariant point inside)
  unfold scalarGaugeConnectionKineticFirstVariationDensity
  change (1/2:ℝ) * ∑ first, ∑ second,
    (lorentzianMetricOfCoframe (flow.configuration.coframe point))⁻¹ first second *
      (scalarCoordinatePairingRe _ _ + scalarCoordinatePairingRe _ _) = _
  rw [flow.coframe, diagonalCoframe_metric_inverse _ _ hn ha]
  simp only [scalarFrameRelativeCovariantDerivative, scalarFrameRelativeCoordinates_zeroChart,
    toContinuumPointField, covariant, scalarCoordinatePairingRe_real_smul_left,
    scalarCoordinatePairingRe_real_smul_right]
  simp [Fin.sum_univ_four, Matrix.diagonal_apply, pairing_symmetric direction (variation 0),
    show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  field_simp [hn]
  ring

theorem Solution.scalar_potential_first {initial : State} (flow : Solution initial)
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    scalarPotentialFirstVariation positiveSmoothUnifiedSource
      (toContinuumPointField flow.configuration point) variation =
      2 * flow.pointState point 4 * scalarCoordinatePairingRe variation direction := by
  unfold scalarPotentialFirstVariation frameRelativeScalarGradient
  change 2 * scalarCoordinateRealPairing (direction + flow.pointState point 4 • direction - direction)
    variation = _
  rw [add_sub_cancel_left]
  change 2 * scalarCoordinatePairingRe (flow.pointState point 4 • direction) variation = _
  rw [scalarCoordinatePairingRe_real_smul_left, pairing_symmetric direction variation]
  ring

theorem Solution.scalar_yukawa_first {initial : State} (flow : Solution initial)
    (point : BasePoint) (variation : ScalarCoordinateCarrier) :
    diracDualScalarYukawaFirstVariationDensity (toContinuumPointField flow.configuration point) variation = 0 := by
  unfold diracDualScalarYukawaFirstVariationDensity diracDualScalarYukawaVariationVector
  change (spinPairDual _ _ _).re = 0
  rw [spinPairDual_yukawa_annihilates]
  rfl

theorem Solution.scalar_algebraic {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : ScalarCoordinateCarrier) :
    diracDualScalarAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration variation point =
      scalarAlgebraic (flow.pointState point) * scalarCoordinatePairingRe variation direction := by
  unfold diracDualScalarAlgebraicDirectionalCoefficient
  rw [flow.scalar_kinetic_first point inside, flow.scalar_potential_first, flow.scalar_yukawa_first]
  have temporal : holonomicScalarVariationAlgebraicDirection flow.configuration variation point 0 = 0 := by
    change scalarMotherLieAction (SU7MotherLieAlgebra.p286LieBlockEmbed
      (gaugePotential (flow.pointState point 2) 0)) variation = 0
    simp [gaugePotential, p286LieBlockEmbed_zero, scalarMotherLieAction]
  rw [temporal]
  simp only [pairing_zero_left, mul_zero, zero_sub, add_zero]
  change |(flow.configuration.coframe point).det| * _ = _
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos
    (mul_pos (clock_positive _ h) (pow_pos h.1 3))]
  unfold scalarAlgebraic
  ring

theorem Solution.scalar_momentum {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : ScalarCoordinateCarrier) (mu : LorentzianIndex) :
    scalarDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation mu point =
      if mu = 0 then scalarMomentum (flow.pointState point) * scalarCoordinatePairingRe variation direction else 0 := by
  unfold scalarDifferentialMomentum
  rw [flow.scalar_kinetic_first point inside]
  change |(flow.configuration.coframe point).det| * _ = _
  have h : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos (mul_pos (clock_positive _ h) (pow_pos h.1 3))]
  by_cases same : mu = 0
  · simp only [same, if_true, scalarVariationDifferentialDirection]
    unfold scalarMomentum
    field_simp [ne_of_gt (clock_positive _ h)]
  · simp [scalarVariationDifferentialDirection, same, Ne.symm same, scalarCoordinatePairingRe]

theorem Solution.scalar_momentum_directional {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : ScalarCoordinateCarrier) (mu : LorentzianIndex) :
    fieldDirectionalDerivative
      (scalarDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation mu)
      point mu =
      if mu = 0 then scalarAlgebraic (flow.pointState point) * scalarCoordinatePairingRe variation direction else 0 := by
  have near : ∀ᶠ p : BasePoint in 𝓝 point, p 0 ∈ Set.Ioo (-flow.radius) flow.radius :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt
      (isOpen_Ioo.mem_nhds inside)
  by_cases same : mu = 0
  · subst mu
    rw [if_pos rfl]
    have derivative := ((flow.scalar_momentum_derivative (point 0) inside).mul_const
      (scalarCoordinatePairingRe variation direction)).hasFDerivAt.comp point
        (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).hasFDerivAt
    have equal : scalarDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation 0 =ᶠ[𝓝 point]
        (fun p : BasePoint => scalarMomentum (flow.pointState p) * scalarCoordinatePairingRe variation direction) := by
      filter_upwards [near] with p hp
      simpa using flow.scalar_momentum p hp variation 0
    have actual := derivative.congr_of_eventuallyEq equal
    unfold fieldDirectionalDerivative
    rw [actual.fderiv]
    change (coordinateDirection 0) 0 *
      (scalarAlgebraic (flow.pointState point) * scalarCoordinatePairingRe variation direction) = _
    simp [coordinateDirection]
  · rw [if_neg same]
    have equal : scalarDifferentialMomentum positiveSmoothUnifiedSource flow.configuration variation mu =ᶠ[𝓝 point]
        (fun _ : BasePoint => (0 : ℝ)) := by
      filter_upwards [near] with p hp
      simpa [same] using flow.scalar_momentum p hp variation mu
    have actual := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) point).congr_of_eventuallyEq equal
    unfold fieldDirectionalDerivative
    rw [actual.fderiv]
    simp

theorem Solution.scalar_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration variation point = 0 := by
  unfold diracDualScalarEulerLagrangeDirectionalCoefficient scalarDifferentialMomentumDivergence
  rw [flow.scalar_algebraic point inside]
  simp_rw [flow.scalar_momentum_directional point inside variation]
  simp

theorem source_scalar_euler_zero (parameter : ℝ) (point : BasePoint)
    (inside : point 0 ∈ Set.Ioo (-(solution parameter).radius) (solution parameter).radius)
    (variation : ScalarCoordinateCarrier) :
    diracDualScalarEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
      (solution parameter).configuration variation point = 0 :=
  (solution parameter).scalar_euler_zero point inside variation

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
