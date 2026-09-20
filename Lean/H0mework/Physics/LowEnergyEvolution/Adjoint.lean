import H0mework.Physics.LowEnergyEvolution.Dirac

/-! The independent linear dual obeys the original variational equation,
including the derivative of the moving volume and inverse coframe. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open StageNineLorentzConnectionVariation StageNineLorentzConnectionVariationDensity
open StageNineMatterVariation StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeMatterVariation StageNineMatterPointwiseEquation
open StageNineDiracDualYukawaSpinJurisdiction Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open StageNineDynamicBreakingVacuum SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open scoped Topology
noncomputable section

def sourceDual (x : State) : Module.Dual ℂ DiracExteriorMatterCarrier :=
  spinPairDual ((spinScale : ℂ)*spinAmplitude 1 x) ((spinScale : ℂ)*spinAmplitude (-1) x)

def dualTime (x : State) (test : DiracExteriorMatterCarrier) : ℂ :=
  sourceDual x (Complex.I • diracMatrixMatterAction (diracGamma 0) test)

def dualSwap (x : State) (test : DiracExteriorMatterCarrier) : ℂ :=
  spinPairDual ((spinScale : ℂ)*spinAmplitude (-1) x) ((spinScale : ℂ)*spinAmplitude 1 x) test

def adjointAlgebraic (x : State) (test : DiracExteriorMatterCarrier) : ℝ :=
  (3*clock x*(x 0)^2/2) * (((x 1 : ℂ)*dualTime x test -
    ((contorsion x-x 2 : ℝ) : ℂ)*dualSwap x test).re)

theorem spinPairDual_damped (damping rate : ℝ) (p q : ℂ) (test : DiracExteriorMatterCarrier) :
    spinPairDual (((damping : ℂ)+Complex.I*(rate : ℂ))*p)
      (((damping : ℂ)-Complex.I*(rate : ℂ))*q) test =
      (damping : ℂ)*spinPairDual p q test +
        spinPairDual (Complex.I*(rate : ℂ)*p) (-Complex.I*(rate : ℂ)*q) test := by
  simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem Solution.dualTime_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius) (test : DiracExteriorMatterCarrier) :
    HasDerivAt (fun t => dualTime (flow.curve t) test)
      ((dilutionRate (flow.curve time) : ℂ)*dualTime (flow.curve time) test -
        (generator (flow.curve time) 6 : ℂ)*dualSwap (flow.curve time) test) time := by
  have derivative := spinPairDual_derivative
    ((flow.spinAmplitude_derivative 1 time inside).const_mul (spinScale : ℂ))
    ((flow.spinAmplitude_derivative (-1) time inside).const_mul (spinScale : ℂ))
    (Complex.I • diracMatrixMatterAction (diracGamma 0) test)
  convert derivative using 1 <;> first | rfl | skip
  have upper : (spinScale : ℂ)*spinVelocity 1 (flow.curve time) =
      ((dilutionRate (flow.curve time) : ℂ)+Complex.I*(generator (flow.curve time) 6 : ℂ))*
        ((spinScale : ℂ)*spinAmplitude 1 (flow.curve time)) := by simp [spinVelocity]; ring
  have lower : (spinScale : ℂ)*spinVelocity (-1) (flow.curve time) =
      ((dilutionRate (flow.curve time) : ℂ)-Complex.I*(generator (flow.curve time) 6 : ℂ))*
        ((spinScale : ℂ)*spinAmplitude (-1) (flow.curve time)) := by simp [spinVelocity]; ring
  rw [upper, lower, spinPairDual_damped, spinPairDual_temporalKinetic]
  dsimp [dualTime, sourceDual, dualSwap]
  ring

private theorem Solution.adjoint_kinetic_spatial {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : MatterCoordinateCarrier) (axis : Fin 3) :
    flow.configuration.conjugateMatter point (Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } axis.succ)
      (holonomicMatterVariationAlgebraicDirection flow.configuration test point axis.succ)) =
      ((flow.pointState point 1 : ℂ)/(2*(flow.pointState point 0 : ℂ)))*
        dualTime (flow.pointState point) (matterCoordinateEquiv.symm test) -
      (((contorsion (flow.pointState point)-flow.pointState point 2 : ℝ) : ℂ)/(2*(flow.pointState point 0 : ℂ)))*
        dualSwap (flow.pointState point) (matterCoordinateEquiv.symm test) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  unfold holonomicMatterVariationAlgebraicDirection
  rw [flow.coframe, flow.connection_generated point inside,
    diagonalInverseGamma _ _ (ne_of_gt (clock_positive _ admissible)) (ne_of_gt admissible.1)]
  have gauge : flow.configuration.gaugeConnection point axis.succ =
      flow.pointState point 2 • sourceColorP286Generator axis := by fin_cases axis <;> rfl
  rw [gauge, flow.dual]
  simp only [Fin.succ_ne_zero, if_false, diracSpinConnectionLift_add,
    coframeDiracMatrixMatterAction_add_matrix, add_assoc,
    RCLike.real_smul_eq_coe_smul (K := ℂ), coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm]
  simp only [map_add, smul_add, boostKinetic, map_smul, smul_eq_mul]
  have rotational := spinPairDual_spatialKinetic (contorsion (flow.pointState point)) (flow.pointState point 2)
    axis ((spinScale : ℂ)*spinAmplitude 1 (flow.pointState point))
    ((spinScale : ℂ)*spinAmplitude (-1) (flow.pointState point)) (matterCoordinateEquiv.symm test)
  dsimp [dualTime, sourceDual, dualSwap]
  simp only [map_add, map_smul, smul_eq_mul] at rotational ⊢
  push_cast at rotational ⊢
  linear_combination ((flow.pointState point 0 : ℂ)⁻¹)*rotational

theorem Solution.adjoint_algebraic {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : MatterCoordinateCarrier) :
    diracDualMatterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration test point =
      adjointAlgebraic (flow.pointState point) (matterCoordinateEquiv.symm test) := by
  have temporal : holonomicMatterVariationAlgebraicDirection flow.configuration test point 0 = 0 := by
    unfold holonomicMatterVariationAlgebraicDirection
    rw [flow.connection_generated point inside]
    simp only [diracSpinConnectionLift_add, boostSpinLift_time, homogeneousSpinLift_time, add_zero,
      diracMatrixMatterAction_zero_matrix, zero_add]
    change diracExteriorMotherLieAction (p286LieBlockEmbed (gaugePotential (flow.pointState point 2) 0)) _ = 0
    simp [gaugePotential, p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix]
  unfold diracDualMatterAlgebraicDirectionalCoefficient diracDualMatterAlgebraicVariationVector
    diracDualMatterFieldVariationVector matterCovariantDerivativeVariationVector matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField, map_add]
  have yukawa : flow.configuration.conjugateMatter point
      (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm (flow.configuration.scalar point))
        (matterCoordinateEquiv.symm test)) = 0 := by
    rw [flow.dual, spinPairDual_yukawa_annihilates]
  rw [yukawa, add_zero, Finset.smul_sum, map_sum, Fin.sum_univ_succ, temporal]
  simp only [map_zero, smul_zero, zero_add]
  simp_rw [flow.adjoint_kinetic_spatial point inside test]
  rw [Fin.sum_univ_three]
  change |(flow.configuration.coframe point).det| * _ = _
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos
    (mul_pos (clock_positive _ admissible) (pow_pos admissible.1 3))]
  have realDivision (r a : ℝ) : (r : ℂ)/(2*(a : ℂ)) = ((r/(2*a) : ℝ) : ℂ) := by
    push_cast
    rfl
  simp only [realDivision, adjointAlgebraic, Complex.add_re, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  field_simp [ne_of_gt admissible.1]
  ring

private theorem realGammaPair (factor : ℝ) (dual : Module.Dual ℂ DiracExteriorMatterCarrier)
    (gamma : DiracMatrix) (test : DiracExteriorMatterCarrier) :
    (dual (Complex.I • diracMatrixMatterAction (factor • gamma) test)).re =
      factor * (dual (Complex.I • diracMatrixMatterAction gamma test)).re := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), coframeDiracMatrixMatterAction_smul_matrix,
    map_smul, smul_eq_mul]
  simp [Complex.mul_re, Complex.mul_im]

def adjointMomentum (mu : LorentzianIndex) (x : State) (test : DiracExteriorMatterCarrier) : ℝ :=
  (if mu = 0 then (x 0)^3 else clock x*(x 0)^2) *
    (sourceDual x (Complex.I • diracMatrixMatterAction (diracGamma mu) test)).re

theorem Solution.adjoint_momentum {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : MatterCoordinateCarrier) (mu : LorentzianIndex) :
    matterDifferentialMomentum positiveSmoothUnifiedSource flow.configuration test mu point =
      adjointMomentum mu (flow.pointState point) (matterCoordinateEquiv.symm test) := by
  unfold matterDifferentialMomentum matterDifferentialVariationVector
  simp only [toContinuumPointField]
  change |(flow.configuration.coframe point).det| * _ = _
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalCoframe_det, abs_of_pos
    (mul_pos (clock_positive _ admissible) (pow_pos admissible.1 3)),
    diagonalInverseGamma _ _ (ne_of_gt (clock_positive _ admissible)) (ne_of_gt admissible.1), realGammaPair,
    flow.dual]
  unfold adjointMomentum sourceDual
  by_cases temporal : mu = 0
  · simp only [if_pos temporal]
    field_simp [ne_of_gt (clock_positive _ admissible)]
  · simp only [if_neg temporal]
    field_simp [ne_of_gt admissible.1]

theorem Solution.adjoint_momentum_temporal_derivative {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius) (test : DiracExteriorMatterCarrier) :
    HasDerivAt (fun t => adjointMomentum 0 (flow.curve t) test)
      (adjointAlgebraic (flow.curve time) test) time := by
  have real := Complex.reCLM.hasFDerivAt.comp_hasDerivAt time (flow.dualTime_derivative time inside test)
  have derivative := ((flow.coordinate_derivative time inside 0).pow 3).mul real
  convert derivative using 1 <;> first | rfl | skip
  simp only [adjointAlgebraic, Complex.reCLM_apply, Function.comp_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  dsimp [dilutionRate, generator]
  have spatialNonzero := ne_of_gt (flow.admissible time inside).1
  ring_nf
  field_simp [spatialNonzero]
  ring

theorem Solution.adjoint_momentum_differentiable {initial : State} (flow : Solution initial)
    (time : ℝ) (inside : time ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : DiracExteriorMatterCarrier) (mu : LorentzianIndex) :
    DifferentiableAt ℝ (fun t => adjointMomentum mu (flow.curve t) test) time := by
  have scale := (flow.coordinate_derivative time inside 0).differentiableAt
  have lapse := (flow.clock_derivative time inside).differentiableAt
  have dual := spinPairDual_derivative
    ((flow.spinAmplitude_derivative 1 time inside).const_mul (spinScale : ℂ))
    ((flow.spinAmplitude_derivative (-1) time inside).const_mul (spinScale : ℂ))
    (Complex.I • diracMatrixMatterAction (diracGamma mu) test)
  have real := (Complex.reCLM.hasFDerivAt.comp_hasDerivAt time dual).differentiableAt
  unfold adjointMomentum sourceDual
  by_cases temporal : mu = 0
  · simp only [if_pos temporal]
    exact (scale.pow 3).mul real
  · simp only [if_neg temporal]
    exact (lapse.mul (scale.pow 2)).mul real

theorem Solution.adjoint_momentum_directional {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : MatterCoordinateCarrier) (mu : LorentzianIndex) :
    fieldDirectionalDerivative
      (matterDifferentialMomentum positiveSmoothUnifiedSource flow.configuration test mu) point mu =
      if mu = 0 then adjointAlgebraic (flow.pointState point) (matterCoordinateEquiv.symm test) else 0 := by
  have near : ∀ᶠ p : BasePoint in 𝓝 point, p 0 ∈ Set.Ioo (-flow.radius) flow.radius :=
    (EuclideanSpace.proj (0 : LorentzianIndex) : BasePoint →L[ℝ] ℝ).continuous.continuousAt
      (isOpen_Ioo.mem_nhds inside)
  have equal : matterDifferentialMomentum positiveSmoothUnifiedSource flow.configuration test mu =ᶠ[𝓝 point]
      (fun p : BasePoint => adjointMomentum mu (flow.curve (p 0)) (matterCoordinateEquiv.symm test)) := by
    filter_upwards [near] with p hp
    exact flow.adjoint_momentum p hp test mu
  unfold fieldDirectionalDerivative
  rw [equal.fderiv_eq]
  by_cases temporal : mu = 0
  · subst mu
    exact time_fderiv_apply _ _ point (flow.adjoint_momentum_temporal_derivative (point 0) inside _) 0
  · rw [time_fderiv_apply _ _ point
      (flow.adjoint_momentum_differentiable (point 0) inside _ mu).hasDerivAt mu]
    simp only [if_neg temporal]

theorem Solution.adjoint_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (test : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration test point = 0 := by
  unfold diracDualMatterEulerLagrangeDirectionalCoefficient matterDifferentialMomentumDivergence
  rw [flow.adjoint_algebraic point inside]
  simp_rw [flow.adjoint_momentum_directional point inside test]
  simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
