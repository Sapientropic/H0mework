import H0mework.Physics.LowEnergyEvolution.Spinor

/-! The original primal Dirac vector consumes the same generated connection
and both amplitude derivatives. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineCoframeFirstJet StageNineCoframeLocalDifferentiability
open StageNineLorentzConnectionVariation StageNineLorentzConnectionVariationDensity
open StageNineMatterVariation StageNineMatterCovariantDerivativeAffine StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualFormNativeConjugateMatterVariation StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracDualYukawaSpinJurisdiction StageNineDynamicBreakingVacuum
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra SU7MotherGaugeTheory SU7ExteriorBreakingYukawa SU7ExteriorMatterRestriction
noncomputable section

theorem sourceColorDiracMatter_add (first second : DiracSpinorIndex → Fin 2 → ℂ) :
    sourceColorDiracMatter (first + second) = sourceColorDiracMatter first + sourceColorDiracMatter second := by
  funext spin
  simp [sourceColorDiracMatter, add_smul, Finset.sum_add_distrib]

theorem spinPairMatter_damped (damping rate : ℝ) (u v : ℂ) :
    spinPairMatter (((damping : ℂ)+Complex.I*(rate : ℂ))*u)
      (((damping : ℂ)-Complex.I*(rate : ℂ))*v) =
      (damping : ℂ) • spinPairMatter u v +
        spinPairMatter (Complex.I*(rate : ℂ)*u) (-Complex.I*(rate : ℂ)*v) := by
  unfold spinPairMatter
  rw [← sourceColorDiracMatter_smul, ← sourceColorDiracMatter_add]
  congr 1
  funext spin state
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases spin <;> fin_cases state <;>
    simp [spinPairCoefficients] <;> ring

theorem boostSpinLift_time (velocity : ℝ) : diracSpinConnectionLift (boostConnection velocity) 0 = 0 := by
  simp [diracSpinConnectionLift, loweredLorentzConnectionCoefficient, boostConnection]

theorem homogeneousSpinLift_time (spin : ℝ) : diracSpinConnectionLift (homogeneousConnection spin) 0 = 0 := by
  simp only [diracSpinConnectionLift, homogeneousConnection,
    loweredLorentzConnectionCoefficient_ofBivectorOneForm]
  simp [homogeneousContorsion, Fin.sum_univ_six]

set_option maxHeartbeats 1000000 in
theorem boostSpinLift_spatial (velocity : ℝ) (axis : Fin 3) :
    diracGamma axis.succ * diracSpinConnectionLift (boostConnection velocity) axis.succ =
      ((velocity : ℂ)/2) • diracGamma 0 := by
  ext row col
  fin_cases axis <;> fin_cases row <;> fin_cases col <;>
    simp [diracSpinConnectionLift, loweredLorentzConnectionCoefficient, boostConnection,
      lorentzBivectorFirst, lorentzBivectorSecond, minkowskiInternalSign,
      diracGamma, diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
      Matrix.mul_apply, Fin.sum_univ_six, Fin.sum_univ_four] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem boostKinetic (velocity : ℝ) (axis : Fin 3) (matter : DiracExteriorMatterCarrier) :
    Complex.I • diracMatrixMatterAction (diracGamma axis.succ)
      (diracMatrixMatterAction (diracSpinConnectionLift (boostConnection velocity) axis.succ) matter) =
      (Complex.I*(velocity : ℂ)/2) • diracMatrixMatterAction (diracGamma 0) matter := by
  rw [← LinearMap.comp_apply, ← diracMatrixMatterAction_mul, boostSpinLift_spatial,
    coframeDiracMatrixMatterAction_smul_matrix, smul_smul]
  congr 1
  ring

theorem Solution.matter_covariant_time {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    holonomicMatterCovariantDerivative flow.configuration point 0 =
      spinPairMatter (spinVelocity 1 (flow.pointState point)) (spinVelocity (-1) (flow.pointState point)) := by
  unfold holonomicMatterCovariantDerivative
  rw [flow.matter_derivative point inside, flow.connection_generated point inside]
  simp only [ite_true, diracSpinConnectionLift_add, boostSpinLift_time,
    homogeneousSpinLift_time, add_zero, diracMatrixMatterAction_zero_matrix]
  have gaugeZero : flow.configuration.gaugeConnection point 0 = 0 := rfl
  rw [gaugeZero, p286LieBlockEmbed_zero, diracExteriorMotherLieAction_zero_matrix, add_zero]

theorem Solution.matter_covariant_spatial {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (axis : Fin 3) :
    holonomicMatterCovariantDerivative flow.configuration point axis.succ =
      diracMatrixMatterAction (diracSpinConnectionLift (boostConnection (flow.pointState point 1)) axis.succ)
        (flow.configuration.matter point) +
      ((((contorsion (flow.pointState point)-flow.pointState point 2 : ℝ) : ℂ)/2) •
        diracMatrixMatterAction (spinRotation axis) (flow.configuration.matter point)) := by
  unfold holonomicMatterCovariantDerivative
  rw [flow.matter_derivative point inside, flow.connection_generated point inside]
  simp only [Fin.succ_ne_zero, if_false, zero_add, diracSpinConnectionLift_add,
    coframeDiracMatrixMatterAction_add_matrix, add_assoc]
  rw [flow.matter]
  have gauge : flow.configuration.gaugeConnection point axis.succ =
      flow.pointState point 2 • sourceColorP286Generator axis := by fin_cases axis <;> rfl
  rw [gauge, spinPair_spatialCovariantTerm]

theorem Solution.matter_time_kinetic {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } 0)
      (holonomicMatterCovariantDerivative flow.configuration point 0) =
      (Complex.I * (dilutionRate (flow.pointState point) : ℂ) / (clock (flow.pointState point) : ℂ)) •
        diracMatrixMatterAction (diracGamma 0) (flow.configuration.matter point) +
      ((generator (flow.pointState point) 6 : ℂ)/(clock (flow.pointState point) : ℂ)) •
        spinPairMatter (spinAmplitude (-1) (flow.pointState point)) (spinAmplitude 1 (flow.pointState point)) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  rw [flow.coframe, diagonalInverseGamma _ _ (ne_of_gt (clock_positive _ admissible))
    (ne_of_gt admissible.1), flow.matter_covariant_time point inside, flow.matter]
  simp only [ite_true, spinVelocity, Complex.ofReal_one, Complex.ofReal_neg,
    one_mul, neg_mul]
  rw [← sub_eq_add_neg]
  rw [spinPairMatter_damped]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), coframeDiracMatrixMatterAction_smul_matrix,
    map_add, map_smul, smul_add]
  push_cast
  congr 1
  · module
  · rw [smul_comm, spinPair_temporalKinetic]
    module

theorem Solution.matter_spatial_kinetic {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) (axis : Fin 3) :
    Complex.I • diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := flow.configuration.coframe point, derivative := 0 } axis.succ)
      (holonomicMatterCovariantDerivative flow.configuration point axis.succ) =
      (Complex.I * (flow.pointState point 1 : ℂ)/(2*(flow.pointState point 0 : ℂ))) •
        diracMatrixMatterAction (diracGamma 0) (flow.configuration.matter point) +
      (-((contorsion (flow.pointState point)-flow.pointState point 2 : ℝ) : ℂ)/(2*(flow.pointState point 0 : ℂ))) •
        spinPairMatter (spinAmplitude (-1) (flow.pointState point)) (spinAmplitude 1 (flow.pointState point)) := by
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  have rotational := spinPair_spatialKinetic (contorsion (flow.pointState point)) (flow.pointState point 2)
    axis (spinAmplitude 1 (flow.pointState point)) (spinAmplitude (-1) (flow.pointState point))
  rw [spinPair_spatialCovariantTerm] at rotational
  rw [flow.coframe, diagonalInverseGamma _ _ (ne_of_gt (clock_positive _ admissible))
    (ne_of_gt admissible.1), flow.matter_covariant_spatial point inside]
  simp only [Fin.succ_ne_zero, if_false, RCLike.real_smul_eq_coe_smul (K := ℂ),
    coframeDiracMatrixMatterAction_smul_matrix]
  rw [smul_comm]
  simp only [map_add, smul_add, boostKinetic]
  rw [flow.matter, rotational]
  push_cast
  module

theorem Solution.kinetic_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius) :
    generatedContinuumMatterKineticVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0 := by
  unfold generatedContinuumMatterKineticVector matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [matterDerivativeFrameRelative_zeroChart, toContinuumPointField]
  rw [Finset.smul_sum, Fin.sum_univ_succ, flow.matter_time_kinetic point inside]
  simp_rw [flow.matter_spatial_kinetic point inside]
  rw [Fin.sum_univ_three]
  have admissible : Admissible (flow.pointState point) := flow.admissible _ inside
  have lapseNonzero : (clock (flow.pointState point) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (clock_positive _ admissible))
  have spatialNonzero : (flow.pointState point 0 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt admissible.1)
  have damping : (Complex.I*(dilutionRate (flow.pointState point) : ℂ)/(clock (flow.pointState point) : ℂ)) =
      -3*(Complex.I*(flow.pointState point 1 : ℂ)/(2*(flow.pointState point 0 : ℂ))) := by
    unfold dilutionRate
    push_cast
    field_simp
  have frequency : (generator (flow.pointState point) 6 : ℂ)/(clock (flow.pointState point) : ℂ) =
      3*((contorsion (flow.pointState point)-flow.pointState point 2 : ℝ) : ℂ)/(2*(flow.pointState point 0 : ℂ)) := by
    simp only [generator]
    push_cast
    field_simp
  rw [damping, frequency]
  module

theorem radialYukawa_zero (amplitude : ℝ) (u v : ℂ) :
    diracDualRightChiralYukawaAction
      (scalarCoordinateEquiv.symm (Response.Radial.direction + amplitude • Response.Radial.direction))
      (spinPairMatter u v) = 0 := by
  have vacuum : diracDualRightChiralYukawaAction
      (sourceGeneratedVacuumBase positiveSmoothUnifiedSource) (spinPairMatter u v) = 0 := by
    unfold diracDualRightChiralYukawaAction
    rw [LinearMap.comp_apply]
    unfold spinPairMatter
    funext spin
    change exteriorYukawaInternalAction (sourceGeneratedVacuumBase positiveSmoothUnifiedSource)
      (∑ other, rightChiralityProjector spin other • sourceColorDiracMatter (spinPairCoefficients u v) other) = 0
    simp only [sourceColorDiracMatter, map_sum, map_smul,
      sourceColorDoublet_internalYukawa_zero, smul_zero, Finset.sum_const_zero]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [map_add, map_smul]
  simp only [Response.Radial.direction, sourceGeneratedVacuumCoordinates, scalarCoordinateEquiv.symm_apply_apply,
    diracDualRightChiralYukawaAction_add, diracDualRightChiralYukawaAction_smul,
    LinearMap.add_apply, LinearMap.smul_apply, vacuum, smul_zero, add_zero]

theorem Solution.yukawa_zero {initial : State} (flow : Solution initial) (point : BasePoint) :
    generatedContinuumDiracDualYukawaVector positiveSmoothUnifiedSource 0 point
      (toContinuumPointField flow.configuration point) = 0 := by
  unfold generatedContinuumDiracDualYukawaVector
  simp only [toContinuumPointField, scalarFrameRelativeCoordinates_zeroChart, matterFrameRelative_zeroChart]
  rw [flow.matter]
  exact radialYukawa_zero _ _ _

theorem Solution.primal_euler_zero {initial : State} (flow : Solution initial)
    (point : BasePoint) (inside : point 0 ∈ Set.Ioo (-flow.radius) flow.radius)
    (variation : MatterCoordinateCarrier) :
    diracDualConjugateMatterDirectionalCoefficient positiveSmoothUnifiedSource flow.configuration variation point = 0 := by
  unfold diracDualConjugateMatterDirectionalCoefficient generatedContinuumDiracDualMatterVector
  rw [flow.kinetic_zero point inside, flow.yukawa_zero]
  simp

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution
