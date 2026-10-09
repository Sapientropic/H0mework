import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCompleteOrbit

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCompleteOrbit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineDiracDualFormNativeMotherAction StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineDynamicBreakingVacuum
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativeOriginPhaseWard
open PreparationPhysicalPhaseGaugeRealization PreparationCoordinates
open SourcePropagationNativeActionHessian PhysicalEMGaugeRealization ActualEMCarrierOwn
open SourceQuantumScalarChart DiracExteriorMatterAction
open PreparationVacuumNativeFieldInjection PreparationVacuumOriginalGreenFeedback
open CanonicalGradedSpatialSource
open scoped Matrix BigOperators

def originAuxiliaryWeight : ℝ := (1/5) * Real.sqrt 2 * Real.sqrt 15

/-- All289 endpoint coordinates, including independent matter/dual and gauge auxiliaries. -/
theorem native_origin_coordinates :
    sourceNativeOriginReal 0 =
      sourceNativeOriginGaugeWeight • (Pi.single 21 1 - Pi.single 34 1) +
      Pi.single 88 1 + Pi.single 94 1 -
      spinScale • (Pi.single 112 1 + Pi.single 118 1) +
      originAuxiliaryWeight • (Pi.single 217 1 - Pi.single 230 1) := by
  funext j
  rw [sourceNativeOriginReal, sourceNativeOriginAction_generated]
  by_cases support : j = 21 ∨ j = 34 ∨ j = 88 ∨ j = 94 ∨
      j = 112 ∨ j = 118 ∨ j = 217 ∨ j = 230
  · rcases support with h | h | h | h | h | h | h | h
    all_goals subst j
    all_goals norm_num [sourceNativeOriginActionTerms, sourceMatrix, SourceTerm.matrix,
      Powers.value, coefficientValue, Matrix.single_apply, Fin.ext_iff, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
      rootTwo, rootFifteen, sourceNativeOriginGaugeWeight, originAuxiliaryWeight, spinScale,
      QuadraticAlgebra.re_one, QuadraticAlgebra.im_one, QuadraticAlgebra.re_zero,
      QuadraticAlgebra.im_zero]
  · push Not at support
    rcases support with ⟨h21, h34, h88, h94, h112, h118, h217, h230⟩
    simp [sourceNativeOriginActionTerms, sourceMatrix, SourceTerm.matrix,
      Powers.value, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      h21, h34, h88, h94, h112, h118, h217, h230,
      Ne.symm h21, Ne.symm h34, Ne.symm h88, Ne.symm h94, Ne.symm h112,
      Ne.symm h118, Ne.symm h217, Ne.symm h230]

theorem native_origin_auxiliary_slots (pair : Fin 6) (a : Fin 12) :
    fieldGaugeB (sourceNativeOriginReal 0) pair a =
      (if pair = 0 ∧ a = 0 then originAuxiliaryWeight else 0) -
      (if pair = 1 ∧ a = 1 then originAuxiliaryWeight else 0) := by
  rw [native_origin_coordinates]
  fin_cases pair <;> fin_cases a <;>
    norm_num [fieldGaugeB, gaugeBSlot, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      Pi.single_apply, Fin.ext_iff]

theorem native_origin_gravity_auxiliaries :
    fieldGravityB (sourceNativeOriginReal 0) = 0 ∧
      fieldMultiplier (sourceNativeOriginReal 0) = 0 := by
  rw [native_origin_coordinates]
  constructor
  · funext pair a
    fin_cases pair <;> fin_cases a <;>
      norm_num [fieldGravityB, gravitySlot, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.single_apply, Fin.ext_iff]
  · funext pair a
    fin_cases pair <;> fin_cases a <;>
      norm_num [fieldMultiplier, multiplierSlot, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, Pi.single_apply, Fin.ext_iff]

theorem native_origin_auxiliary_scale :
    2 * originAuxiliaryWeight = gaugeScale^2 / (sourceCoupling * lapse) := by
  let radical : ℝ := Real.sqrt 2 * Real.sqrt 15
  have radicalSquare : radical^2 = 30 := by
    dsimp only [radical]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 15)]
    norm_num
  have radicalPositive : 0 < radical :=
    mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have clock : lapse = (3/25) * radical := by
    nlinarith [lapse_pos, lapse_sq]
  rw [sourceCoupling_eq, clock]
  have gaugeSquare : gaugeScale^2 = 18/25 := by
    rw [gaugeScale, div_pow, mul_pow, spinScale_sq]
    norm_num
  have weight : originAuxiliaryWeight = (1/5) * radical := by
    dsimp only [originAuxiliaryWeight, radical]
    ring
  rw [gaugeSquare, weight]
  have nonzero := radicalPositive.ne'
  field_simp [nonzero]
  nlinarith

private theorem em_color_bracket (i : Fin 3) :
    p286LieBracket emDirection (sourceColorP286Generator i) =
      -p286LieBracket (sourceColorP286Generator 2) (sourceColorP286Generator i) := by
  have hyper : p286LieBracket Stage10.HyperchargeResponse.chargeDirection
      (sourceColorP286Generator i) = 0 := by
    apply Prod.ext
    · apply Subtype.ext
      simp [p286LieBracket, Stage10.HyperchargeResponse.chargeDirection, suLieBracket]
    · apply Prod.ext
      · apply Subtype.ext
        simp [p286LieBracket, Stage10.HyperchargeResponse.chargeDirection, suLieBracket]
      · simp [p286LieBracket]
  have split : emDirection = (-1:ℝ) • sourceColorP286Generator 2 +
      (-1/2:ℝ) • Stage10.HyperchargeResponse.chargeDirection := by
    unfold emDirection
    module
  rw [split, p286LieBracket_add_left, p286LieBracket_smul_left,
    p286LieBracket_smul_left, hyper, smul_zero, add_zero]
  module

theorem native_origin_auxiliary_orbit (point : BasePoint) (pair : Fin 6) :
    gaugeBInsertion (sourceNativeOriginReal 0) pair = emOrbit.gaugeAuxiliary point pair := by
  have row : (∑ a : Fin 12, fieldGaugeB (sourceNativeOriginReal 0) pair a • originalUnit a) =
      if pair = 0 then originAuxiliaryWeight • originalUnit 0
      else if pair = 1 then -originAuxiliaryWeight • originalUnit 1 else 0 := by
    simp_rw [native_origin_auxiliary_slots]
    fin_cases pair <;> simp
  have scaled (c : ℝ) (v : NativeLie) :
      p286CoordinateEquiv.symm (c • v) = c • p286CoordinateEquiv.symm v := by
    exact p286CoordinateEquiv.symm.toLinearMap.map_smul c v
  have converted : gaugeBInsertion (sourceNativeOriginReal 0) pair =
      if pair = 0 then originAuxiliaryWeight • ((2:ℝ) • sourceColorP286Generator 1)
      else if pair = 1 then -originAuxiliaryWeight • ((2:ℝ) • sourceColorP286Generator 0) else 0 := by
    unfold gaugeBInsertion
    rw [row]
    by_cases p0 : pair = 0
    · simp only [if_pos p0]
      exact (scaled originAuxiliaryWeight (originalUnit 0)).trans
        (congrArg (fun x : P286LieBlockData => originAuxiliaryWeight • x) sourceNativeOrigin_unit_zero)
    · by_cases p1 : pair = 1
      · simp only [if_neg p0, if_pos p1]
        exact (scaled (-originAuxiliaryWeight) (originalUnit 1)).trans
          (congrArg (fun x : P286LieBlockData => -originAuxiliaryWeight • x) sourceNativeOrigin_unit_one)
      · simp only [if_neg p0, if_neg p1, map_zero]
  rw [converted]
  change _ = p286LieBracket emDirection (actual.gaugeAuxiliary point pair)
  rw [actual_gaugeAuxiliary]
  have scale : originAuxiliaryWeight * 2 = gaugeScale^2 / (sourceCoupling * lapse) := by
    nlinarith [native_origin_auxiliary_scale]
  have bracketZero : p286LieBracket emDirection 0 = 0 := by
    simp [p286LieBracket, suLieBracket]
  fin_cases pair <;> simp [electricAuxiliary, p286LieBracket_smul_right,
    em_color_bracket, sourceColorP286Generator_bracket, bracketZero, smul_smul, scale]
  all_goals module

/-- The full origin is the actual gauge orbit with its scalar countervariation retained. -/
theorem native_origin_full_configuration :
    originDirection =
      { configurationRay actual emOrbit 1 with scalar := actual.scalar } := by
  have fields := sourceNativeOriginReal_remaining 0
  have gravity := native_origin_gravity_auxiliaries
  apply StageNineHolonomicConfiguration.ext
  · funext point
    change actual.coframe point + fieldCoframe (sourceNativeOriginReal 0) =
      actual.coframe point + (1:ℝ) • emOrbit.coframe point
    rw [fields.2.1]
    simp [emOrbit]
  · funext point
    change actual.gravityConnection point +
      StageNineLorentzConnectionVariation.lorentzSkewConnectionOfBivectorOneForm
        (fieldLorentz (sourceNativeOriginReal 0)) =
      actual.gravityConnection point + (1:ℝ) • emOrbit.gravityConnection point
    rw [fields.2.2, StageNineLorentzConnectionVariationDensity.lorentzSkewConnectionOfBivectorOneForm_zero]
    simp [emOrbit]
  · funext point
    change actual.gravityAuxiliary point + fieldGravityB (sourceNativeOriginReal 0) =
      actual.gravityAuxiliary point + (1:ℝ) • emOrbit.gravityAuxiliary point
    rw [gravity.1]
    simp [emOrbit]
  · funext point
    change actual.gravitySimplicityMultiplier point + fieldMultiplier (sourceNativeOriginReal 0) =
      actual.gravitySimplicityMultiplier point + (1:ℝ) • emOrbit.gravitySimplicityMultiplier point
    rw [gravity.2]
    simp [emOrbit]
  · funext point mu
    change actual.gaugeConnection point mu +
      p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal 0) mu) =
      actual.gaugeConnection point mu + (1:ℝ) • emOrbit.gaugeConnection point mu
    rw [native_origin_gauge_orbit, one_smul]
  · funext point pair
    change actual.gaugeAuxiliary point pair + gaugeBInsertion (sourceNativeOriginReal 0) pair =
      actual.gaugeAuxiliary point pair + (1:ℝ) • emOrbit.gaugeAuxiliary point pair
    rw [native_origin_auxiliary_orbit, one_smul]
  · funext point
    change actual.scalar point + fieldScalar (sourceNativeOriginReal 0) = actual.scalar point
    rw [fields.1, add_zero]
  · funext point
    change actual.matter point + diracMatrixMatterAction (ActiveGauge.rotation point)
      (primalInsertion (sourceNativeOriginReal 0)) =
      actual.matter point + (1:ℂ) • emOrbit.matter point
    rw [native_origin_primal_orbit, one_smul]
  · funext point
    change actual.conjugateMatter point + (dualInsertion (sourceNativeOriginReal 0)).comp
      (diracMatrixMatterAction (ActiveGauge.rotation point)) =
      actual.conjugateMatter point + (1:ℂ) • emOrbit.conjugateMatter point
    rw [native_origin_dual_orbit, one_smul]

/-- The complete nine-field identification is consumed by the literal original local action. -/
theorem native_origin_original_action (point : BasePoint) :
    nativeDensity (fun _ => sourceNativeOriginReal 0) point =
      generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary positiveSmoothUnifiedSource
        (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource) 0 point
        (toContinuumPointField
          { configurationRay actual emOrbit 1 with scalar := actual.scalar } point) := by
  rw [nativeDensity_original]
  change generatedDiracDualFormNativeUnifiedLocalDensityAtBoundary _ _ _ _
    (toContinuumPointField originDirection point) = _
  rw [native_origin_full_configuration]

end LowEnergy.GaussComposite.ActualEMCompleteOrbit
