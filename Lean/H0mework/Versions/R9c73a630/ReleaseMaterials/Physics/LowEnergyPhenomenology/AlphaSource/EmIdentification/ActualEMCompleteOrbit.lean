import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMCarrier

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualEMCompleteOrbit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineP286GaugeAuxiliaryVariation StageNineDynamicBreakingVacuum
open StageNineP286GaugeConnectionVariationDensity SU7ExteriorMatterRepresentation
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativeOriginPhaseWard
open PreparationPhysicalPhaseGaugeRealization PreparationCoordinates
open SourcePropagationNativeActionHessian PhysicalEMGaugeRealization ActualEMCarrierOwn
open SourceQuantumScalarChart DiracExteriorMatterAction
open scoped Matrix BigOperators

/-- The original constant-generator orbit retains all nine field groups. -/
def emOrbit : StageNineHolonomicConfiguration where
  coframe := 0
  gravityConnection := 0
  gravityAuxiliary := 0
  gravitySimplicityMultiplier := 0
  gaugeConnection point mu := p286LieBracket emDirection (actual.gaugeConnection point mu)
  gaugeAuxiliary point pair := p286LieBracket emDirection (actual.gaugeAuxiliary point pair)
  scalar _ := sourcePhaseGaugeScalarVariation
  matter point := emGaugeAction (actual.matter point)
  conjugateMatter point := -(actual.conjugateMatter point).comp emGaugeAction

/-- This is a restriction of the actual full origin endpoint, before any field is discarded. -/
def originDirection : StageNineHolonomicConfiguration :=
  nativeConfiguration (fun _ => sourceNativeOriginReal 0)

theorem phase_lie_original :
    p286CoordinateEquiv.symm sourcePhaseGaugeLie = emDirection := by
  apply p286CoordinateEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change -p286CoordinateEquiv (sourceColorP286Generator 2) -
    (1/2:ℝ) • p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection =
      p286CoordinateEquiv (-sourceColorP286Generator 2 -
        (1/2:ℝ) • Stage10.HyperchargeResponse.chargeDirection)
  let linear : P286LieBlockData →ₗ[ℝ] P286CoordinateCarrier := p286CoordinateEquiv.toLinearMap
  have result := (linear.map_sub (-sourceColorP286Generator 2)
    ((1/2:ℝ) • Stage10.HyperchargeResponse.chargeDirection)).trans
      (congrArg₂ (fun x y : P286CoordinateCarrier => x - y)
        (linear.map_neg (sourceColorP286Generator 2))
        (linear.map_smul (1/2:ℝ) Stage10.HyperchargeResponse.chargeDirection))
  exact result.symm

theorem em_orbit_scalar_original :
    (emOrbit.scalar 0) = scalarMotherLieAction (p286LieBlockEmbed emDirection) (actual.scalar 0) := by
  change sourcePhaseGaugeScalarVariation = _
  unfold sourcePhaseGaugeScalarVariation orbit action
  change scalarP286ActionBilinear sourcePhaseGaugeLie vacuum = _
  rw [actual_scalar]
  change scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm sourcePhaseGaugeLie))
    vacuum = _
  rw [phase_lie_original]
  rfl

theorem native_origin_gauge_orbit (point : BasePoint) (mu : Fin 4) :
    p286CoordinateEquiv.symm (fieldGauge (sourceNativeOriginReal 0) mu) =
      emOrbit.gaugeConnection point mu := by
  rw [sourceNativeOriginReal_gauge, if_pos rfl]
  simp only [map_smul, map_sub, apply_ite, map_zero,
    sourceNativeOrigin_unit_zero, sourceNativeOrigin_unit_one, smul_sub,
    smul_zero, smul_smul]
  have scale : sourceNativeOriginGaugeWeight * 2 = gaugeScale := by
    norm_num [sourceNativeOriginGaugeWeight, gaugeScale, spinScale]
    ring
  rw [scale]
  have opposite := em_actual_background_derivative point
  change _ = p286LieBracket emDirection (actual.gaugeConnection point mu)
  rw [StageNineP286BracketCalculus.p286LieBracket_skew]
  change _ = -emBackgroundDerivative point mu
  rw [opposite]
  fin_cases mu <;> simp
  module

theorem native_origin_primal_orbit (point : BasePoint) :
    diracMatrixMatterAction (ActiveGauge.rotation point)
      (primalInsertion (sourceNativeOriginReal 0)) = emOrbit.matter point := by
  rw [origin_actual_primal_em]
  have embedded : emFullDefect (actual.matter point) = 0 := by
    rw [actual_matter]
    exact em_defect_embedded (fun index =>
      spinPairCoefficients (upperPhase point) (lowerPhase point) index.1 index.2)
  rw [embedded, add_zero]
  rfl

private theorem hypercharge_dual (state : Fin 2) (v : SU7ExteriorSpinorMatterCarrier) :
    sourceColorDoubletDual state
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection) v) =
      Complex.I * sourceColorDoubletDual state v := by
  have weight : SU7ExteriorMatterRestriction.exteriorHyperchargeWeight (sourceColorDoubletIndex state) = 1 := by
    fin_cases state <;> decide
  change (SU7ExteriorMatterRestriction.su7ExteriorBasis 2).coord (sourceColorDoubletIndex state)
    (exteriorMotherLieAction 2
      (p286LieBlockEmbed Stage10.HyperchargeResponse.chargeDirection) v.2.1) = _
  conv_lhs => rw [←(SU7ExteriorMatterRestriction.su7ExteriorBasis 2).sum_repr v.2.1]
  simp only [map_sum, map_smul, Stage10.HyperchargeResponse.exterior_charge_basis,
    Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [weight]
  simp [sourceColorDoubletDual, mul_comm]

theorem em_defect_actual_dual (point : BasePoint) (v : DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (emFullDefect v) = 0 := by
  rw [Stage9DEF.Compatibility.actual_dual_evaluation]
  apply Finset.sum_eq_zero
  intro index _
  have zero : Stage9DEF.Compatibility.coordinates (emFullDefect v) index = 0 := by
    simp only [Stage9DEF.Compatibility.coordinates, LinearMap.coe_mk, AddHom.coe_mk,
      emFullDefect, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Pi.smul_apply, Pi.sub_apply, diracExteriorMotherLieAction, internalMatterLinearAction,
      map_smul, map_sub,
      hypercharge_dual, smul_eq_mul]
    ring
  rw [zero, mul_zero]

theorem native_origin_dual_orbit (point : BasePoint) :
    (dualInsertion (sourceNativeOriginReal 0)).comp
      (diracMatrixMatterAction (ActiveGauge.rotation point)) = emOrbit.conjugateMatter point := by
  rw [origin_actual_dual_em]
  have defect : (actual.conjugateMatter point).comp emFullDefect = 0 := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply]
    exact em_defect_actual_dual point v
  change -(actual.conjugateMatter point).comp (emGaugeAction + emFullDefect) = _
  rw [LinearMap.comp_add, defect, add_zero]
  rfl

theorem native_origin_scalar_difference :
    fieldScalar (sourceNativeOriginReal 0) - emOrbit.scalar 0 =
      (1/2:ℝ) • orbit GaussComposite.nativeY := by
  rw [(sourceNativeOriginReal_remaining 0).1]
  change 0 - sourcePhaseGaugeScalarVariation = _
  rw [sourcePhaseGaugeScalarVariation_return]
  module

theorem em_scalar_hypercharge : orbit GaussComposite.nativeY = Stage10.HyperchargeResponse.scalarCharge := by
  change scalarMotherLieAction
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (p286CoordinateEquiv Stage10.HyperchargeResponse.chargeDirection)))
    vacuum = _
  rw [LinearEquiv.symm_apply_apply]
  simp only [Stage10.HyperchargeResponse.scalarCharge, Stage10.Runtime.source_eq, vacuum]

theorem em_orbit_scalar_norm : scalarCoordinateSquaredNorm (emOrbit.scalar 0) = (1/2:ℝ) := by
  change scalarCoordinateSquaredNorm sourcePhaseGaugeScalarVariation = _
  rw [sourcePhaseGaugeScalarVariation_return, em_scalar_hypercharge,
    Stage10.HyperchargeResponse.scalarCharge_norm]
  norm_num

theorem em_orbit_scalar_nonzero : emOrbit.scalar 0 ≠ 0 := by
  intro vanish
  have norm := em_orbit_scalar_norm
  rw [vanish] at norm
  norm_num [scalarCoordinateSquaredNorm] at norm

end LowEnergy.GaussComposite.ActualEMCompleteOrbit
