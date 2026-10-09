import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageCauchyTangent

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumStaticVoltageSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource
open StageNineCanonicalCauchyState StageNineCoframeLocalDifferentiability
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair
open Stage10 Stage10.TemporalGauge SourcePropagationNativeActionHessian
open SourceQuantumScalarChart SourceQuantumNativeDimensions PreparationCoordinates
open PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical PreparationVacuumNativeSourceRestriction
open StageNineLorentzConnectionVariation StageNineP286ActionCauchySplit StageNineP286ActionConnectionVelocity
open SourcePropagationNativeEulerHistory SourcePropagationMotherEulerKernel
open StageNineDiracDualFormNativeMotherAction StageNineDiracDualFormNativeJointResidualCarrier
open scoped Matrix BigOperators Topology ContDiff
attribute [local irreducible] Runtime.configuration Runtime.source

/-- The original raw eleventh gauge coordinate is precisely the original charge direction. -/
theorem sourceVoltageY_native : originalUnit 11=p286CoordinateEquiv HyperchargeResponse.chargeDirection := by
  apply rawCoordinates.injective
  rw [originalUnit,LinearEquiv.apply_symm_apply]
  ext i
  fin_cases i <;> simp [rawCoordinates,rawRead,nativeCoordinates_apply,
    HyperchargeResponse.chargeDirection,hyperchargeGenerator]

theorem sourceVoltage_scalar_basis : orbit (originalUnit 11)=scalarCharge HyperchargeResponse.chargeDirection := by
  rw [sourceVoltageY_native]
  change scalarMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm
    (p286CoordinateEquiv HyperchargeResponse.chargeDirection))) vacuum=scalarCharge HyperchargeResponse.chargeDirection
  rw [LinearEquiv.symm_apply_apply,scalarCharge,Runtime.source_eq]
  rfl

/-- These are the actual voltage, scalar normal velocity, and constitutive gauge-B coordinates. -/
def sourceVoltageCoordinates (value slope : ℝ) (electric : Fin 3→ℝ) : Field289 :=
  Pi.single 20 value+Pi.single 8 slope+Pi.single 264 (electric 0)+
    Pi.single 276 (electric 1)+Pi.single 288 (electric 2)

private theorem coordinate_slot (value slope : ℝ) (electric : Fin 3→ℝ) (i : Fin 289) :
    sourceVoltageCoordinates value slope electric i=
      (if i=20 then value else 0)+(if i=8 then slope else 0)+
      (if i=264 then electric 0 else 0)+(if i=276 then electric 1 else 0)+(if i=288 then electric 2 else 0) := by
  simp only [sourceVoltageCoordinates,Pi.add_apply,Pi.single_apply]

theorem sourceVoltageCoordinates_scalar (value slope : ℝ) (electric : Fin 3→ℝ) :
    fieldScalar (sourceVoltageCoordinates value slope electric)=slope • scalarCharge HyperchargeResponse.chargeDirection := by
  simp [fieldScalar,coordinate_slot,scalarSlot,Fin.sum_univ_succ,originalJColumns,
    sourceVoltage_scalar_basis]

theorem sourceVoltageCoordinates_gauge (value slope : ℝ) (electric : Fin 3→ℝ) (mu : Fin 4) :
    fieldGauge (sourceVoltageCoordinates value slope electric) mu=
      if mu=0 then value • p286CoordinateEquiv HyperchargeResponse.chargeDirection else 0 := by
  fin_cases mu <;> simp [fieldGauge,coordinate_slot,gaugeSlot,Fin.sum_univ_succ,sourceVoltageY_native]

private theorem nativeY_scale (a : ℝ) :
    p286CoordinateEquiv.symm (a • p286CoordinateEquiv HyperchargeResponse.chargeDirection)=
      a • HyperchargeResponse.chargeDirection := by
  have h := p286CoordinateEquiv.symm.toLinearMap.map_smul a (p286CoordinateEquiv HyperchargeResponse.chargeDirection)
  simpa only [LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply] using h

theorem sourceVoltageCoordinates_auxiliary (value slope : ℝ) (electric : Fin 3→ℝ) (pair : Fin 6) :
    gaugeBInsertion (sourceVoltageCoordinates value slope electric) pair=
      TemporalGauge.field (fun _=>0) (fun j=>electric j • HyperchargeResponse.chargeDirection) pair := by
  have selected : ∀pair : Fin 6,(∑a : Fin 12,fieldGaugeB (sourceVoltageCoordinates value slope electric) pair a • originalUnit a)=
      ![0,0,0,electric 0 • p286CoordinateEquiv HyperchargeResponse.chargeDirection,
        electric 1 • p286CoordinateEquiv HyperchargeResponse.chargeDirection,
        electric 2 • p286CoordinateEquiv HyperchargeResponse.chargeDirection] pair := by
    intro p
    fin_cases p <;> simp [fieldGaugeB,coordinate_slot,gaugeBSlot,Fin.sum_univ_succ,sourceVoltageY_native]
  unfold gaugeBInsertion
  rw [selected]
  fin_cases pair <;> first | exact map_zero _ | exact nativeY_scale _

theorem sourceVoltageCoordinates_other (value slope : ℝ) (electric : Fin 3→ℝ) :
    fieldCoframe (sourceVoltageCoordinates value slope electric)=0 ∧
    fieldLorentz (sourceVoltageCoordinates value slope electric)=0 ∧
    fieldGravityB (sourceVoltageCoordinates value slope electric)=0 ∧
    fieldMultiplier (sourceVoltageCoordinates value slope electric)=0 ∧
    primalInsertion (sourceVoltageCoordinates value slope electric)=0 ∧
    dualInsertion (sourceVoltageCoordinates value slope electric)=0 := by
  have primal (spin : Fin 4) (color : Fin 3) :
      fieldPrimalComplex (sourceVoltageCoordinates value slope electric) spin color=0 := by
    fin_cases spin <;> fin_cases color <;>
      norm_num [fieldPrimalComplex,fieldPrimal,coordinate_slot,primalSlot,Fin.ext_iff]
  have dual (spin : Fin 4) (color : Fin 3) :
      fieldDualComplex (sourceVoltageCoordinates value slope electric) spin color=0 := by
    fin_cases spin <;> fin_cases color <;>
      norm_num [fieldDualComplex,fieldDual,coordinate_slot,dualSlot,Fin.ext_iff]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · ext a mu
    fin_cases a <;> fin_cases mu <;> norm_num [fieldCoframe,coordinate_slot,coframeSlot,Fin.ext_iff]
  · ext mu a
    fin_cases mu <;> fin_cases a <;> norm_num [fieldLorentz,coordinate_slot,lorentzSlot,Fin.ext_iff]
  · ext pair a
    fin_cases pair <;> fin_cases a <;> norm_num [fieldGravityB,coordinate_slot,gravitySlot,Fin.ext_iff]
  · ext pair a
    fin_cases pair <;> fin_cases a <;> norm_num [fieldMultiplier,coordinate_slot,multiplierSlot,Fin.ext_iff]
  · simp only [primalInsertion,primal,zero_smul,Finset.sum_const_zero]
  · apply LinearMap.ext
    intro v
    change (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex (sourceVoltageCoordinates value slope electric) spin color * sourceTripletRead (v spin) color)=0
    simp only [dual,zero_mul,Finset.sum_const_zero]

def sourceVoltageSignal (profile : BasePoint→ℝ) (amplitude : ℝ) (point : BasePoint) : Field289 :=
  sourceVoltageCoordinates (amplitude*profile point)
    (amplitude * (-(canonicalTimeProjection point*profile (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)))))
    (fun axis=>amplitude * (-(2*lapse)*fieldDirectionalDerivative profile point axis.succ))

/-- The full 289 coordinate family is exactly the original normal/constitutive Cauchy family on the same background. -/
theorem sourceVoltage_nativeConfiguration (profile : BasePoint→ℝ) (regular : Differentiable ℝ profile)
    (amplitude : ℝ) :
    nativeConfiguration (sourceVoltageSignal profile amplitude)=sourceVoltageConfiguration profile amplitude := by
  apply StageNineHolonomicConfiguration.ext
  · funext point
    rw [sourceVoltage_coframe,Runtime.configuration_eq]
    change actual.coframe point+fieldCoframe (sourceVoltageCoordinates _ _ _)=actual.coframe point
    rw [(sourceVoltageCoordinates_other _ _ _).1,add_zero]
  · funext point
    change actual.gravityConnection point+lorentzSkewConnectionOfBivectorOneForm
      (fieldLorentz (sourceVoltageSignal profile amplitude point))=Runtime.configuration.gravityConnection point
    rw [Runtime.configuration_eq]
    unfold sourceVoltageSignal
    rw [(sourceVoltageCoordinates_other _ _ _).2.1]
    simp
  · funext point
    change actual.gravityAuxiliary point+fieldGravityB (sourceVoltageSignal profile amplitude point)=Runtime.configuration.gravityAuxiliary point
    rw [Runtime.configuration_eq]
    unfold sourceVoltageSignal
    rw [(sourceVoltageCoordinates_other _ _ _).2.2.1,add_zero]
  · funext point
    change actual.gravitySimplicityMultiplier point+fieldMultiplier (sourceVoltageSignal profile amplitude point)=Runtime.configuration.gravitySimplicityMultiplier point
    rw [Runtime.configuration_eq]
    unfold sourceVoltageSignal
    rw [(sourceVoltageCoordinates_other _ _ _).2.2.2.1,add_zero]
  · funext point mu
    rw [sourceVoltage_connection,Runtime.configuration_eq]
    change actual.gaugeConnection point mu+p286CoordinateEquiv.symm
      (fieldGauge (sourceVoltageCoordinates _ _ _) mu)=_
    rw [sourceVoltageCoordinates_gauge]
    split_ifs <;> simp only [nativeY_scale,map_zero]
  · funext point pair
    rw [sourceVoltage_auxiliary_affine profile regular,Runtime.configuration_eq]
    change actual.gaugeAuxiliary point pair+gaugeBInsertion (sourceVoltageCoordinates _ _ _) pair=_
    rw [sourceVoltageCoordinates_auxiliary]
    change actual.gaugeAuxiliary point pair+TemporalGauge.field (fun _=>0)
      (fun axis=>(amplitude * (-(2*lapse)*fieldDirectionalDerivative profile point axis.succ)) • HyperchargeResponse.chargeDirection) pair=
        actual.gaugeAuxiliary point pair+amplitude • sourceVoltageAuxiliaryTangent profile point pair
    congr 1
    fin_cases pair <;> simp [TemporalGauge.field,sourceVoltageAuxiliaryTangent,smul_smul]
  · funext point
    rw [sourceVoltage_scalar,Runtime.configuration_eq]
    change actual.scalar point+fieldScalar (sourceVoltageCoordinates _ _ _)=_
    rw [sourceVoltageCoordinates_scalar]
    simp only [sourceVoltageScalarTangent,smul_smul]
  · funext point
    rw [(sourceVoltage_matter profile amplitude).1,Runtime.configuration_eq]
    change actual.matter point+_=actual.matter point
    unfold sourceVoltageSignal
    rw [(sourceVoltageCoordinates_other _ _ _).2.2.2.2.1,map_zero,add_zero]
  · funext point
    rw [(sourceVoltage_matter profile amplitude).2,Runtime.configuration_eq]
    change actual.conjugateMatter point+_=actual.conjugateMatter point
    unfold sourceVoltageSignal
    rw [(sourceVoltageCoordinates_other _ _ _).2.2.2.2.2,LinearMap.zero_comp,add_zero]

theorem sourceVoltageSignal_amplitude (profile : BasePoint→ℝ) (amplitude : ℝ) :
    sourceVoltageSignal profile amplitude=fun point=>amplitude • sourceVoltageSignal profile 1 point := by
  funext point i
  simp only [sourceVoltageSignal,coordinate_slot,Pi.smul_apply,smul_eq_mul,one_mul]
  split_ifs <;> ring

theorem sourceVoltageSignal_smooth (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile) (amplitude : ℝ) :
    ContDiff ℝ ∞ (sourceVoltageSignal profile amplitude) := by
  have gradient (mu : Fin 4) : ContDiff ℝ ∞ (fun point=>fieldDirectionalDerivative profile point mu) :=
    (smooth.fderiv_right (m:=∞) (by simp)).clm_apply contDiff_const
  have time : ContDiff ℝ ∞ canonicalTimeProjection := canonicalTimeProjection.contDiff
  have spatial : ContDiff ℝ ∞ canonicalSpatialProjection := canonicalSpatialProjection.contDiff
  have slice : ContDiff ℝ ∞ (canonicalCauchySlicePoint 0) := by
    have same : canonicalCauchySlicePoint 0=canonicalSpatialInclusion := by
      funext x
      rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
      simp
    rw [same]
    exact canonicalSpatialInclusion.contDiff
  apply contDiff_pi.mpr
  intro i
  simp only [sourceVoltageSignal,coordinate_slot]
  split_ifs <;> fun_prop

/-- The new coordinates carry the original nonlinear action's joint Euler, on the identical voltage configuration. -/
theorem sourceVoltage_Euler_original (profile : BasePoint→ℝ) (regular : Differentiable ℝ profile)
    (amplitude : ℝ) (point : BasePoint) :
    nativeEuler (sourceVoltageSignal profile amplitude) point=
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        (sourceVoltageConfiguration profile amplitude) point := by
  rw [nativeEuler_original,sourceVoltage_nativeConfiguration profile regular]

/-- The whole linear source is generated by amplitude differentiation of this actual holonomic Cauchy deformation. -/
theorem sourceVoltage_Euler_generated (profile : BasePoint→ℝ) (smooth : ContDiff ℝ ∞ profile)
    (point : BasePoint) (field : Fin 289) :
    HasDerivAt (fun amplitude : ℝ=>nativeHolonomicEuler (sourceVoltageSignal profile amplitude) point field)
      (nativeEulerLinearJet (signalSecondJet (sourceVoltageSignal profile 1) point) field) 0 := by
  have same : (fun amplitude : ℝ=>nativeHolonomicEuler (sourceVoltageSignal profile amplitude) point field)=
      fun amplitude=>nativeHolonomicEuler (fun position=>amplitude • sourceVoltageSignal profile 1 position) point field := by
    funext amplitude
    rw [sourceVoltageSignal_amplitude profile amplitude]
  rw [same]
  exact nativeHolonomicEuler_source_linear (sourceVoltageSignal profile 1) point
    ((sourceVoltageSignal_smooth profile smooth 1).contDiffAt.of_le (by change ((2:ℕ∞):ℕ∞ω)≤((⊤:ℕ∞):ℕ∞ω);exact WithTop.coe_le_coe.mpr le_top)) field

end LowEnergy.PreparationVacuumStaticVoltageSource
