import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageHamiltonianResponse
import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceGaussActionTimeReturn

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageNoether
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField ProofFreeRicherAnholonomicSource Stage10 Stage10.TemporalGauge
open StageNineCurrentCoframeMatterTemporalPrincipal
open StageNineCanonicalCauchyState StageNineP286ActionConnectionVelocity
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open Stage9C.Material.SpinPair DiracExteriorMatterAction FullQuantum.StateGreen FullQuantum.CoframeResponse
open PreparationVacuumStaticVoltageSource PreparationVacuumPhysicalQuantumLockedCharge
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalDensity
open PreparationVacuumPhysicalModeChargeRead PreparationVacuumNativeFieldInjection
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussQuantumMultiplier
open GaussCoreHilbert GaussFockLift CanonicalGradedSpatialSource CanonicalGradedCharge GaussComposite
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationPhysicalActionUnits
open scoped BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace Topology ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
attribute [local irreducible] sourceModeGaussReader sourcePreparedTimeMatrix sourceCanonicalMomentumInverse

def sourceVoltageEnergyCoefficient (value slope : ℝ) (s : ActionState) (k : Fin 4) : SourceMatrix :=
  -densityActionMatrix*densityVariation (sourceVoltageCoordinates value slope 0) s k

private theorem voltage_phase_lower (s : ActionState) (nondegenerate : s.1.det≠0) (value slope : ℝ) :
    sourceVoltageHamiltonianMatrix value slope s=
      -(statePhase s*(stateVolume s • sourceVoltageLowerInput value slope s)) := by
  have volume : stateVolume s≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nondegenerate)
  unfold sourceVoltageHamiltonianMatrix statePhase
  rw [mul_smul_comm,smul_mul_assoc,smul_smul]
  have factor : stateVolume s*(Complex.I*(stateVolume s)⁻¹)=Complex.I :=by
    field_simp
  rw [factor,neg_smul]

/-- The raw Noether density and original time momentum generate the energy coefficient. -/
theorem sourceVoltageEnergyCoefficient_generated (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope : ℝ) (k : Fin 4) :
    sourceVoltageEnergyCoefficient value slope s k=sourcePreparedTimeMatrix s*
      (if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0) := by
  unfold sourceVoltageEnergyCoefficient
  rw [sourceVoltage_density_generated s nondegenerate]
  split_ifs
  · rw [voltage_phase_lower s nondegenerate,Matrix.mul_neg,←mul_assoc,
      sourcePreparedTimeMatrix_phase_cancel s nondegenerate regular,neg_mul]
  · simp only [Matrix.mul_zero]

theorem sourceVoltageEnergyCoefficient_affine (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope a : ℝ) (k : Fin 4) :
    originalEnergyCoefficient (s+a • sourceVoltageStateDirection value slope) k=
      originalEnergyCoefficient s k+a • sourceVoltageEnergyCoefficient value slope s k := by
  have coframe : (s+a • sourceVoltageStateDirection value slope).1=s.1 :=by
    simp [sourceVoltageStateDirection]
  have timeMatrix : sourcePreparedTimeMatrix (s+a • sourceVoltageStateDirection value slope)=
      sourcePreparedTimeMatrix s :=by unfold sourcePreparedTimeMatrix;rw [coframe]
  rw [originalEnergyCoefficient_generated _ (by simpa only [coframe] using regular),timeMatrix,
    sourceVoltageHamiltonian_affine,mul_add,mul_smul_comm,
    ←originalEnergyCoefficient_generated s regular,←sourceVoltageEnergyCoefficient_generated s nondegenerate regular]

theorem sourceVoltageEnergyCoefficient_derivative (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope : ℝ) (k : Fin 4) :
    HasDerivAt (fun a : ℝ=>originalEnergyCoefficient (s+a • sourceVoltageStateDirection value slope) k)
      (sourceVoltageEnergyCoefficient value slope s k) 0 := by
  have h:=((hasDerivAt_id (0:ℝ)).smul_const
    (sourceVoltageEnergyCoefficient value slope s k)).const_add (originalEnergyCoefficient s k)
  simpa only [sourceVoltageEnergyCoefficient_affine s nondegenerate regular,one_smul,id_eq] using h

/-- The original actionScale and original canonical momentum inverse return the actual Hamiltonian response. -/
theorem sourceVoltageEnergyCoefficient_normalized (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0)
    (value slope : ℝ) (k : Fin 4) :
    sourceCanonicalMomentumInverse s*((ActionNormalization.actionScale:ℂ) •
      sourceVoltageEnergyCoefficient value slope s k)=
        if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0 := by
  rw [sourceVoltageEnergyCoefficient_generated s nondegenerate regular,←smul_mul_assoc,←mul_assoc,
    sourceCanonicalMomentumInverse_generated s nondegenerate regular,one_mul]

def sourceVoltageEnergySymbol (p : PhysicalMomentum) (s : ActionState) (value slope : ℝ) : FullMatrix :=
  fourierLinear p (fun k=>sourceCanonicalMomentumInverse s*((ActionNormalization.actionScale:ℂ) •
    sourceVoltageEnergyCoefficient value slope s k))

theorem sourceVoltageEnergySymbol_generated (p : PhysicalMomentum) (s : ActionState)
    (nondegenerate : s.1.det≠0) (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ) :
    sourceVoltageEnergySymbol p s value slope=
      SourceRealScalarFock.branches (sourceVoltageHamiltonianMatrix value slope s) := by
  unfold sourceVoltageEnergySymbol
  simp only [sourceVoltageEnergyCoefficient_normalized s nondegenerate regular]
  change realFourierMatrix (fun k=>if k=0 then sourceVoltageHamiltonianMatrix value slope s else 0) p=_
  simp [realFourierMatrix,affineMatrix,SourceRealScalarFock.branches]


/-- The actual five-slot Cauchy signal drives the same old symbol and the original normalized energy coefficient. -/
theorem sourceVoltageEnergySymbol_actual (profile : BasePoint→ℝ) (point : BasePoint)
    (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) :
    symbolFirst p s (fieldDirection (sourceVoltageSignal profile 1 point))=
      sourceVoltageEnergySymbol p s (profile point)
        (-(canonicalTimeProjection point*profile
          (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point)))) := by
  unfold sourceVoltageSignal
  simp only [one_mul]
  rw [sourceVoltageField_direction,sourceVoltageSymbol_first p s valid,
    sourceVoltageEnergySymbol_generated p s valid.1 valid.2]


def sourceVoltageEnergyRead (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (s : ActionState) (value slope : ℝ) (side edge other opposite : Fin 2) : ℂ :=
  inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
    (lift (quantized (sourceVoltageEnergySymbol p s value slope))
      (sourceChargedGaussPrepared epsilon precision other opposite))

def sourceVoltageScalarEnergyRead (epsilon : ℝ) (precision : 0<epsilon)
    (s : ActionState) (side edge other opposite : Fin 2) : ℂ :=
  inner ℂ (sourceChargedGaussPrepared epsilon precision side edge)
    (lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))
      (sourceChargedGaussPrepared epsilon precision other opposite))

/-- Both independent exterior legs consume the same raw density, canonical momentum and original action units. -/
theorem sourceVoltageEnergyRead_generated (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ)
    (side edge other opposite : Fin 2) :
    sourceVoltageEnergyRead epsilon precision p s value slope side edge other opposite=
      (value:ℂ)*(if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0)+
      (slope:ℂ)*sourceVoltageScalarEnergyRead epsilon precision s side edge other opposite := by
  unfold sourceVoltageEnergyRead sourceVoltageScalarEnergyRead
  rw [sourceVoltageEnergySymbol_generated p s nondegenerate regular,
    sourceVoltage_charged_Gauss epsilon precision s regular,inner_add_right]
  simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),inner_smul_right]
  rw [sourceChargedGauss_gram]
  rfl

theorem sourceVoltageScalarEnergyRead_price (epsilon : ℝ) (precision : 0<epsilon)
    (s : ActionState) (side edge other opposite : Fin 2) :
    ‖sourceVoltageScalarEnergyRead epsilon precision s side edge other opposite‖≤
      ‖lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))‖ := by
  unfold sourceVoltageScalarEnergyRead
  calc
    _≤‖sourceChargedGaussPrepared epsilon precision side edge‖*
      ‖lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))
        (sourceChargedGaussPrepared epsilon precision other opposite)‖:=norm_inner_le_norm _ _
    _≤_ := by
      rw [sourceChargedGauss_unit,one_mul]
      calc
        _≤‖lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))‖*
          ‖sourceChargedGaussPrepared epsilon precision other opposite‖:=ContinuousLinearMap.le_opNorm _ _
        _=_ := by rw [sourceChargedGauss_unit,mul_one]


theorem sourceVoltageEnergyRead_price (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (value slope : ℝ)
    (side edge other opposite : Fin 2) :
    ‖sourceVoltageEnergyRead epsilon precision p s value slope side edge other opposite‖≤
      |value|+|slope| *‖lift (quantized (SourceRealScalarFock.branches (sourceVoltageScalarHamiltonian s)))‖ := by
  rw [sourceVoltageEnergyRead_generated epsilon precision p s nondegenerate regular]
  have gram : ‖(if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then (1:ℂ) else 0)‖≤1 := by
    split_ifs <;> norm_num
  calc
    _≤‖(value:ℂ)*(if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0)‖+
      ‖(slope:ℂ)*sourceVoltageScalarEnergyRead epsilon precision s side edge other opposite‖ :=norm_add_le _ _
    _≤_ := by
      simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact add_le_add (by simpa only [mul_one] using mul_le_mul_of_nonneg_left gram (abs_nonneg value))
        (mul_le_mul_of_nonneg_left (sourceVoltageScalarEnergyRead_price epsilon precision s side edge other opposite)
          (abs_nonneg slope))


def sourceVoltageActualEnergy (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (s : ActionState) (profile : BasePoint→ℝ) (point : BasePoint) (side edge other opposite : Fin 2) : ℂ :=
  sourceVoltageEnergyRead epsilon precision p s (profile point)
    (-(canonicalTimeProjection point*profile (canonicalCauchySlicePoint 0 (canonicalSpatialProjection point))))
    side edge other opposite

theorem sourceVoltageActualEnergy_Cauchy (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (profile : BasePoint→ℝ)
    (x : StageNineSpatialPoint) (side edge other opposite : Fin 2) :
    sourceVoltageActualEnergy epsilon precision p s profile (canonicalCauchySlicePoint 0 x)
      side edge other opposite=(profile (canonicalCauchySlicePoint 0 x):ℂ)*
        (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0) := by
  unfold sourceVoltageActualEnergy
  rw [sourceVoltageEnergyRead_generated epsilon precision p s nondegenerate regular]
  simp only [canonicalTimeProjection_slice,zero_mul,neg_zero,Complex.ofReal_zero,zero_mul,add_zero]

theorem sourceVoltageActualEnergy_unit (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (profile : BasePoint→ℝ)
    (x : StageNineSpatialPoint) (side edge : Fin 2) :
    sourceVoltageActualEnergy epsilon precision p s profile (canonicalCauchySlicePoint 0 x)
      side edge side edge=(profile (canonicalCauchySlicePoint 0 x):ℂ) := by
  rw [sourceVoltageActualEnergy_Cauchy epsilon precision p s nondegenerate regular]
  simp only [ite_true,mul_one]

/-- The energy read consumes the original normalized Noether temporal current of the same restriction. -/
theorem sourceVoltageActualEnergy_Noether_unit (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (profile : BasePoint→ℝ)
    (x : StageNineSpatialPoint) (side edge : Fin 2) :
    sourceVoltageActualEnergy epsilon precision p s profile (canonicalCauchySlicePoint 0 x)
      side edge side edge=-(profile (canonicalCauchySlicePoint 0 x):ℂ)*
        GaussComposite.PhysicalModeEMCurrent.canonicalCurrentTensor
          (canonicalCauchySlicePoint 0 x) 0 (sourceChargedRestIndex side edge) (sourceChargedRestIndex side edge) := by
  rw [sourceVoltageActualEnergy_unit epsilon precision p s nondegenerate regular,
    GaussComposite.PhysicalModeEMCurrent.canonicalTemporal]
  ring

theorem sourceVoltageSpatialEnergy_derivative (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (profile : BasePoint→ℝ)
    (smooth : ContDiff ℝ ∞ profile) (x : StageNineSpatialPoint)
    (side edge other opposite : Fin 2) :
    HasFDerivAt (fun y=>sourceVoltageActualEnergy epsilon precision p s profile
      (canonicalCauchySlicePoint 0 y) side edge other opposite)
      ((if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then (1:ℂ) else 0) •
        Complex.ofRealCLM.comp ((fderiv ℝ profile (canonicalCauchySlicePoint 0 x)).comp canonicalSpatialInclusion)) x := by
  have differentiable := ((smooth.differentiable (by simp)).differentiableAt
    (x:=canonicalCauchySlicePoint 0 x)).hasFDerivAt
  have derivative := Complex.ofRealCLM.hasFDerivAt.comp x
    (differentiable.comp x (canonicalCauchySlicePoint_hasFDerivAt 0 x))
  have scaled:=derivative.const_smul
    (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then (1:ℂ) else 0)
  apply scaled.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun y=>by
    change sourceVoltageActualEnergy epsilon precision p s profile (canonicalCauchySlicePoint 0 y)
      side edge other opposite=
        (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then (1:ℂ) else 0) •
          (profile (canonicalCauchySlicePoint 0 y):ℂ)
    rw [sourceVoltageActualEnergy_Cauchy epsilon precision p s nondegenerate regular]
    simp only [smul_eq_mul,mul_comm])

def sourceVoltageSpatialForce (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (s : ActionState) (profile : BasePoint→ℝ) (x : StageNineSpatialPoint) (axis : Fin 3)
    (side edge other opposite : Fin 2) : ℂ :=
  -(fderiv ℝ (fun y=>sourceVoltageActualEnergy epsilon precision p s profile
    (canonicalCauchySlicePoint 0 y) side edge other opposite) x (canonicalSpatialCoordinateDirection axis))

/-- The original energy gradient generates the actual spatial force on the two source legs. -/
theorem sourceVoltageSpatialForce_generated (epsilon : ℝ) (precision : 0<epsilon)
    (p : PhysicalMomentum) (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (profile : BasePoint→ℝ)
    (smooth : ContDiff ℝ ∞ profile) (x : StageNineSpatialPoint) (axis : Fin 3)
    (side edge other opposite : Fin 2) :
    sourceVoltageSpatialForce epsilon precision p s profile x axis side edge other opposite=
      -((fieldDirectionalDerivative profile (canonicalCauchySlicePoint 0 x) axis.succ:ℝ):ℂ)*
        (if sourceChargedRestIndex side edge=sourceChargedRestIndex other opposite then 1 else 0) := by
  unfold sourceVoltageSpatialForce
  rw [(sourceVoltageSpatialEnergy_derivative epsilon precision p s nondegenerate regular
    profile smooth x side edge other opposite).fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    canonicalSpatialInclusion_coordinateDirection,Complex.ofRealCLM_apply,smul_eq_mul,
    fieldDirectionalDerivative]
  ring

end LowEnergy.PreparationPhysicalVoltageNoether
