import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceOriginalEnergyDensity
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricPairCurrent
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceN1Prepared
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalTimePolynomial

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActionUnits
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open PreparationVacuumActionFieldLift PreparationVacuumFullElectricWard
open PreparationVacuumPhysicalColorWard PreparationVacuumPhysicalN1WardCollapse
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumMovingPoleGaussReturn
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential GaussCoreHilbert GaussFockPair
open PreparationVacuumActionDecomposition
open PreparationVacuumPhysicalHalfAxis PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalFeedback FullYSourceCutoffVolterra CanonicalGradedSpatialSource
open PreparationVacuumRawJointFeedback
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

theorem sourceStateVolume_actual (z : physicalChart) :
    stateVolume (sourceState z.val)=(Stage9C.Material.SpinPair.lapse*GaussNativeEnergy.volume z.val:ℝ) :=by
  simp only [stateVolume,sourceState,CanonicalGradedSpatialSource.sourceCoframe,GaussNativeEnergy.coframe_determinant,
    GaussNativeEnergy.source_time_generated,Matrix.cons_val_zero]
  change ((|Stage9C.Material.SpinPair.lapse*GaussNativeEnergy.volume z.val|:ℝ):ℂ)=_
  rw [abs_of_pos (mul_pos Stage9C.Material.SpinPair.lapse_pos (GaussNativeEnergy.volume_pos z))]

theorem sourceInversePhase_actual (z : physicalChart) :
    inversePhase (sourceState z.val)=(GaussNativeEnergy.volume z.val:ℂ) •
      Quantum.operatorMatrix (DiracExteriorMatterAction.diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero) :=by
  have temporal : currentCoframeMatterTemporalPrincipal (sourceCoframe z.val)=
      (Complex.I*(Stage9C.Material.SpinPair.lapse:ℂ)⁻¹) •
        DiracExteriorMatterAction.diracMatrixMatterAction DiracCliffordRepresentation.diracGammaZero :=by
    apply LinearMap.ext
    intro v
    simp only [currentCoframeMatterTemporalPrincipal,temporal_gamma,LinearMap.smul_apply,
      StageNineP286GaugeConnectionVariationDensity.diracMatrixMatterAction_smul_matrix,smul_smul]
  rw [inversePhase,sourceStateVolume_actual]
  change (-Complex.I*(Stage9C.Material.SpinPair.lapse*GaussNativeEnergy.volume z.val:ℝ)) •
    Quantum.operatorMatrix (currentCoframeMatterTemporalPrincipal (sourceCoframe z.val))=_
  rw [temporal,map_smul,smul_smul]
  congr 1
  have nz : (Stage9C.Material.SpinPair.lapse:ℂ)≠0:=
    Complex.ofReal_ne_zero.mpr Stage9C.Material.SpinPair.lapse_pos.ne'
  push_cast
  field_simp
  simp [Complex.I_sq]

theorem sourcePreparedTimeMatrix_actual_normalized (z : physicalChart) :
    (Stage10.ActionNormalization.actionScale:ℂ) • sourcePreparedTimeMatrix (sourceState z.val)=
      (GaussNativeEnergy.volume z.val:ℂ) • Quantum.operatorMatrix Stage10.CanonicalMatter.temporalMother :=by
  rw [sourcePreparedTimeMatrix_normalized,sourceInversePhase_actual,mul_smul_comm,
    ←Quantum.matrix_composition]
  rfl

theorem sourcePreparedTimeMatrix_actual_preparation (z : physicalChart)
    (v : DiracExteriorMatterAction.DiracExteriorMatterCarrier) :
    ((Stage10.ActionNormalization.actionScale:ℂ) • sourcePreparedTimeMatrix (sourceState z.val))*ᵥ
      Quantum.coordinates (Stage10.ChargedPreparation.preparation v)=
        (GaussNativeEnergy.volume z.val:ℂ) • Quantum.coordinates (Stage10.ChargedPreparation.preparation v) :=by
  rw [sourcePreparedTimeMatrix_actual_normalized,Matrix.smul_mulVec,Quantum.matrix_action,
    Stage10.CanonicalMatter.positive_time_preparation]

def sourceTimeWeightFiber (z : SourceCoordinateSlice) : PreparationVacuumSourceFieldFamily.FiberMap :=
  quantizer (sourceTimeWeight (sourceState z))

theorem sourceTimeWeightFiber_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ sourceTimeWeightFiber z.val :=by
  change ContDiffAt ℝ ∞ (fun w=>quantizer (sourceTimeWeight (sourceState w))) z.val
  simp_rw [sourceTimeWeight_original]
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp z.val
    (((sourceActionWeight_smooth _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid z)).comp z.val sourceState_smooth.contDiffAt).const_smul (4:ℂ))

def sourceTimeWeightCore : QuantumTest→ₗ[ℂ] QuantumTest :=
  localMultiplier sourceTimeWeightFiber sourceTimeWeightFiber_smooth

abbrev fullSourceAction (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  CanonicalPhysicalSpatial.physicalAction p+GaussYukawaOperator.originalAction

theorem originalEnergyCoefficient_smooth (s : ActionState) (nondegenerate : s.1.det≠0) (i : Fin 4) :
    ContDiffAt ℝ ∞ (fun w=>originalEnergyCoefficient w i) s :=by
  apply ContDiffAt.mul contDiffAt_const
  refine Fin.cases ?_ (fun j=>?_) i
  · exact (stateDensityLower_smooth s nondegenerate).neg
  · exact (statePrincipal_smooth j.succ s nondegenerate).const_smul (-Complex.I)

theorem originalEnergyFiber_smooth (p : PhysicalMomentum) (s : ActionState)
    (nondegenerate : s.1.det≠0) : ContDiffAt ℝ ∞ (originalEnergyFiber p) s :=by
  have coefficients : ContDiffAt ℝ ∞ originalEnergyCoefficient s :=
    contDiffAt_pi.mpr (originalEnergyCoefficient_smooth s nondegenerate)
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp s
    ((rawFourier p).toContinuousLinearMap.contDiff.contDiffAt.comp s coefficients)

def originalEnergyCore (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z=>originalEnergyFiber p (sourceState z))
    (fun z=>(originalEnergyFiber_smooth p (sourceState z.val) (PreparationVacuumNonlinearFieldCurve.sourceState_valid z).1).comp z.val
      sourceState_smooth.contDiffAt)

def sourceEnergyNormalFiber (p : PhysicalMomentum) (z : SourceCoordinateSlice) : PreparationVacuumSourceFieldFamily.FiberMap :=
  pairFiber (sourceTimeWeight (sourceState z)) (fourierLinear p (stateHamiltonian (sourceState z)))

theorem originalEnergyFiber_normal_order (p : PhysicalMomentum) (z : physicalChart) :
    originalEnergyFiber p (sourceState z.val)=
      sourceTimeWeightFiber z.val*actualFiber p z.val-sourceEnergyNormalFiber p z.val :=by
  have car:=quantized_normal_order (sourceTimeWeight (sourceState z.val))
    (fourierLinear p (stateHamiltonian (sourceState z.val)))
  rw [originalEnergyFiber,originalEnergySymbol_generated p _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid z).2]
  change quantizer (_*_)=_
  unfold sourceEnergyNormalFiber
  exact eq_sub_of_add_eq car.symm

theorem sourceEnergyNormalFiber_smooth (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceEnergyNormalFiber p) z.val :=by
  have h : (fun w=>sourceTimeWeightFiber w*actualFiber p w-originalEnergyFiber p (sourceState w))=ᶠ[𝓝 z.val]
      sourceEnergyNormalFiber p :=by
    filter_upwards [(physicalChart.isOpen.mem_nhds z.property)] with w hw
    rw [originalEnergyFiber_normal_order p ⟨w,hw⟩]
    abel
  apply ContDiffAt.congr_of_eventuallyEq _ h.symm
  exact ((sourceTimeWeightFiber_smooth z).mul (actualFiber_smooth p z)).sub
    ((originalEnergyFiber_smooth p (sourceState z.val) (PreparationVacuumNonlinearFieldCurve.sourceState_valid z).1).comp z.val
      sourceState_smooth.contDiffAt)

def sourceEnergyNormalCore (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  localMultiplier (sourceEnergyNormalFiber p) (sourceEnergyNormalFiber_smooth p)

theorem originalEnergyCore_normal_order (p : PhysicalMomentum) :
    originalEnergyCore p=sourceTimeWeightCore.comp (actualCore p)-sourceEnergyNormalCore p :=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases inside : z∈physicalChart
  · change originalEnergyFiber p (sourceState z) (f z)=
      sourceTimeWeightFiber z (actualFiber p z (f z))-sourceEnergyNormalFiber p z (f z)
    rw [originalEnergyFiber_normal_order p ⟨z,inside⟩]
    rfl
  · have outside : f z=0:=image_eq_zero_of_notMem_tsupport (fun hz=>inside (f.tsupport_subset hz))
    change originalEnergyFiber p (sourceState z) (f z)=
      sourceTimeWeightFiber z (actualFiber p z (f z))-sourceEnergyNormalFiber p z (f z)
    rw [outside,map_zero,map_zero,map_zero,map_zero,sub_zero]

theorem sourceEnergyNormalCore_numberOne (g : NativeHistoryGrade.Label) (one : g.1.val=1)
    (p : PhysicalMomentum) (f : QuantumTest) :
    sourceEnergyNormalCore p (GaussCoreLabel.project g f)=0 :=by
  apply DFunLike.ext
  intro x
  have car:=sourceNumberOne_pairFiber_zero g one (sourceTimeWeight (sourceState x))
    (fourierLinear p (stateHamiltonian (sourceState x)))
  have value:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (f x)) car
  exact value

theorem sourceEnergyNormalCore_actualN1_zero (q : PreparationVacuumPhysicalFeedback.PhysicalResponsePoint)
    (p energyP : PhysicalMomentum) (state : PreparationVacuumElectromagneticIdentity.RestStateIndex)
    (z : ℂ) (t : ℝ) (nonreal : z.im≠0) :
    sourceEnergyNormalCore energyP (PreparationVacuumFieldConstraintResponse.sourceTestApprox q.F
      (sourceActualN1Primal q p state z t))=0 :=by
  have fixed:=sourceActualN1Primal_core q p state z t nonreal
  have actual:=congrArg (sourceEnergyNormalCore energyP) fixed
  simp only [map_add] at actual
  rw [sourceEnergyNormalCore_numberOne CanonicalGradedCurrent.sourceLabel rfl energyP _,
    sourceEnergyNormalCore_numberOne PreparationVacuumPhysicalNumberOneRead.sourceExcitedLabel rfl energyP _,
    zero_add] at actual
  exact actual.symm

/-- The non-matter terms stay in their original action decomposition. -/
def sourceCompleteDensityCore (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  originalEnergyCore p+sourceTimeWeightCore.comp (GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction-retainedCore)

theorem sourceCompleteDensityCore_generated (p : PhysicalMomentum) :
    sourceCompleteDensityCore p=sourceTimeWeightCore.comp (fullSourceAction p)-sourceEnergyNormalCore p :=by
  rw [sourceCompleteDensityCore,originalEnergyCore_normal_order]
  have complete:=physical_action_decomposition p
  change fullSourceAction p=GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+actualCore p-retainedCore at complete
  simp only [complete,LinearMap.comp_sub,LinearMap.comp_add]
  abel

def sourceDensityEnergyRead (p : PhysicalMomentum) (a b : QuantumTest) : ℂ :=
  sourcePair a (sourceCompleteDensityCore p b)

theorem sourceDensityEnergyRead_original_measure (p : PhysicalMomentum) (a b : QuantumTest) :
    sourceDensityEnergyRead p a b=
      ∫z,densityPair a (sourceCompleteDensityCore p b) z ∂GaussHistoryHilbert.configurationMeasure :=
  sourcePair_integral a _

def sourceNormalizedWeightCore : QuantumTest→ₗ[ℂ] QuantumTest :=
  (Stage10.ActionNormalization.actionScale:ℂ) • sourceTimeWeightCore

theorem sourceDensityEnergyRead_actualN1 (q : PreparationVacuumPhysicalFeedback.PhysicalResponsePoint)
    (p energyP : PhysicalMomentum) (state : PreparationVacuumElectromagneticIdentity.RestStateIndex)
    (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (a : QuantumTest) :
    (Stage10.ActionNormalization.actionScale:ℂ)*sourceDensityEnergyRead energyP a
      (PreparationVacuumFieldConstraintResponse.sourceTestApprox q.F (sourceActualN1Primal q p state z t))=
        sourcePair a (sourceNormalizedWeightCore (fullSourceAction energyP
          (PreparationVacuumFieldConstraintResponse.sourceTestApprox q.F (sourceActualN1Primal q p state z t)))) :=by
  rw [sourceDensityEnergyRead,sourceCompleteDensityCore_generated,LinearMap.sub_apply,
    LinearMap.comp_apply,sourceEnergyNormalCore_actualN1_zero q p energyP state z t nonreal,sub_zero]
  unfold sourcePair sourceNormalizedWeightCore
  simp only [LinearMap.smul_apply,map_smul,inner_smul_right]

def sourceUnitActionDefect (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  (sourceNormalizedWeightCore-1).comp (fullSourceAction p)-
    (Stage10.ActionNormalization.actionScale:ℂ) • sourceEnergyNormalCore p

theorem sourceDensityEnergyRead_normalized (p : PhysicalMomentum) (a b : QuantumTest) :
    (Stage10.ActionNormalization.actionScale:ℂ)*sourceDensityEnergyRead p a b=
      sourcePair a (fullSourceAction p b)+sourcePair a (sourceUnitActionDefect p b) :=by
  rw [sourceDensityEnergyRead,sourceCompleteDensityCore_generated]
  unfold sourcePair sourceUnitActionDefect sourceNormalizedWeightCore
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,Module.End.one_apply,
    map_sub,map_smul,inner_sub_right,inner_smul_right,mul_sub]
  ring

def sourceCompressionDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (b : QuantumTest) : H :=
  embed (CanonicalPhysicalSpatial.physicalAction p b)-actualC p F (embed b)

def sourceUncutRetainerDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (b : QuantumTest) : H :=
  embed (GaussYukawaOperator.originalAction b)-actualA p F (embed b)

def sourceActualUnitDefect (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (a b : QuantumTest) : ℂ :=
  sourcePair a (sourceUnitActionDefect p b)+
    inner ℂ (embed a) (sourceCompressionDefect p F b+sourceUncutRetainerDefect p F b)

theorem sourceActualUnitDefect_actualN1 (q : PreparationVacuumPhysicalFeedback.PhysicalResponsePoint)
    (p energyP : PhysicalMomentum) (state : PreparationVacuumElectromagneticIdentity.RestStateIndex)
    (z : ℂ) (t : ℝ) (nonreal : z.im≠0) (a : QuantumTest) :
    let b:=PreparationVacuumFieldConstraintResponse.sourceTestApprox q.F (sourceActualN1Primal q p state z t)
    sourceActualUnitDefect energyP q.F a b=
      sourcePair a ((sourceNormalizedWeightCore-1) (fullSourceAction energyP b))+
        inner ℂ (embed a) (sourceCompressionDefect energyP q.F b+sourceUncutRetainerDefect energyP q.F b) :=by
  dsimp only
  unfold sourceActualUnitDefect sourceUnitActionDefect
  rw [LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    sourceEnergyNormalCore_actualN1_zero q p energyP state z t nonreal,smul_zero,sub_zero]

theorem sourceDensityEnergyRead_actual_time (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (a b : QuantumTest) :
    (Stage10.ActionNormalization.actionScale:ℂ)*sourceDensityEnergyRead p a b=
      inner ℂ (embed a) ((actualC p F+actualA p F) (embed b))+sourceActualUnitDefect p F a b :=by
  rw [sourceDensityEnergyRead_normalized]
  unfold sourcePair sourceActualUnitDefect sourceCompressionDefect sourceUncutRetainerDefect fullSourceAction
  simp only [sourcePair,LinearMap.add_apply,map_add,add_apply,inner_add_right,inner_sub_right]
  ring

theorem sourceScalarActionUnit_iff (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (a b : QuantumTest) :
    (Stage10.ActionNormalization.actionScale:ℂ)*sourceDensityEnergyRead p a b=
      inner ℂ (embed a) ((actualC p F+actualA p F) (embed b)) ↔
      sourceActualUnitDefect p F a b=0 :=by
  rw [sourceDensityEnergyRead_actual_time,add_eq_left]

theorem sourceActualTime_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    HasDerivAt (partialEvolution (actualC p F) (actualA p F) 56)
      (partialEvolution (actualC p F) (actualA p F) 56 t*((-Complex.I) • (actualC p F+actualA p F))) t :=by
  simpa only [actualGenerator_source] using actual_prefix_derivative p F t

theorem sourceActualPhysicalTime_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    HasDerivAt (fun s=>physicalTime p F s 0)
      (physicalTime p F t 0*((-Complex.I) • (actualC p F+actualA p F))) t :=by
  rw [actual_time_finitePrefix p F t]
  apply (sourceActualTime_generated p F t).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun s=>actual_time_finitePrefix p F s)

def sourceCanonicalMomentumInverse (s : ActionState) : SourceMatrix :=
  statePhase s*Quantum.operatorMatrix YangMills.FullPairing.flipMatter

theorem sourcePhase_timeMomentum_right (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) : statePhase s*inversePhase s=1 :=by
  have volume : stateVolume s≠0:=Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nondegenerate)
  have factor : (Complex.I*(stateVolume s)⁻¹)*(-Complex.I*stateVolume s)=1 :=by
    calc
      _= -(Complex.I*Complex.I)*((stateVolume s)⁻¹*stateVolume s) :=by ring
      _=1 :=by rw [Complex.I_mul_I,inv_mul_cancel₀ volume];norm_num
  rw [statePhase,inversePhase,smul_mul_smul,
    Ring.inverse_mul_cancel _ (principalMatrix_regular s.1 regular),factor,one_smul]

theorem sourceCanonicalMomentumInverse_generated (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) :
    sourceCanonicalMomentumInverse s*((Stage10.ActionNormalization.actionScale:ℂ) • sourcePreparedTimeMatrix s)=1 :=by
  have flip : Quantum.operatorMatrix YangMills.FullPairing.flipMatter*
      Quantum.operatorMatrix YangMills.FullPairing.flipMatter=1 :=by
    rw [←Quantum.matrix_composition]
    have twice : YangMills.FullPairing.flipMatter.comp YangMills.FullPairing.flipMatter=1 :=by
      apply LinearMap.ext
      exact YangMills.FullPairing.flipMatter_twice
    rw [twice,map_one]
  rw [sourcePreparedTimeMatrix_normalized,sourceCanonicalMomentumInverse]
  calc
    _=statePhase s*(Quantum.operatorMatrix YangMills.FullPairing.flipMatter*
      Quantum.operatorMatrix YangMills.FullPairing.flipMatter)*inversePhase s :=by simp only [mul_assoc]
    _=1 :=by rw [flip,mul_one,sourcePhase_timeMomentum_right s nondegenerate regular]

theorem sourceCanonicalMomentum_energyCoefficient_return (s : ActionState) (nondegenerate : s.1.det≠0)
    (regular : coframeTemporalPrincipalScalar s.1≠0) (i : Fin 4) :
    sourceCanonicalMomentumInverse s*((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient s i)=
      stateHamiltonian s i :=by
  rw [originalEnergyCoefficient_generated s regular i,←smul_mul_assoc,←mul_assoc,
    sourceCanonicalMomentumInverse_generated s nondegenerate regular,one_mul]

def sourceCanonicalEnergyFiber (p : PhysicalMomentum) (z : SourceCoordinateSlice) : PreparationVacuumSourceFieldFamily.FiberMap :=
  quantizer (fourierLinear p (fun i=>sourceCanonicalMomentumInverse (sourceState z)*
    ((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient (sourceState z) i)))

theorem sourceCanonicalEnergyFiber_original (p : PhysicalMomentum) (z : physicalChart) :
    sourceCanonicalEnergyFiber p z.val=actualFiber p z.val :=by
  have coefficients : (fun i=>sourceCanonicalMomentumInverse (sourceState z.val)*
      ((Stage10.ActionNormalization.actionScale:ℂ) • originalEnergyCoefficient (sourceState z.val) i))=
      stateHamiltonian (sourceState z.val) :=
    funext (sourceCanonicalMomentum_energyCoefficient_return _ (PreparationVacuumNonlinearFieldCurve.sourceState_valid z).1 (PreparationVacuumNonlinearFieldCurve.sourceState_valid z).2)
  rw [sourceCanonicalEnergyFiber,coefficients]
  rfl

theorem sourceCanonicalEnergyFiber_smooth (p : PhysicalMomentum) (z : physicalChart) :
    ContDiffAt ℝ ∞ (sourceCanonicalEnergyFiber p) z.val :=by
  apply (actualFiber_smooth p z).congr_of_eventuallyEq
  filter_upwards [physicalChart.isOpen.mem_nhds z.property] with w hw
  exact sourceCanonicalEnergyFiber_original p ⟨w,hw⟩

def sourceCanonicalEnergyCore (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  localMultiplier (sourceCanonicalEnergyFiber p) (sourceCanonicalEnergyFiber_smooth p)

theorem sourceCanonicalEnergyCore_original (p : PhysicalMomentum) :
    sourceCanonicalEnergyCore p=actualCore p :=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change sourceCanonicalEnergyFiber p z (f z)=actualFiber p z (f z)
  by_cases inside : z∈physicalChart
  · rw [sourceCanonicalEnergyFiber_original p ⟨z,inside⟩]
  · have outside : f z=0:=image_eq_zero_of_notMem_tsupport (fun hz=>inside (f.tsupport_subset hz))
    rw [outside,map_zero,map_zero]

def sourceCanonicalCompleteCore (p : PhysicalMomentum) : QuantumTest→ₗ[ℂ] QuantumTest :=
  GaussNativeForm.nativeAction+GaussCoframeForm.coframeAction+sourceCanonicalEnergyCore p-retainedCore

theorem sourceCanonicalCompleteCore_original (p : PhysicalMomentum) :
    sourceCanonicalCompleteCore p=fullSourceAction p :=by
  rw [sourceCanonicalCompleteCore,sourceCanonicalEnergyCore_original]
  exact (physical_action_decomposition p).symm

theorem sourceCanonicalCompleteRead_actual_time (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (a b : QuantumTest) :
    sourcePair a (sourceCanonicalCompleteCore p b)=
      inner ℂ (embed a) ((actualC p F+actualA p F) (embed b))+
        inner ℂ (embed a) (sourceCompressionDefect p F b+sourceUncutRetainerDefect p F b) :=by
  rw [sourceCanonicalCompleteCore_original]
  unfold sourcePair fullSourceAction sourceCompressionDefect sourceUncutRetainerDefect
  simp only [LinearMap.add_apply,map_add,add_apply,inner_add_right,inner_sub_right]
  ring

end LowEnergy.PreparationPhysicalActionUnits
