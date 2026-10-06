import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceRestMatterLight
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeActionFieldLift
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeActionJets
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectromagneticIdentity
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField StageNineGlobalIntegratedAction
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open StageNineP286GaugeConnectionVariationDensity StageNineMatterVariation
open StageNineDynamicBreakingVacuum Stage9C.Dynamics.Homogeneous
open PreparationCoordinates StageNineP286GaugeAuxiliaryVariation StageNineDiracDualFormNativeMatterVariation
open SU7MotherLieAlgebra SU7MotherGaugeTheory DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair Stage10 Stage10.CanonicalMatter
open YangMills.FullPairing Electromagnetic.ExternalState Stage9DEF Stage9DEF.Compatibility
open SourcePropagationNativeActionHessian PreparationVacuumMixedFieldReturn PreparationVacuumLowerClassical
open StageNineDiracKineticLocalSpinDensity StageNineMatterCovariantDerivativeAffine
open StageNineP286GaugeConnectionActionVariation StageNineP286GaugeConnectionVariation
open StageNineCoframeLocalDifferentiability PreparationVacuumNativeSourceRestriction
open scoped BigOperators Matrix InnerProductSpace ContDiff

def sourceTemporalGaugeDirection (direction : P286LieBlockData) : Field289 := fun field=>
  if inside : 9≤field.val ∧ field.val<21 then
    rawCoordinates (p286CoordinateEquiv direction) ⟨field.val-9,by omega⟩ else 0

private theorem temporalGauge_slot (direction : P286LieBlockData) (mu : Fin 4) (index : Fin 12) :
    sourceTemporalGaugeDirection direction (gaugeSlot mu index)=
      if mu=0 then rawCoordinates (p286CoordinateEquiv direction) index else 0 := by
  by_cases time : mu=0
  · subst mu
    simp only [sourceTemporalGaugeDirection,gaugeSlot,Fin.val_mk,if_true]
    rw [dif_pos (by constructor <;> omega)]
    apply congrArg (rawCoordinates (p286CoordinateEquiv direction))
    apply Fin.ext
    simp
  · have outside : ¬(9≤(gaugeSlot mu index).val ∧ (gaugeSlot mu index).val<21) := by
      simp only [gaugeSlot,Fin.val_mk]
      have value : mu.val≠0 := by intro equal; apply time; exact Fin.ext equal
      omega
    simp only [sourceTemporalGaugeDirection,dif_neg outside,if_neg time]

theorem sourceTemporalGaugeDirection_generated (direction : P286LieBlockData) (mu : Fin 4) :
    p286CoordinateEquiv.symm (fieldGauge (sourceTemporalGaugeDirection direction) mu)=
      if mu=0 then direction else 0 := by
  unfold fieldGauge
  simp only [temporalGauge_slot]
  by_cases time : mu=0
  · simp only [if_pos time]
    have reconstruction : (∑ index : Fin 12,rawCoordinates (p286CoordinateEquiv direction) index • originalUnit index)=
        p286CoordinateEquiv direction := by
      exact (raw_original_expansion (show NativeLie from p286CoordinateEquiv direction)).symm
    rw [reconstruction,LinearEquiv.symm_apply_apply]
  · simp [time]

def actualRestPairConfiguration (left right : RestStateIndex) : StageNineHolonomicConfiguration :=
  { actual with
    matter := fun point=>actualRestStatePreparation right (actual.matter point)
    conjugateMatter := fun point=>(actual.conjugateMatter point).comp (canonicalDual (actualRestStatePreparation left)) }

def actualRestPairPoint (point : BasePoint) (left right : RestStateIndex) : StageNineContinuumPointField :=
  toContinuumPointField (actualRestPairConfiguration left right) point

def sourceGaugeMatterDirection (field : StageNineContinuumPointField) (force : Field289)
    (mu : Fin 4) : DiracExteriorMatterCarrier :=
  diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (fieldGauge force mu))) field.matter

def actualRestNativeGaugeCurrent (point : BasePoint) (left right : RestStateIndex) (force : Field289) : ℝ :=
  generatedVolumeDensity (actualRestPairPoint point left right)*
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (actualRestPairPoint point left right) (sourceGaugeMatterDirection (actualRestPairPoint point left right) force)

theorem actualRestTemporalGaugeCurrent (direction : Fin 3) (point : BasePoint) (left right : RestStateIndex) :
    actualRestNativeGaugeCurrent point left right (sourceTemporalGaugeDirection (sourceColorP286Generator direction))=
      ((Stage10.ActionNormalization.phaseMomentum : ℂ)*sourceRestChargeMixing direction left right).re := by
  unfold actualRestNativeGaugeCurrent matterGaugeConnectionFirstVariationDensity
    matterGaugeConnectionVariationVector matterGaugeKineticSum
  simp only [matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
  have frame : (actualRestPairPoint point left right).coframe=homogeneousCoframe lapse := by
    change actual.coframe point=_
    exact congrFun actual_coframe point
  have volume : generatedVolumeDensity (actualRestPairPoint point left right)=lapse := by
    change |((actualRestPairPoint point left right).coframe).det|=lapse
    rw [frame]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  rw [volume]
  simp only [sourceGaugeMatterDirection,sourceTemporalGaugeDirection_generated]
  have vector : (∑ mu : Fin 4,diracMatrixMatterAction
      (inverseCoframeDiracGamma {coframe := (actualRestPairPoint point left right).coframe,derivative := 0} mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (if mu=0 then sourceColorP286Generator direction else 0))
        (actualRestPairPoint point left right).matter))=
      ((lapse : ℂ)⁻¹) • diracMatrixMatterAction diracGammaZero
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (actualRestPairPoint point left right).matter) := by
    rw [Finset.sum_eq_single 0]
    · rw [frame,homogeneousInverseGamma lapse lapse_pos.ne']
      simp only [Fin.isValue,Matrix.cons_val_zero,diracGamma,
        diracMatrixMatterAction_smul_matrix,if_true,Complex.ofReal_inv]
    · intro mu _ off
      simp [off]
    · simp
  rw [vector]
  change lapse*((actual.conjugateMatter point)
    (canonicalDual (actualRestStatePreparation left)
      (Complex.I • ((lapse : ℂ)⁻¹ • diracMatrixMatterAction diracGammaZero
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (actualRestStatePreparation right (actual.matter point))))))).re=_
  rw [map_smul,map_smul,map_smul,map_smul]
  have current:=actualRestState_current_mixing direction point left right
  simp only [currentAction,LinearMap.smul_apply,LinearMap.comp_apply,diracGamma,Matrix.cons_val_zero] at current
  rw [map_smul,map_smul] at current
  rw [←current]
  simp only [←Complex.ofReal_inv,smul_eq_mul,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,sub_zero,zero_sub]
  field_simp [lapse_pos.ne']
  ring

def sourceNativeGaugeCurrentComplex (point : BasePoint) (field : StageNineContinuumPointField)
    (force : Field289) : ℂ :=
  (generatedVolumeDensity field:ℂ)*matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
    (matterGaugeConnectionVariationVector positiveSmoothUnifiedSource 0 point field (sourceGaugeMatterDirection field force))

private theorem temporalGauge_complex (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : P286LieBlockData) (frame : field.coframe=homogeneousCoframe lapse) :
    sourceNativeGaugeCurrentComplex point field (sourceTemporalGaugeDirection direction)=
      field.conjugateMatter (Complex.I • diracMatrixMatterAction diracGammaZero
        (diracExteriorMotherLieAction (p286LieBlockEmbed direction) field.matter)) := by
  have volume : generatedVolumeDensity field=lapse := by
    change |field.coframe.det|=lapse
    rw [frame]
    simp [homogeneousCoframe,Matrix.det_diagonal,Fin.prod_univ_four,abs_of_pos lapse_pos]
  unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
  rw [volume]
  simp only [matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart,
    sourceGaugeMatterDirection,sourceTemporalGaugeDirection_generated]
  have vector : (∑ mu : Fin 4,diracMatrixMatterAction
      (inverseCoframeDiracGamma {coframe := field.coframe,derivative := 0} mu)
      (diracExteriorMotherLieAction (p286LieBlockEmbed (if mu=0 then direction else 0)) field.matter))=
      ((lapse:ℂ)⁻¹) • diracMatrixMatterAction diracGammaZero
        (diracExteriorMotherLieAction (p286LieBlockEmbed direction) field.matter) := by
    rw [Finset.sum_eq_single 0]
    · rw [frame,homogeneousInverseGamma lapse lapse_pos.ne']
      simp only [Fin.isValue,Matrix.cons_val_zero,diracGamma,
        diracMatrixMatterAction_smul_matrix,if_true,Complex.ofReal_inv]
    · intro mu _ off
      simp [off]
    · simp
  rw [vector,map_smul,map_smul,map_smul]
  simp only [smul_eq_mul]
  have nonzero : (lapse:ℂ)≠0 := by exact_mod_cast lapse_pos.ne'
  field_simp [nonzero]

theorem actualRestTemporalGaugeCurrent_complex (direction : Fin 3) (point : BasePoint)
    (left right : RestStateIndex) :
    sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right)
      (sourceTemporalGaugeDirection (sourceColorP286Generator direction))=
      (Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right := by
  rw [temporalGauge_complex point _ _ (congrFun actual_coframe point)]
  exact actualRestState_current_mixing direction point left right

def sourceCurrentPhase (part : Fin 2) : ℂ := if part=0 then 1 else -Complex.I

def actualRestPairPhaseConfiguration (part : Fin 2) (left right : RestStateIndex) : StageNineHolonomicConfiguration :=
  {actualRestPairConfiguration left right with
    matter := fun point=>sourceCurrentPhase part • actualRestStatePreparation right (actual.matter point)}

def actualRestPairPhasePoint (part : Fin 2) (point : BasePoint) (left right : RestStateIndex) :
    StageNineContinuumPointField := toContinuumPointField (actualRestPairPhaseConfiguration part left right) point

def actualRestNativeGaugeQuadrature (part : Fin 2) (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) : ℝ :=
  generatedVolumeDensity (actualRestPairPhasePoint part point left right)*
    matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 point
      (actualRestPairPhasePoint part point left right)
      (sourceGaugeMatterDirection (actualRestPairPhasePoint part point left right) force)

theorem actualRestTemporalGaugeQuadrature (part : Fin 2) (direction : Fin 3) (point : BasePoint)
    (left right : RestStateIndex) :
    actualRestNativeGaugeQuadrature part point left right
      (sourceTemporalGaugeDirection (sourceColorP286Generator direction))=
      if part=0 then ((Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right).re
      else ((Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right).im := by
  have realPart (field : StageNineContinuumPointField) (force : Field289) :
      generatedVolumeDensity field*matterGaugeConnectionFirstVariationDensity positiveSmoothUnifiedSource 0 point
        field (sourceGaugeMatterDirection field force)=(sourceNativeGaugeCurrentComplex point field force).re := by
    simp only [sourceNativeGaugeCurrentComplex,matterGaugeConnectionFirstVariationDensity,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  unfold actualRestNativeGaugeQuadrature
  rw [realPart,temporalGauge_complex point _ _ (congrFun actual_coframe point)]
  change ((actual.conjugateMatter point) (canonicalDual (actualRestStatePreparation left)
    (Complex.I • diracMatrixMatterAction diracGammaZero
      (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
        (sourceCurrentPhase part • actualRestStatePreparation right (actual.matter point)))))).re=_
  simp only [map_smul,smul_smul]
  have mixing:=actualRestState_current_mixing direction point left right
  simp only [currentAction,LinearMap.smul_apply,LinearMap.comp_apply,diracGamma,Matrix.cons_val_zero,map_smul] at mixing
  change (Complex.I * sourceCurrentPhase part *
    (actual.conjugateMatter point) (canonicalDual (actualRestStatePreparation left)
      (diracMatrixMatterAction diracGammaZero
        (diracExteriorMotherLieAction (p286LieBlockEmbed (sourceColorP286Generator direction))
          (actualRestStatePreparation right (actual.matter point)))))).re=_
  have scaled:=congrArg (fun z : ℂ=>(sourceCurrentPhase part*z).re) mixing
  convert! scaled using 1
  · congr 1
    change Complex.I*sourceCurrentPhase part*_ = sourceCurrentPhase part*(Complex.I*_)
    ring
  · fin_cases part <;> simp [sourceCurrentPhase,Complex.mul_re]


def actualRestNativeGaugeKineticCurve (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) (parameter : ℝ) : ℝ :=
  let field:=actualRestPairPoint point left right
  generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
    (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
      (field.matterCovariantDerivative+parameter • sourceGaugeMatterDirection field force))

private def directionDensity (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : Fin 4→DiracExteriorMatterCarrier) : ℝ :=
  matterCovariantDerivativeFirstVariationDensity positiveSmoothUnifiedSource 0 point field direction

private theorem nativeGaugeKinetic_affine (point : BasePoint) (field : StageNineContinuumPointField)
    (direction : Fin 4→DiracExteriorMatterCarrier) (parameter : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
        (field.matterCovariantDerivative+parameter • direction))=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point field+
        parameter*(generatedVolumeDensity field*directionDensity point field direction) := by
  change generatedVolumeDensity field*
    (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field
        (field.matterCovariantDerivative+parameter • direction))).re=
    generatedVolumeDensity field*
      (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
        (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field field.matterCovariantDerivative)).re+_
  rw [matterCovariantDerivativeVariationVector_add,map_add,Complex.add_re]
  have scaled : (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      (matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field (parameter • direction))).re=
      parameter*directionDensity point field direction := by
    rw [matterCovariantDerivativeVariationVector_real_smul]
    change (matterDualFrameRelative positiveSmoothUnifiedSource 0 point field.conjugateMatter
      ((parameter:ℂ) • matterCovariantDerivativeVariationVector positiveSmoothUnifiedSource 0 point field direction)).re=_
    rw [map_smul]
    simp only [smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rfl
  rw [scaled]
  ring


theorem actualRestNativeGaugeKineticCurve_affine (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) (parameter : ℝ) :
    actualRestNativeGaugeKineticCurve point left right force parameter=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
        (actualRestPairPoint point left right)+parameter*actualRestNativeGaugeCurrent point left right force := by
  exact nativeGaugeKinetic_affine point (actualRestPairPoint point left right)
    (sourceGaugeMatterDirection (actualRestPairPoint point left right) force) parameter

theorem actualRestNativeGaugeKineticCurve_hasDerivAt (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) (parameter : ℝ) :
    HasDerivAt (actualRestNativeGaugeKineticCurve point left right force)
      (actualRestNativeGaugeCurrent point left right force) parameter := by
  have curve:=((hasDerivAt_id parameter).mul_const (actualRestNativeGaugeCurrent point left right force)).const_add
    (generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (actualRestPairPoint point left right))
  convert! curve using 1
  · funext r
    exact actualRestNativeGaugeKineticCurve_affine point left right force r
  · simp

theorem actualRestTemporalGaugeKineticCurve_hasDerivAt (direction : Fin 3) (point : BasePoint)
    (left right : RestStateIndex) (parameter : ℝ) :
    HasDerivAt (actualRestNativeGaugeKineticCurve point left right
      (sourceTemporalGaugeDirection (sourceColorP286Generator direction)))
      (((Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right).re) parameter := by
  rw [←actualRestTemporalGaugeCurrent direction point left right]
  exact actualRestNativeGaugeKineticCurve_hasDerivAt point left right _ parameter


def nativeTemporalGaugeValueRay (jet : NativeFirstJet) (direction : P286LieBlockData) (parameter : ℝ) : NativeFirstJet :=
  (jet.1+parameter • sourceTemporalGaugeDirection direction,jet.2)

private theorem temporalGauge_outside (direction : P286LieBlockData) (field : Fin 289)
    (outside : field.val<9 ∨ 21≤field.val) : sourceTemporalGaugeDirection direction field=0 := by
  exact dif_neg (by omega)

private theorem temporalGauge_primal (direction : P286LieBlockData) (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    fieldPrimal (sourceTemporalGaugeDirection direction) part spin color=0 := by
  apply temporalGauge_outside
  right
  simp only [primalSlot,Fin.val_mk]
  omega

private theorem temporalGauge_dual (direction : P286LieBlockData) (part : Fin 2) (spin : Fin 4) (color : Fin 3) :
    fieldDual (sourceTemporalGaugeDirection direction) part spin color=0 := by
  apply temporalGauge_outside
  right
  simp only [dualSlot,Fin.val_mk]
  omega

private theorem temporalGauge_primal_shift (value : Field289) (direction : P286LieBlockData) (parameter : ℝ)
    (spin : Fin 4) (color : Fin 3) :
    fieldPrimalComplex (value+parameter • sourceTemporalGaugeDirection direction) spin color=
      fieldPrimalComplex value spin color := by
  simp only [fieldPrimalComplex,fieldPrimal,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have zero0:=temporalGauge_primal direction 0 spin color
  have zero1:=temporalGauge_primal direction 1 spin color
  change sourceTemporalGaugeDirection direction (primalSlot 0 spin color)=0 at zero0
  change sourceTemporalGaugeDirection direction (primalSlot 1 spin color)=0 at zero1
  rw [zero0,zero1]
  simp

private theorem temporalGauge_dual_shift (value : Field289) (direction : P286LieBlockData) (parameter : ℝ)
    (spin : Fin 4) (color : Fin 3) :
    fieldDualComplex (value+parameter • sourceTemporalGaugeDirection direction) spin color=
      fieldDualComplex value spin color := by
  simp only [fieldDualComplex,fieldDual,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  have zero0:=temporalGauge_dual direction 0 spin color
  have zero1:=temporalGauge_dual direction 1 spin color
  change sourceTemporalGaugeDirection direction (dualSlot 0 spin color)=0 at zero0
  change sourceTemporalGaugeDirection direction (dualSlot 1 spin color)=0 at zero1
  rw [zero0,zero1]
  simp

theorem nativeTemporalGaugeValueRay_matter (jet : NativeFirstJet) (direction : P286LieBlockData) (parameter : ℝ) :
    nativeMatterValue (nativeTemporalGaugeValueRay jet direction parameter)=nativeMatterValue jet := by
  simp only [nativeMatterValue,nativeTemporalGaugeValueRay,primalInsertion,temporalGauge_primal_shift]

theorem nativeTemporalGaugeValueRay_dual (jet : NativeFirstJet) (direction : P286LieBlockData) (parameter : ℝ) :
    nativeDualValue (nativeTemporalGaugeValueRay jet direction parameter)=nativeDualValue jet := by
  unfold nativeDualValue
  congr 1
  apply LinearMap.ext
  intro v
  simp only [dualInsertion,nativeTemporalGaugeValueRay,temporalGauge_dual_shift]

theorem nativeTemporalGaugeValueRay_coframe (jet : NativeFirstJet) (direction : P286LieBlockData) (parameter : ℝ) :
    (nativeJetPoint (nativeTemporalGaugeValueRay jet direction parameter)).coframe=(nativeJetPoint jet).coframe := by
  change actual.coframe 0+fieldCoframe (jet.1+parameter • sourceTemporalGaugeDirection direction)=_
  congr 1
  funext row mu
  have outside : sourceTemporalGaugeDirection direction (coframeSlot row mu)=0 := by
    apply temporalGauge_outside
    right
    simp only [coframeSlot,Fin.val_mk]
    omega
  simp only [fieldCoframe,Pi.add_apply,Pi.smul_apply,smul_eq_mul,outside,mul_zero,add_zero]


private theorem temporalGauge_lorentz_shift (value : Field289) (direction : P286LieBlockData) (parameter : ℝ) :
    lorentzInsertionCLM (value+parameter • sourceTemporalGaugeDirection direction)=lorentzInsertionCLM value := by
  have fields : fieldLorentz (value+parameter • sourceTemporalGaugeDirection direction)=fieldLorentz value := by
    funext mu a
    have outside : sourceTemporalGaugeDirection direction (lorentzSlot mu a)=0 := by
      apply temporalGauge_outside
      right
      simp only [lorentzSlot,Fin.val_mk]
      omega
    simp only [fieldLorentz,Pi.add_apply,Pi.smul_apply,smul_eq_mul,outside,mul_zero,add_zero]
  change PreparationVacuumGaugeSourceInjection.lorentzLinear
    (fieldLorentz (value+parameter • sourceTemporalGaugeDirection direction))=
    PreparationVacuumGaugeSourceInjection.lorentzLinear (fieldLorentz value)
  rw [fields]

private theorem temporalGauge_connection_shift (value : Field289) (direction : P286LieBlockData)
    (parameter : ℝ) (mu : Fin 4) :
    p286CoordinateEquiv.symm (fieldGauge (value+parameter • sourceTemporalGaugeDirection direction) mu)=
      p286CoordinateEquiv.symm (fieldGauge value mu)+parameter • (if mu=0 then direction else 0) := by
  rw [fieldGauge_add,fieldGauge_smul,map_add,map_smul,sourceTemporalGaugeDirection_generated]

theorem nativeTemporalGaugeValueRay_covariant (jet : NativeFirstJet) (direction : P286LieBlockData)
    (parameter : ℝ) (mu : Fin 4) :
    nativeMatterCovariant (nativeTemporalGaugeValueRay jet direction parameter) mu=
      nativeMatterCovariant jet mu+parameter • sourceGaugeMatterDirection (nativeJetPoint jet)
        (sourceTemporalGaugeDirection direction) mu := by
  have rotation : rotatedPrimalDerivative (nativeTemporalGaugeValueRay jet direction parameter) mu=
      rotatedPrimalDerivative jet mu := by
    simp only [rotatedPrimalDerivative,nativeTemporalGaugeValueRay,temporalGauge_primal_shift]
  unfold nativeMatterCovariant
  rw [rotation,nativeTemporalGaugeValueRay_matter]
  change _+diracMatrixMatterAction
      (PointwiseDiracSpinConnectionLift.diracSpinConnectionLift
        (actual.gravityConnection 0+lorentzInsertionCLM (jet.1+parameter • sourceTemporalGaugeDirection direction)) mu)
      (nativeMatterValue jet)+
    diracExteriorMotherLieAction
      (p286LieBlockEmbed (actual.gaugeConnection 0 mu+
        p286CoordinateEquiv.symm (fieldGauge (jet.1+parameter • sourceTemporalGaugeDirection direction) mu)))
      (nativeMatterValue jet)=_
  rw [temporalGauge_lorentz_shift,temporalGauge_connection_shift]
  rw [←add_assoc,p286LieBlockEmbed_add,StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add]
  rw [p286LieBlockEmbed_real_smul,StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul]
  simp only [sourceGaugeMatterDirection,sourceTemporalGaugeDirection_generated,nativeJetPoint,
    LinearMap.add_apply,LinearMap.smul_apply]
  change (_ : DiracExteriorMatterCarrier)+(_ : DiracExteriorMatterCarrier)+
    ((_ : DiracExteriorMatterCarrier)+parameter • (_ : DiracExteriorMatterCarrier))=_
  abel

theorem nativeTemporalGaugeValueRay_kinetic_affine (jet : NativeFirstJet) (direction : P286LieBlockData)
    (parameter : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
      (nativeJetPoint (nativeTemporalGaugeValueRay jet direction parameter))=
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet)+
      parameter*(sourceNativeGaugeCurrentComplex 0 (nativeJetPoint jet) (sourceTemporalGaugeDirection direction)).re := by
  have derivative : (nativeJetPoint (nativeTemporalGaugeValueRay jet direction parameter)).matterCovariantDerivative=
      (nativeJetPoint jet).matterCovariantDerivative+parameter • sourceGaugeMatterDirection (nativeJetPoint jet)
        (sourceTemporalGaugeDirection direction) := by
    funext mu
    exact nativeTemporalGaugeValueRay_covariant jet direction parameter mu
  have dual : (nativeJetPoint (nativeTemporalGaugeValueRay jet direction parameter)).conjugateMatter=
      (nativeJetPoint jet).conjugateMatter := nativeTemporalGaugeValueRay_dual jet direction parameter
  have equality : generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
      (nativeJetPoint (nativeTemporalGaugeValueRay jet direction parameter))=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
        (withP286GaugeConnectionJets (nativeJetPoint jet) (p286CurvatureCoordinate (nativeJetPoint jet))
          (nativeJetPoint jet).scalarCovariantDerivative
          ((nativeJetPoint jet).matterCovariantDerivative+parameter • sourceGaugeMatterDirection (nativeJetPoint jet)
            (sourceTemporalGaugeDirection direction))) := by
    unfold generatedDensitizedContinuumMatterKineticDensity
    simp only [generatedVolumeDensity,nativeTemporalGaugeValueRay_coframe,dual,
      generatedContinuumMatterKineticVector,matterCovariantDerivativeVariationVector,matterCovariantDerivativeKineticSum,
      derivative,withP286GaugeConnectionJets]
  rw [equality,nativeGaugeKinetic_affine]
  simp only [sourceNativeGaugeCurrentComplex,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,directionDensity,matterCovariantDerivativeFirstVariationDensity,
    matterGaugeConnectionVariationVector,matterGaugeKineticSum]
  rfl


theorem nativeTemporalGaugeValueRay_hasDerivAt (jet : NativeFirstJet) (direction : P286LieBlockData) (parameter : ℝ) :
    HasDerivAt (fun r=>generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
      (nativeJetPoint (nativeTemporalGaugeValueRay jet direction r)))
      (sourceNativeGaugeCurrentComplex 0 (nativeJetPoint jet) (sourceTemporalGaugeDirection direction)).re parameter := by
  have curve:=((hasDerivAt_id parameter).mul_const
    (sourceNativeGaugeCurrentComplex 0 (nativeJetPoint jet) (sourceTemporalGaugeDirection direction)).re).const_add
      (generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0 (nativeJetPoint jet))
  convert! curve using 1
  · funext r
    exact nativeTemporalGaugeValueRay_kinetic_affine jet direction r
  · simp


def actualRestNativeGaugeQuadratureCurve (part : Fin 2) (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) (parameter : ℝ) : ℝ :=
  let field:=actualRestPairPhasePoint part point left right
  generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
    (withP286GaugeConnectionJets field (p286CurvatureCoordinate field) field.scalarCovariantDerivative
      (field.matterCovariantDerivative+parameter • sourceGaugeMatterDirection field force))

theorem actualRestNativeGaugeQuadratureCurve_hasDerivAt (part : Fin 2) (point : BasePoint)
    (left right : RestStateIndex) (force : Field289) (parameter : ℝ) :
    HasDerivAt (actualRestNativeGaugeQuadratureCurve part point left right force)
      (actualRestNativeGaugeQuadrature part point left right force) parameter := by
  have affine (r : ℝ) : actualRestNativeGaugeQuadratureCurve part point left right force r=
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
        (actualRestPairPhasePoint part point left right)+r*actualRestNativeGaugeQuadrature part point left right force :=
    nativeGaugeKinetic_affine point (actualRestPairPhasePoint part point left right)
      (sourceGaugeMatterDirection (actualRestPairPhasePoint part point left right) force) r
  have curve:=((hasDerivAt_id parameter).mul_const (actualRestNativeGaugeQuadrature part point left right force)).const_add
    (generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 point
      (actualRestPairPhasePoint part point left right))
  convert! curve using 1
  · exact funext affine
  · simp

private theorem sourceGaugeMatterDirection_add (field : StageNineContinuumPointField) (first second : Field289) :
    sourceGaugeMatterDirection field (first+second)=sourceGaugeMatterDirection field first+sourceGaugeMatterDirection field second := by
  funext mu
  simp only [sourceGaugeMatterDirection,fieldGauge_add,map_add,p286LieBlockEmbed_add,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_add,LinearMap.add_apply,Pi.add_apply]

private theorem sourceGaugeMatterDirection_smul (field : StageNineContinuumPointField) (force : Field289) (parameter : ℝ) :
    sourceGaugeMatterDirection field (parameter • force)=parameter • sourceGaugeMatterDirection field force := by
  funext mu
  simp only [sourceGaugeMatterDirection,fieldGauge_smul,map_smul,p286LieBlockEmbed_real_smul,
    StageNineP286GaugeConnectionVariation.diracExteriorMotherLieAction_real_smul,LinearMap.smul_apply]
  rfl

def sourceNativeGaugeCurrentLinear (point : BasePoint) (field : StageNineContinuumPointField) : Field289 →ₗ[ℝ] ℝ where
  toFun force:=generatedVolumeDensity field*directionDensity point field (sourceGaugeMatterDirection field force)
  map_add' first second:=by
    rw [sourceGaugeMatterDirection_add]
    unfold directionDensity
    rw [matterCovariantDerivativeFirstVariationDensity_add]
    ring
  map_smul' parameter force:=by
    rw [sourceGaugeMatterDirection_smul]
    unfold directionDensity
    rw [matterCovariantDerivativeFirstVariationDensity_real_smul]
    simp only [RingHom.id_apply,smul_eq_mul]
    ring

theorem sourceNativeGaugeCurrentLinear_complex (point : BasePoint) (field : StageNineContinuumPointField) (force : Field289) :
    sourceNativeGaugeCurrentLinear point field force=(sourceNativeGaugeCurrentComplex point field force).re := by
  simp only [sourceNativeGaugeCurrentLinear,sourceNativeGaugeCurrentComplex,directionDensity,
    matterCovariantDerivativeFirstVariationDensity,matterGaugeConnectionVariationVector,
    matterCovariantDerivativeVariationVector,matterGaugeKineticSum,matterCovariantDerivativeKineticSum,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

def actualRestNativeForcingCovector (part : Fin 2) (point : BasePoint) (left right : RestStateIndex) : Field289 :=
  fun field=>sourceNativeGaugeCurrentLinear point (actualRestPairPhasePoint part point left right) (Pi.single field 1)

theorem actualRestNativeForcingCovector_generated (part : Fin 2) (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) :
    (∑ field : Fin 289,force field*actualRestNativeForcingCovector part point left right field)=
      actualRestNativeGaugeQuadrature part point left right force := by
  have reconstruction : force=∑ field : Fin 289,force field • (Pi.single field 1 : Field289) := by
    ext field
    simp [Pi.single_apply]
  change _=sourceNativeGaugeCurrentLinear point (actualRestPairPhasePoint part point left right) force
  conv_rhs=>rw [reconstruction]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul,actualRestNativeForcingCovector]


theorem actualRestNativeGaugeQuadrature_complex (part : Fin 2) (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) :
    actualRestNativeGaugeQuadrature part point left right force=
      if part=0 then (sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right) force).re
      else (sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right) force).im := by
  change sourceNativeGaugeCurrentLinear point (actualRestPairPhasePoint part point left right) force=_
  rw [sourceNativeGaugeCurrentLinear_complex]
  have phase : sourceNativeGaugeCurrentComplex point (actualRestPairPhasePoint part point left right) force=
      sourceCurrentPhase part*sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right) force := by
    unfold sourceNativeGaugeCurrentComplex matterGaugeConnectionVariationVector matterGaugeKineticSum
    simp only [sourceGaugeMatterDirection,matterDualFrameRelative_zeroChart,matterDerivativeFrameRelative_zeroChart]
    change (generatedVolumeDensity (actualRestPairPoint point left right):ℂ)*
      (actualRestPairPoint point left right).conjugateMatter
        (Complex.I • ∑ mu : Fin 4,diracMatrixMatterAction
          (inverseCoframeDiracGamma {coframe:=(actualRestPairPoint point left right).coframe,derivative:=0} mu)
          (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm (fieldGauge force mu)))
            (sourceCurrentPhase part • (actualRestPairPoint point left right).matter)))=_
    simp only [map_smul]
    rw [←Finset.smul_sum,map_smul]
    simp only [smul_eq_mul]
    ring
  rw [phase]
  fin_cases part <;> simp [sourceCurrentPhase,Complex.mul_re]

def actualRestNativeComplexForcingCovector (point : BasePoint) (left right : RestStateIndex) : Fin 289→ℂ :=
  fun field=>(actualRestNativeForcingCovector 0 point left right field:ℂ)+
    Complex.I*(actualRestNativeForcingCovector 1 point left right field:ℂ)

theorem actualRestNativeComplexForcingCovector_generated (point : BasePoint) (left right : RestStateIndex)
    (force : Field289) :
    (∑ field : Fin 289,(force field:ℂ)*actualRestNativeComplexForcingCovector point left right field)=
      sourceNativeGaugeCurrentComplex point (actualRestPairPoint point left right) force := by
  have realPart:=actualRestNativeForcingCovector_generated 0 point left right force
  have imagPart:=actualRestNativeForcingCovector_generated 1 point left right force
  rw [actualRestNativeGaugeQuadrature_complex] at realPart imagPart
  simp only [Fin.isValue,if_true,if_false,Fin.reduceEq] at realPart imagPart
  apply Complex.ext
  · simpa [actualRestNativeComplexForcingCovector,Complex.mul_re] using realPart
  · simpa [actualRestNativeComplexForcingCovector,Complex.mul_im] using imagPart

theorem actualRestNativeForcingCovector_temporal (part : Fin 2) (direction : Fin 3) (point : BasePoint)
    (left right : RestStateIndex) :
    (∑ field : Fin 289,sourceTemporalGaugeDirection (sourceColorP286Generator direction) field*
      actualRestNativeForcingCovector part point left right field)=
      if part=0 then ((Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right).re
      else ((Stage10.ActionNormalization.phaseMomentum:ℂ)*sourceRestChargeMixing direction left right).im := by
  rw [actualRestNativeForcingCovector_generated,actualRestTemporalGaugeQuadrature]

theorem actualRestNativeForcingCovector_supported (part : Fin 2) (point : BasePoint) (left right : RestStateIndex)
    (field : Fin 289) (outside : field.val<9 ∨ 57≤field.val) :
    actualRestNativeForcingCovector part point left right field=0 := by
  have gauges (mu : Fin 4) : fieldGauge (Pi.single field 1) mu=0 := by
    unfold fieldGauge
    apply Finset.sum_eq_zero
    intro a _
    have off : field≠gaugeSlot mu a := by
      intro equal
      have value:=congrArg Fin.val equal
      simp only [gaugeSlot,Fin.val_mk] at value
      omega
    simp [off]
  have direction : sourceGaugeMatterDirection (actualRestPairPhasePoint part point left right) (Pi.single field 1)=0 := by
    funext mu
    simp [sourceGaugeMatterDirection,gauges,diracExteriorMotherLieAction,internalMatterLinearAction,
      exteriorSpinorMotherLieAction]
    rfl
  change sourceNativeGaugeCurrentLinear point (actualRestPairPhasePoint part point left right) (Pi.single field 1)=0
  change generatedVolumeDensity _*directionDensity point _ (sourceGaugeMatterDirection _ (Pi.single field 1))=0
  rw [direction]
  simp [directionDensity,matterCovariantDerivativeFirstVariationDensity,matterCovariantDerivativeVariationVector,
    matterCovariantDerivativeKineticSum]

end LowEnergy.PreparationVacuumElectromagneticIdentity
