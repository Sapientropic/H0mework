import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstFullGaugeRemainder

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalFirstPoleGaugeVertex PreparationPhysicalNormalizedFullField
open PreparationVacuumNativeFieldInjection PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumActualFieldQuantization PreparationVacuumOriginalGreenFeedback
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussNativeMatter GaussHistoryHilbert GaussQuantumMultiplier
open StageNineHolonomicField StageNineDynamicBreakingVacuum DiracExteriorMatterAction DiracCliffordRepresentation
open Stage9C.Material.SpinPair FullQuantum.CoframeResponse FullQuantum.StateGreen
open PointwiseLorentzianCoframeJet PointwiseDiracSpinConnectionLift
open Filter Set
open scoped BigOperators Matrix Topology ContDiff Matrix.Norms.L2Operator
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

open PreparationPhysicalFirstGaugeBackgroundReturn PreparationPhysicalSourceHarmonicReturn
open PreparationVacuumPhysicalCharacteristic ProofFreeRicherAnholonomicSource
open CanonicalGradedSpatialSource FullQuantum FullSpace PreparationVacuumLowerClassical

open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativePolarizationEmitter
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumNativeSlowCoupling PreparationVacuumPhysicalFeedback
open PreparationPhysicalResponseChargeGrading PreparationVacuumLorentzFieldInjection
open PreparationVacuumPhysicalChargedFieldFactor PreparationPhysicalPoleChargeMatrix
open GaussFockLift GaussCoreHilbert PreparationVacuumPhysicalQuantumLockedCharge
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalNativePhaseChargeInventory
open scoped InnerProductSpace

private theorem mode_tangent_state (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) :
    configurationState (sourceFirstModeTangent imaginary omega k) x=
      fieldDirection (sourceFirstModeField imaginary omega k x) := by
  change configurationState (configurationFromFields (sourceFirstModeTangent imaginary omega k)
    (fun y=>sourceData (sourceFirstModeField imaginary omega k y))) x=_
  rw [configurationFromFields_state,stateDirection_source]

/-- The gradient is exactly the computed harmonic gauge-parameter derivative. -/
def sourceFirstModeGradient (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum) (x : BasePoint) : ActionState :=
  (0,(fun mu=>sourceFirstGaugeQuadratureDerivative imaginary omega k x mu • nativePrimal sourceFirstTemporalLie),0)

/-- Original all-nine-field remainder, restricted only at the original action consumer. -/
def sourceFirstModeRemainderState (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) : ActionState :=
  configurationState (sourceFirstModeRemainder imaginary omega k c) x

/-- The actual source symbol reads the computed gauge variation and the complete remaining field. -/
theorem sourceFirstModeSymbol_return (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (p : PhysicalMomentum)
    (valid : configurationState c x∈validStates) :
    symbolFirst p (configurationState c x) (fieldDirection (sourceFirstModeField imaginary omega k x))=
      sourceFirstGaugeQuadrature imaginary omega k x •
        sourceFirstBackgroundFullAd (sourceSymbol p (configurationState c x))-
      symbolFirst p (configurationState c x) (sourceFirstModeGradient imaginary omega k x)+
      symbolFirst p (configurationState c x) (sourceFirstModeRemainderState imaginary omega k c x) := by
  have same:=congrArg (fun d=>configurationState d x) (sourceFirstModeRemainder_original imaginary omega k c)
  rw [configurationState_ray,one_smul,sourceFirstModeGauge_state,mode_tangent_state] at same
  rw [←same]
  simp only [symbolFirst,map_add,map_sub,map_smul]
  change _=_
  rw [show (fderiv ℝ (sourceSymbol p) (configurationState c x))
    (sourceFirstGaugeState (configurationState c x))=sourceFirstBackgroundFullAd
      (sourceSymbol p (configurationState c x)) from sourceFirstBackgroundSymbol p _ valid]
  rfl

open Lean Elab Term in
elab "paidFirstActualWeight%" : term => do
  let wanted:=`LowEnergy.PreparationPhysicalFirstPoleGaugeVertex.eight_weight
  let all:=(←getEnv).constants.toList
  let candidates:=all.filter fun (name,_)=>name.toString.startsWith "_private.H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstGaugeRepresentation." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return mkConst name
  | _=>throwError "Expected unique original FirstGaugeRepresentation.eight_weight"

private def firstFullWeight : Mode→ℂ
  | .inl i=>(sourceFirstWholeWeight i:ℂ)*Complex.I
  | .inr i=> -(sourceFirstWholeWeight i:ℂ)*Complex.I

private theorem first_full_diagonal : sourceFirstBackgroundFullGenerator=Matrix.diagonal firstFullWeight := by
  unfold sourceFirstBackgroundFullGenerator
  rw [←sourceFirstTemporal_native,sourceFirstTemporal_matrix]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.fromBlocks,Matrix.diagonal_apply,firstFullWeight]

private theorem first_actual_weight (side edge : Fin 2) :
    firstFullWeight (Sum.inl (sourceChargedQuantumIndex side edge))=(sourceActualPhaseCharge edge:ℂ)*Complex.I := by
  change (sourceFirstWholeWeight (sourceFirstEightIndex (sourceChargedBasisIndex side edge)):ℂ)*Complex.I=_
  rw [paidFirstActualWeight%]
  rfl

/-- Actual normalized Gauss/fullCAR endpoints consume Gt, while its full representation is retained in the inserted operator. -/
theorem sourceFirstBackgroundPrepared_return (epsilon : ℝ) (precision : 0<epsilon)
    (A : FullMatrix) (i j : ActualPreparedIndex) :
    inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
      (lift (quantized (sourceFirstBackgroundFullAd A)) (sourceChargedGaussPrepared epsilon precision j.1 j.2))=
      (((sourceActualPhaseCharge i.2:ℂ)-(sourceActualPhaseCharge j.2:ℂ))*Complex.I)*
        inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
          (lift (quantized A) (sourceChargedGaussPrepared epsilon precision j.1 j.2)) := by
  simp only [sourceChargedEnergyRead_entry,sourceFirstBackgroundFullAd,LinearMap.coe_mk,AddHom.coe_mk,
    first_full_diagonal,Matrix.sub_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,first_actual_weight]
  ring

/-- Each actual real quadrature carries the original gauge gradient and its generated field remainder. -/
def sourceFirstGaugeModeEnergy (omega : ℝ) (k : PhysicalMomentum) (c : StageNineHolonomicConfiguration)
    (x : BasePoint) (p : PhysicalMomentum) : FullMatrix :=
  symbolFirst p (configurationState c x) (configurationState (sourceFirstModeGauge false omega k c) x)+
    Complex.I • symbolFirst p (configurationState c x) (configurationState (sourceFirstModeGauge true omega k c) x)

def sourceFirstRemainderModeEnergy (omega : ℝ) (k : PhysicalMomentum) (c : StageNineHolonomicConfiguration)
    (x : BasePoint) (p : PhysicalMomentum) : FullMatrix :=
  symbolFirst p (configurationState c x) (sourceFirstModeRemainderState false omega k c x)+
    Complex.I • symbolFirst p (configurationState c x) (sourceFirstModeRemainderState true omega k c x)

private theorem energy_real (p : PhysicalMomentum) (s : ActionState) (valid : s∈validStates) (f : Field289) :
    sourceFullEnergyMatrix p s (fun row=>(f row:ℂ))=symbolFirst p s (fieldDirection f) := by
  rw [fieldDirection_coordinates]
  simp only [sourceFullEnergyMatrix]
  simp_rw [sourceNormalizedEnergySymbol_original p s _ valid]
  simp only [symbolFirst,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro row _
  ext a b
  simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul]

private theorem energy_add (p : PhysicalMomentum) (s : ActionState) (A B : Fin 289→ℂ) :
    sourceFullEnergyMatrix p s (A+B)=sourceFullEnergyMatrix p s A+sourceFullEnergyMatrix p s B := by
  simp only [sourceFullEnergyMatrix,Pi.add_apply,add_smul,Finset.sum_add_distrib]

private theorem energy_smul (p : PhysicalMomentum) (s : ActionState) (a : ℂ) (A : Fin 289→ℂ) :
    sourceFullEnergyMatrix p s (a • A)=a • sourceFullEnergyMatrix p s A := by
  simp only [sourceFullEnergyMatrix,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

/-- Original complete FrameJet energy is the two generated real configuration reads, with no field sector suppressed. -/
theorem sourceFirstModeEnergy_return (omega : ℝ) (k : PhysicalMomentum) (c : StageNineHolonomicConfiguration)
    (x : BasePoint) (p : PhysicalMomentum) (valid : configurationState c x∈validStates) :
    sourceFullEnergyMatrix p (configurationState c x)
      (fun row=>sourceFirstHarmonicPhase omega k x*sourceChargedNativeFrameJet (physicalFrequencyMomentum omega k) row 1)=
      sourceFirstGaugeModeEnergy omega k c x p+sourceFirstRemainderModeEnergy omega k c x p := by
  have fields : (fun row=>sourceFirstHarmonicPhase omega k x*sourceChargedNativeFrameJet (physicalFrequencyMomentum omega k) row 1)=
      (fun row=>(sourceFirstModeField false omega k x row:ℂ))+Complex.I •
        (fun row=>(sourceFirstModeField true omega k x row:ℂ)) := by
    funext row
    exact (sourceFirstModeField_complex omega k x row).symm
  rw [fields,energy_add,energy_smul,energy_real p _ valid,energy_real p _ valid]
  have split (imaginary : Bool) : fieldDirection (sourceFirstModeField imaginary omega k x)=
      configurationState (sourceFirstModeGauge imaginary omega k c) x+
        sourceFirstModeRemainderState imaginary omega k c x := by
    have H:=congrArg (fun d=>configurationState d x) (sourceFirstModeRemainder_original imaginary omega k c)
    simpa only [configurationState_ray,one_smul,mode_tangent_state,sourceFirstModeRemainderState] using H.symm
  rw [split false,split true]
  simp only [sourceFirstGaugeModeEnergy,sourceFirstRemainderModeEnergy,symbolFirst,map_add,smul_add]
  abel

/-- Same actual normalized external preparations read both generated terms. -/
def sourceFirstModePreparedRead (epsilon : ℝ) (precision : 0<epsilon) (i j : ActualPreparedIndex)
    (A : FullMatrix) : ℂ :=
  inner ℂ (sourceChargedGaussPrepared epsilon precision i.1 i.2)
    (lift (quantized A) (sourceChargedGaussPrepared epsilon precision j.1 j.2))

/-- The Gt background part returns the actual external charge variation; the physical derivative insertions remain. -/
theorem sourceFirstGaugeModePrepared_return (omega : ℝ) (k : PhysicalMomentum) (c : StageNineHolonomicConfiguration)
    (x : BasePoint) (p : PhysicalMomentum) (valid : configurationState c x∈validStates)
    (epsilon : ℝ) (precision : 0<epsilon) (i j : ActualPreparedIndex) :
    sourceFirstModePreparedRead epsilon precision i j (sourceFirstGaugeModeEnergy omega k c x p)=
      (((sourceFirstGaugeQuadrature false omega k x:ℂ)+Complex.I*(sourceFirstGaugeQuadrature true omega k x:ℂ))*
        (((sourceActualPhaseCharge i.2:ℂ)-(sourceActualPhaseCharge j.2:ℂ))*Complex.I))*
        sourceFirstModePreparedRead epsilon precision i j (sourceSymbol p (configurationState c x))-
      sourceFirstModePreparedRead epsilon precision i j (symbolFirst p (configurationState c x) (sourceFirstModeGradient false omega k x))-
      Complex.I*sourceFirstModePreparedRead epsilon precision i j (symbolFirst p (configurationState c x) (sourceFirstModeGradient true omega k x)) := by
  have gauge (imaginary : Bool) :
      symbolFirst p (configurationState c x) (configurationState (sourceFirstModeGauge imaginary omega k c) x)=
        sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstBackgroundFullAd (sourceSymbol p (configurationState c x))-
          symbolFirst p (configurationState c x) (sourceFirstModeGradient imaginary omega k x) := by
    rw [sourceFirstModeGauge_state]
    simp only [symbolFirst,map_sub,map_smul]
    rw [show (fderiv ℝ (sourceSymbol p) (configurationState c x))
      (sourceFirstGaugeState (configurationState c x))=sourceFirstBackgroundFullAd (sourceSymbol p (configurationState c x))
      from sourceFirstBackgroundSymbol p _ valid]
    rfl
  rw [sourceFirstGaugeModeEnergy,gauge false,gauge true]
  have charge:=sourceFirstBackgroundPrepared_return epsilon precision (sourceSymbol p (configurationState c x)) i j
  simp only [sourceChargedEnergyRead_entry] at charge
  simp only [sourceFirstModePreparedRead,sourceChargedEnergyRead_entry,Matrix.add_apply,
    Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  rw [charge]
  ring

/-- The computed gauge Hessian retains its field-dependent contact and physical gradient contribution. -/
theorem sourceFirstModeGaugeMixed_return (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (p : PhysicalMomentum)
    (valid : configurationState c x∈validStates) (f : Field289) :
    symbolSecond p (configurationState c x) (configurationState (sourceFirstModeGauge imaginary omega k c) x) (fieldDirection f)+
      symbolFirst p (configurationState c x)
        (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstGaugeState (fieldDirection f))=
      sourceFirstGaugeQuadrature imaginary omega k x •
        sourceFirstBackgroundFullAd (symbolFirst p (configurationState c x) (fieldDirection f))-
      symbolSecond p (configurationState c x) (sourceFirstModeGradient imaginary omega k x) (fieldDirection f) := by
  rw [sourceFirstModeGauge_state]
  have original:=sourceFirstBackgroundMixed_return p (configurationState c x) valid f
  unfold sourceFirstBackgroundMixed at original
  rw [←original]
  simp only [symbolSecond,symbolFirst,map_sub,map_smul,smul_add,sourceFirstModeGradient]
  abel

/-- The compensating remainder contact is retained when the original fixed field Hessian is reconstructed. -/
theorem sourceFirstModeMixed_return (imaginary : Bool) (omega : ℝ) (k : PhysicalMomentum)
    (c : StageNineHolonomicConfiguration) (x : BasePoint) (p : PhysicalMomentum) (f : Field289) :
    symbolSecond p (configurationState c x) (fieldDirection (sourceFirstModeField imaginary omega k x)) (fieldDirection f)=
      (symbolSecond p (configurationState c x) (configurationState (sourceFirstModeGauge imaginary omega k c) x) (fieldDirection f)+
        symbolFirst p (configurationState c x)
          (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstGaugeState (fieldDirection f)))+
      (symbolSecond p (configurationState c x) (sourceFirstModeRemainderState imaginary omega k c x) (fieldDirection f)-
        symbolFirst p (configurationState c x)
          (sourceFirstGaugeQuadrature imaginary omega k x • sourceFirstGaugeState (fieldDirection f))) := by
  have same:=congrArg (fun d=>configurationState d x) (sourceFirstModeRemainder_original imaginary omega k c)
  rw [configurationState_ray,one_smul,mode_tangent_state] at same
  rw [←same]
  simp only [symbolSecond,map_add,sourceFirstModeRemainderState]
  abel

private theorem first_mode_read_add (epsilon : ℝ) (precision : 0<epsilon) (i j : ActualPreparedIndex) (A B : FullMatrix) :
    sourceFirstModePreparedRead epsilon precision i j (A+B)=
      sourceFirstModePreparedRead epsilon precision i j A+sourceFirstModePreparedRead epsilon precision i j B := by
  simp only [sourceFirstModePreparedRead,sourceChargedEnergyRead_entry,Matrix.add_apply]

private theorem original_first_read (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum)
    (omega : ℝ) (k : PhysicalMomentum) (i j : ActualPreparedIndex) :
    sourceFirstModePreparedRead epsilon precision i j
        (sourceFirstGaugeModeEnergy omega k (emitter sourcePoint.val) 0 p)+
      sourceFirstModePreparedRead epsilon precision i j
        (sourceFirstRemainderModeEnergy omega k (emitter sourcePoint.val) 0 p)=
      Matrix.diagonal (sourceFirstPreparedCoefficient (physicalFrequencyMomentum omega k)) i j := by
  rw [←first_mode_read_add]
  have valid : configurationState (emitter sourcePoint.val) 0∈validStates :=
    PreparationVacuumNonlinearFieldCurve.sourceState_valid sourcePoint
  have full:=sourceFirstModeEnergy_return omega k (emitter sourcePoint.val) 0 p valid
  have phaseZero : sourceFirstHarmonicPhase omega k 0=1 := by
    simp only [sourceFirstHarmonicPhase,map_zero,Complex.exp_zero]
  rw [phaseZero] at full
  simp only [one_mul,configurationState_emitter] at full
  have column : (⟨(1:Fin 3).val,by decide⟩:Fin 289)=(1:Fin 289) := by decide
  have literal:=sourceLiteralEnergyWeight_generated p (sourceState sourcePoint.val) (physicalFrequencyMomentum omega k) 1
  rw [column] at literal
  rw [←literal] at full
  rw [←full]
  have original:=congrArg (fun M : Matrix ActualPreparedIndex ActualPreparedIndex ℂ=>M i j)
    (sourceFirstEnergyFour_value epsilon precision p (physicalFrequencyMomentum omega k))
  exact original

open PreparationPhysicalPhaseGaugeRealization PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalFinitePoleCurvatureReturn PreparationPhysicalCurvatureSheetLimit
open PreparationVacuumSoftPoleSelection PreparationVacuumPhysicalPoleSheet
open PreparationVacuumQuantumSlowResidue PreparationPhysicalActualGaussChargeCurrent

/-- The actual moving current-emitted first pole directly reads the generated gauge/external and complete remainder terms, with the origin still subtracted explicitly. -/
theorem sourceFirstPoleCurrent_remainder (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (pL pR : PhysicalMomentum) (lambda : ℂ) (T : ℝ) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (epsilon : ℝ) (precision : 0<epsilon) (p : PhysicalMomentum) (i j : ActualPreparedIndex) :
    Tendsto (fun e : scaleDomain=>(2*(sourceSheet 0 n unit e.val:ℂ))*
      (sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePhaseGaugePhotonField q sL eL sR eR pL pR lambda T e.val (sourceSheet 0 n unit e.val) n)-
       sourcePhotonLeftReader 0 e.val (sourceSheet 0 n unit e.val) n
         (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T)*
       sourceFullEnergyRead epsilon precision p (sourceState sourcePoint.val) i.1 i.2 j.1 j.2
        (sourcePoleOriginField 0 e.val (sourceSheet 0 n unit e.val) n)))
      scaleApproach (𝓝 (sourceCurvatureEmitterInput
        (sourceActualPreparedCurrent q pL pR sL eL sR eR lambda T) (residueIndex 0)*
        ((softCoefficient 0:ℂ)*
          (sourceFirstModePreparedRead epsilon precision i j
              (sourceFirstGaugeModeEnergy (sourceSpeed 0) n (emitter sourcePoint.val) 0 p)+
            sourceFirstModePreparedRead epsilon precision i j
              (sourceFirstRemainderModeEnergy (sourceSpeed 0) n (emitter sourcePoint.val) 0 p))))) := by
  rw [original_first_read]
  exact sourceFirstPoleCurrent_energy q sL eL sR eR pL pR lambda T n unit epsilon precision p i j

end LowEnergy.PreparationPhysicalFirstPoleGaugeRemainder
