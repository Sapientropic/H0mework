import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstFourPointTransfer

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
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

open PreparationPhysicalFirstPoleGaugeRemainder PreparationPhysicalMaterialChargeTorque
open PreparationPhysicalActualGaussChargeCurrent PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalCoframeChargeSelection PreparationPhysicalCoframeChargeExchange
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualGaugeSlice CanonicalGradedCharge GaussCoreDifferential GaussQuantumMultiplier
open GaussFockPair GaussLiveMomentum GaussNativePotential
open scoped ContDiff

open NativeHistoryGrade GaussUnitaryHistory CanonicalPhysicalSpatial CanonicalPhysicalWardCore
open PreparationVacuumGradedTransport PreparationVacuumUncutYukawa PreparationPhysicalActualLegNormalization
open PreparationVacuumPhysicalHalfAxis PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumPhysicalPoleAmputation PreparationPhysicalChargedScatteringPoleReturn
open GaussFockWeights GaussDensityCore MeasureTheory PreparationVacuumFieldConstraintResponse PreparationVacuumYukawaTransport
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent actualC gradedTest

open PreparationPhysicalFirstGaugeMaterialDifference PreparationPhysicalActualUnitFourPointReturn
open PreparationPhysicalActualPolarizationResponse PreparationVacuumFullFieldRiesz

attribute [local irreducible] jointCurrent jointHessian sourceUnitRead sourceActualUnitLegRead

open scoped Interval

/-- Both ordered charge insertions and the independent Hessian are read on the original unit legs. -/
def sourceFirstUnitFourPointInsertion (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) : ℂ :=
  sourceUnitRead q sL eL sR eR (sourceFirstFourPointInsertion q f g)

/-- Actual internal Green legs carry current-created states; the computed material read is evaluated at those states. -/
theorem sourceFirstUnitGreenInsertion_read (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (z : ℂ) (A B : H→L[ℂ]H) :
    sourceUnitRead q sL eL sR eR (A*sourceFirstGreenInsertion q z*B)=
      sourceActualLegNormalization q sL eL sR eR*
        (sourceFirstMaterialChargeRead q.F
          ((jointResolvent 0 q.F z 0).adjoint (A.adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL)))
          (jointResolvent 0 q.F z 0 (B (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))+
          sourceActualLegCorrection q sL eL sR eR (A*sourceFirstGreenInsertion q z*B)) := by
  rw [sourceUnitRead_original,sourceActualUnitLegRead_return]
  have generated:=sourceFirstGreenInsertion_read q z
    (A.adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL))
    (B (sourceChargedGaussPrepared q.epsilon q.precision sR eR))
  have read : sourceQuantumChargedRead q sL eL sR eR (A*sourceFirstGreenInsertion q z*B)=
      sourceFirstMaterialChargeRead q.F
        ((jointResolvent 0 q.F z 0).adjoint (A.adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL)))
        (jointResolvent 0 q.F z 0 (B (sourceChargedGaussPrepared q.epsilon q.precision sR eR))) := by
    change inner ℂ (sourceChargedGaussPrepared q.epsilon q.precision sL eL)
      (A (sourceFirstGreenInsertion q z (B (sourceChargedGaussPrepared q.epsilon q.precision sR eR))))=_
    rw [←ContinuousLinearMap.adjoint_inner_left]
    exact generated
  exact congrArg (fun v : ℂ=>sourceActualLegNormalization q sL eL sR eR*
    (v+sourceActualLegCorrection q sL eL sR eR (A*sourceFirstGreenInsertion q z*B))) read

/-- The computed current, mixed and both material Green insertions are consumed by the actual two-order core. -/
theorem sourceFirstUnitFourPointInsertion_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceUnitRead q sL eL sR eR
      (sourceFourPointCore q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointCore q f g)=
      sourceFirstUnitFourPointInsertion q sL eL sR eR f g := by
  rw [sourceFirstFourPointInsertion_generated q f g left right]
  rfl

/-- Explicit evaluated material transfer in each ordering, with its own full independent-leg correction. -/
theorem sourceFirstUnitFourPointInsertion_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) :
    sourceFirstUnitFourPointInsertion q sL eL sR eR f g=
      sourceUnitRead q sL eL sR eR
        (sourceFirstCurrentInsertion f 0 q.F*jointResolvent 0 q.F q.z 0*jointCurrent 0 q.F q.w 0 g)-
      sourceActualLegNormalization q sL eL sR eR*
        (sourceFirstMaterialChargeRead q.F
          ((jointResolvent 0 q.F q.z 0).adjoint ((jointCurrent 0 q.F q.z 0 f).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL)))
          (jointResolvent 0 q.F q.z 0 (jointCurrent 0 q.F q.w 0 g (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))+
          sourceActualLegCorrection q sL eL sR eR
            (jointCurrent 0 q.F q.z 0 f*sourceFirstGreenInsertion q q.z*jointCurrent 0 q.F q.w 0 g))+
      sourceUnitRead q sL eL sR eR
        (jointCurrent 0 q.F q.z 0 f*jointResolvent 0 q.F q.z 0*sourceFirstCurrentInsertion g 0 q.F)+
      sourceUnitRead q sL eL sR eR
        (sourceFirstCurrentInsertion g 0 q.F*jointResolvent 0 q.F q.w 0*jointCurrent 0 q.F q.w 0 f)-
      sourceActualLegNormalization q sL eL sR eR*
        (sourceFirstMaterialChargeRead q.F
          ((jointResolvent 0 q.F q.w 0).adjoint ((jointCurrent 0 q.F q.w 0 g).adjoint (sourceChargedGaussPrepared q.epsilon q.precision sL eL)))
          (jointResolvent 0 q.F q.w 0 (jointCurrent 0 q.F q.w 0 f (sourceChargedGaussPrepared q.epsilon q.precision sR eR)))+
          sourceActualLegCorrection q sL eL sR eR
            (jointCurrent 0 q.F q.w 0 g*sourceFirstGreenInsertion q q.w*jointCurrent 0 q.F q.w 0 f))+
      sourceUnitRead q sL eL sR eR
        (jointCurrent 0 q.F q.w 0 g*jointResolvent 0 q.F q.w 0*sourceFirstCurrentInsertion f 0 q.F)-
      sourceUnitRead q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F) := by
  simp only [sourceFirstUnitFourPointInsertion,sourceFirstFourPointInsertion,map_add,map_sub]
  exact congrArg₂ (fun x y : ℂ=>
    sourceUnitRead q sL eL sR eR
      (sourceFirstCurrentInsertion f 0 q.F*jointResolvent 0 q.F q.z 0*jointCurrent 0 q.F q.w 0 g)-x+
    sourceUnitRead q sL eL sR eR
      (jointCurrent 0 q.F q.z 0 f*jointResolvent 0 q.F q.z 0*sourceFirstCurrentInsertion g 0 q.F)+
    sourceUnitRead q sL eL sR eR
      (sourceFirstCurrentInsertion g 0 q.F*jointResolvent 0 q.F q.w 0*jointCurrent 0 q.F q.w 0 f)-y+
    sourceUnitRead q sL eL sR eR
      (jointCurrent 0 q.F q.w 0 g*jointResolvent 0 q.F q.w 0*sourceFirstCurrentInsertion f 0 q.F)-
    sourceUnitRead q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F))
    (sourceFirstUnitGreenInsertion_read q sL eL sR eR q.z
      (jointCurrent 0 q.F q.z 0 f) (jointCurrent 0 q.F q.w 0 g))
    (sourceFirstUnitGreenInsertion_read q sL eL sR eR q.w
      (jointCurrent 0 q.F q.w 0 g) (jointCurrent 0 q.F q.w 0 f))

open Lean Elab Term in
elab "paidFirstChargeEnds%" : term => do
  let wanted:=`LowEnergy.PreparationPhysicalFirstGaugeMaterialDifference.first_charge_ends
  let candidates:=(←getEnv).constants.toList.filter fun (name,_)=>
    name.toString.startsWith "_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFirstMaterialVertexReturn." && privateToUserName name==wanted
  match candidates with
  | [(name,_)]=>logInfo m!"Original private payer: {name}";return ←Lean.Meta.mkConstWithFreshMVarLevels name
  | _=>throwError "Expected unique original D65 first_charge_ends"

private theorem bare_charge_read (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (A : H→L[ℂ]H) :
    sourceQuantumChargedRead q sL eL sR eR (A*sourceFirstCharge-sourceFirstCharge*A)=
      ((sourceActualPhaseCharge eR:ℂ)-(sourceActualPhaseCharge eL:ℂ))*sourceQuantumChargedRead q sL eL sR eR A := by
  have ends:=(paidFirstChargeEnds%) q sL eL sR eR A
  rw [map_sub,ends.1,ends.2]
  ring

private theorem pair_total (n a b c d e f : ℂ) :
    (n*(a+d+b+e),-n*(c+f)).1+(n*(a+d+b+e),-n*(c+f)).2=
      n*((a+b-c)+(d+e-f)) := by ring

private theorem charge_balance (n delta value correction transfer : ℂ) :
    n*(delta*value+transfer)=delta*(n*(value+correction))+n*(transfer-delta*correction) := by ring

/-- The original full four-point response itself is the charge-transfer consumer; its two orders and independent contact retain every normalization correction. -/
theorem sourceFirstUnitFourPointResponse_transfer (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (f g : Field289) (left : q.z.im≠0) (right : q.w.im≠0) :
    sourceFirstUnitFourPointInsertion q sL eL sR eR f g=
      ((sourceActualPhaseCharge eR:ℂ)-(sourceActualPhaseCharge eL:ℂ))*
        ((sourceUnitFourPointPair q sL eL sR eR f g).1+(sourceUnitFourPointPair q sL eL sR eR f g).2)+
      sourceActualLegNormalization q sL eL sR eR*
        (sourceActualLegCorrection q sL eL sR eR
          (sourceFourPointCore q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointCore q f g)-
          ((sourceActualPhaseCharge eR:ℂ)-(sourceActualPhaseCharge eL:ℂ))*
          sourceActualLegCorrection q sL eL sR eR (sourceFourPointCore q f g)) := by
  have raw : sourceQuantumChargedRead q sL eL sR eR (sourceFourPointCore q f g)=
      sourceQuantumChargedRead q sL eL sR eR (sourceFourPointForward q f g)+
      sourceQuantumChargedRead q sL eL sR eR (sourceFourPointReverse q f g)-
      sourceQuantumChargedRead q sL eL sR eR (sourceFourPointContact q f g) := by
    simp only [sourceFourPointCore,map_sub,map_add]
  have correction : sourceActualLegCorrection q sL eL sR eR (sourceFourPointCore q f g)=
      sourceActualLegCorrection q sL eL sR eR (sourceFourPointForward q f g)+
      sourceActualLegCorrection q sL eL sR eR (sourceFourPointReverse q f g)-
      sourceActualLegCorrection q sL eL sR eR (sourceFourPointContact q f g) := by
    simp only [sourceFourPointCore,sourceActualLegCorrection,add_apply,sub_apply,map_add,map_sub]
    ring
  let K:=sourceFourPointCore q f g
  let D:=K*sourceFirstCharge-sourceFirstCharge*K
  let n:=sourceActualLegNormalization q sL eL sR eR
  let delta:=(sourceActualPhaseCharge eR:ℂ)-(sourceActualPhaseCharge eL:ℂ)
  have insertion : sourceFirstUnitFourPointInsertion q sL eL sR eR f g=
      n*(delta*sourceQuantumChargedRead q sL eL sR eR K+sourceActualLegCorrection q sL eL sR eR D) :=
    (sourceFirstUnitFourPointInsertion_generated q sL eL sR eR f g left right).symm.trans
      ((sourceUnitRead_original q sL eL sR eR D).trans
        ((sourceActualUnitLegRead_return q sL eL sR eR D).trans
          (congrArg (fun v : ℂ=>n*(v+sourceActualLegCorrection q sL eL sR eR D))
            (bare_charge_read q sL eL sR eR K))))
  have total:=(congrArg (fun v : ℂ × ℂ =>v.1+v.2) (sourceUnitFourPoint_return q sL eL sR eR f g)).trans
    (pair_total n
      (sourceQuantumChargedRead q sL eL sR eR (sourceFourPointForward q f g))
      (sourceQuantumChargedRead q sL eL sR eR (sourceFourPointReverse q f g))
      (sourceQuantumChargedRead q sL eL sR eR (sourceFourPointContact q f g))
      (sourceActualLegCorrection q sL eL sR eR (sourceFourPointForward q f g))
      (sourceActualLegCorrection q sL eL sR eR (sourceFourPointReverse q f g))
      (sourceActualLegCorrection q sL eL sR eR (sourceFourPointContact q f g)))
  have collapsed:=total.trans (congrArg₂ (fun a b : ℂ=>n*(a+b)) raw.symm correction.symm)
  exact insertion.trans ((charge_balance n delta (sourceQuantumChargedRead q sL eL sR eR K)
    (sourceActualLegCorrection q sL eL sR eR K) (sourceActualLegCorrection q sL eL sR eR D)).trans
      (congrArg (fun v : ℂ=>delta*v+n*(sourceActualLegCorrection q sL eL sR eR D-
        delta*sourceActualLegCorrection q sL eL sR eR K)) collapsed.symm))

/-- The contact channel is not lost when the ordered transfer is assembled. -/
theorem sourceFirstUnitContact_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (f g : Field289) :
    -sourceUnitRead q sL eL sR eR
      (sourceFourPointContact q f g*sourceFirstCharge-sourceFirstCharge*sourceFourPointContact q f g)=
      -sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F)+
          sourceActualLegCorrection q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F)) := by
  have mixed:=sourceFirstMixedInsertion_generated f g 0 q.F q.w
  have read:=(sourceUnitRead_original q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F)).trans
    (sourceActualUnitLegRead_return q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F))
  exact (congrArg (fun A : H→L[ℂ]H=>-sourceUnitRead q sL eL sR eR A) mixed).trans
    ((congrArg (fun a : ℂ=>-a) read).trans
      (_root_.neg_mul (sourceActualLegNormalization q sL eL sR eR)
        (sourceQuantumChargedRead q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F)+
          sourceActualLegCorrection q sL eL sR eR (sourceFirstMixedInsertion f g 0 q.F))).symm)

private theorem time_continuous (C : H→L[ℂ]H) : Continuous (SourceFiniteUnitary.time C) :=
  continuous_iff_continuousAt.mpr (fun t=>(hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

private theorem time_derivative (C : H→L[ℂ]H) (t : ℝ) :
    HasDerivAt (SourceFiniteUnitary.time C) (SourceFiniteUnitary.time C t*((-Complex.I) • C)) t :=
  hasDerivAt_exp_smul_const ((-Complex.I) • C) t

/-- The original physical clock has a generated finite-time charge insertion; no material commutation or selfadjointness premise is imposed. -/
def sourceFirstTimeInsertion (q : PhysicalResponsePoint) (t : ℝ) : H→L[ℂ]H :=
  ∫s in (0:ℝ)..t,physicalTime 0 q.F s 0*
    ((-Complex.I) • (jointGenerator 0 q.F 0 0*sourceFirstCharge-sourceFirstCharge*jointGenerator 0 q.F 0 0))*
      physicalTime 0 q.F (t-s) 0

private theorem time_charge (C Q : H→L[ℂ]H) (t : ℝ) :
    SourceFiniteUnitary.time C t*Q-Q*SourceFiniteUnitary.time C t=
      ∫s in (0:ℝ)..t,SourceFiniteUnitary.time C s*((-Complex.I) • (C*Q-Q*C))*SourceFiniteUnitary.time C (t-s) := by
  let f:=fun s : ℝ=>SourceFiniteUnitary.time C s*Q*SourceFiniteUnitary.time C (t-s)
  let df:=fun s : ℝ=>SourceFiniteUnitary.time C s*((-Complex.I) • (C*Q-Q*C))*SourceFiniteUnitary.time C (t-s)
  have derivative (s : ℝ) : HasDerivAt f (df s) s := by
    have right:=(time_derivative C (t-s)).scomp s ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    have generated:=((time_derivative C s).mul_const Q).mul right
    have commute:=((SourceFiniteUnitary.time_commutes C C (Commute.refl C) (t-s)).smul_left (-Complex.I)).eq
    convert generated using 1
    all_goals
      first
      | rfl
      | simp only [df,Function.comp_apply,zero_sub,neg_one_smul,mul_neg]
        rw [←commute]
        simp only [smul_sub,mul_sub,sub_mul,mul_assoc,smul_mul_assoc,mul_smul_comm]
        abel
  have integrable : IntervalIntegrable df volume 0 t :=
    (((time_continuous C).mul continuous_const).mul
      ((time_continuous C).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _=>derivative s) integrable
  simpa only [f,df,sub_zero,sub_self,SourceFiniteUnitary.time_zero,mul_one,one_mul] using generated.symm

theorem sourceFirstTimeInsertion_generated (q : PhysicalResponsePoint) (t : ℝ) :
    physicalTime 0 q.F t 0*sourceFirstCharge-sourceFirstCharge*physicalTime 0 q.F t 0=
      sourceFirstTimeInsertion q t :=
  time_charge (jointGenerator 0 q.F 0 0) sourceFirstCharge t

/-- The integrand is evaluated on the actual transported Hilbert states, preserving all M57 and D65 terms. -/
theorem sourceFirstTimeInsertion_integrand (q : PhysicalResponsePoint) (t s : ℝ) (x y : H) :
    inner ℂ x ((physicalTime 0 q.F s 0*
      ((-Complex.I) • (jointGenerator 0 q.F 0 0*sourceFirstCharge-sourceFirstCharge*jointGenerator 0 q.F 0 0))*
      physicalTime 0 q.F (t-s) 0) y)=
      (-Complex.I)*sourceFirstMaterialChargeRead q.F
        ((physicalTime 0 q.F s 0).adjoint x) (physicalTime 0 q.F (t-s) 0 y) := by
  simp only [mul_apply_eq_comp]
  rw [←ContinuousLinearMap.adjoint_inner_left,smul_apply,inner_smul_right,sourceFirstMaterialCharge_return]

private def chargeMap : (H→L[ℂ]H)→L[ℂ](H→L[ℂ]H) :=
  (ContinuousLinearMap.mul ℂ (H→L[ℂ]H)).flip sourceFirstCharge-
    ContinuousLinearMap.mul ℂ (H→L[ℂ]H) sourceFirstCharge

private theorem product_charge {R : Type*} [Ring R] (A B C Q : R) :
    (A*B*C)*Q-Q*(A*B*C)=
      (A*Q-Q*A)*B*C+A*(B*Q-Q*B)*C+A*B*(C*Q-Q*C) := by noncomm_ring

private theorem scalar_charge (c : ℂ) (A : H→L[ℂ]H) :
    (c • A)*sourceFirstCharge-sourceFirstCharge*(c • A)=c • (A*sourceFirstCharge-sourceFirstCharge*A) := by
  rw [smul_mul_assoc c A sourceFirstCharge,mul_smul_comm c sourceFirstCharge A]
  exact (smul_sub c _ _).symm

/-- The actual field variation of the same clock carries two transported material insertions and the original full current insertion. -/
def sourceFirstTimeSlopeInsertion (q : PhysicalResponsePoint) (f : Field289) (t : ℝ) : H→L[ℂ]H :=
  ∫s in (0:ℝ)..t,
    sourceFirstTimeInsertion q s*((-Complex.I) • jointCurrent 0 q.F 0 0 f)*physicalTime 0 q.F (t-s) 0+
    physicalTime 0 q.F s 0*((-Complex.I) • sourceFirstCurrentInsertion f 0 q.F)*physicalTime 0 q.F (t-s) 0+
    physicalTime 0 q.F s 0*((-Complex.I) • jointCurrent 0 q.F 0 0 f)*sourceFirstTimeInsertion q (t-s)

theorem sourceFirstTimeSlopeInsertion_generated (q : PhysicalResponsePoint) (f : Field289) (t : ℝ) :
    timeSlope f 0 q.F t*sourceFirstCharge-sourceFirstCharge*timeSlope f 0 q.F t=
      sourceFirstTimeSlopeInsertion q f t := by
  let integrand:=fun s : ℝ=>physicalTime 0 q.F s 0*((-Complex.I) • jointCurrent 0 q.F 0 0 f)*physicalTime 0 q.F (t-s) 0
  have integrable : IntervalIntegrable integrand volume 0 t :=
    (((time_continuous (jointGenerator 0 q.F 0 0)).mul continuous_const).mul
      ((time_continuous (jointGenerator 0 q.F 0 0)).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  have original : timeSlope f 0 q.F t=∫s in (0:ℝ)..t,integrand s := by
    simp only [timeSlope,CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,
      zero_smul,add_zero,integrand,physicalTime]
  change chargeMap (timeSlope f 0 q.F t)=_
  rw [original,←chargeMap.intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro s _
  change (integrand s)*sourceFirstCharge-sourceFirstCharge*(integrand s)=_
  simp only [integrand,product_charge,scalar_charge,sourceFirstTimeInsertion_generated,
    sourceFirstCurrentInsertion_generated]

/-- The leading minus is the original derivative of the inverse, with all three actual charge insertions retained. -/
def sourceFirstGreenSlopeInsertion (q : PhysicalResponsePoint) (z : ℂ) (f : Field289) : H→L[ℂ]H :=
  -((-sourceFirstGreenInsertion q z)*jointCurrent 0 q.F z 0 f*jointResolvent 0 q.F z 0+
    jointResolvent 0 q.F z 0*sourceFirstCurrentInsertion f 0 q.F*jointResolvent 0 q.F z 0+
    jointResolvent 0 q.F z 0*jointCurrent 0 q.F z 0 f*(-sourceFirstGreenInsertion q z))

private theorem negative_charge {R : Type*} [Ring R] (A Q : R) :
    (-A)*Q-Q*(-A)= -(A*Q-Q*A) := by noncomm_ring

theorem sourceFirstGreenSlopeInsertion_generated (q : PhysicalResponsePoint) (z : ℂ)
    (nonreal : z.im≠0) (f : Field289) :
    (-(jointResolvent 0 q.F z 0*jointCurrent 0 q.F z 0 f*jointResolvent 0 q.F z 0))*sourceFirstCharge-
      sourceFirstCharge*(-(jointResolvent 0 q.F z 0*jointCurrent 0 q.F z 0 f*jointResolvent 0 q.F z 0))=
      sourceFirstGreenSlopeInsertion q z f := by
  have generated:=product_charge (jointResolvent 0 q.F z 0) (jointCurrent 0 q.F z 0 f)
    (jointResolvent 0 q.F z 0) sourceFirstCharge
  have slots:=congrArg₂ (fun dG dJ : H→L[ℂ]H=>
    dG*jointCurrent 0 q.F z 0 f*jointResolvent 0 q.F z 0+
    jointResolvent 0 q.F z 0*dJ*jointResolvent 0 q.F z 0+
    jointResolvent 0 q.F z 0*jointCurrent 0 q.F z 0 f*dG)
    (sourceFirstGreenInsertion_generated q z nonreal) (sourceFirstCurrentInsertion_generated f 0 q.F z)
  exact (negative_charge _ sourceFirstCharge).trans
    (congrArg (fun A : H→L[ℂ]H=>-A) (generated.trans slots))

private def wordInsertion {R : Type*} [Ring R] (A B C D E a b c d e : R) : R :=
  a*B*C*D*E+A*b*C*D*E+A*B*c*D*E+A*B*C*d*E+A*B*C*D*e

private theorem word_charge {R : Type*} [Ring R] (A B C D E Q : R) :
    (A*B*C*D*E)*Q-Q*(A*B*C*D*E)=
      wordInsertion A B C D E
        (A*Q-Q*A) (B*Q-Q*B) (C*Q-Q*C) (D*Q-Q*D) (E*Q-Q*E) := by
  unfold wordInsertion
  noncomm_ring

private theorem collect_four {R : Type*} [Ring R] (A B C D Q : R) :
    (A+B+C+D)*Q-Q*(A+B+C+D)=(A*Q-Q*A)+(B*Q-Q*B)+(C*Q-Q*C)+(D*Q-Q*D) := by noncomm_ring

/-- All four surviving first-axis words are explicit; the original fifth (direct raw contact) has its source-proved zero only for these two fields. -/
def sourceFirstFiveInsertion (q : PhysicalResponsePoint) (k l : Fin 4) (age : ℝ) : H→L[ℂ]H :=
  let f:=sourceEnergyAxisField 1 l
  let reader:=sourceEnergyAxisField 1 k
  let L:=physicalTime 0 q.F (-age) 0
  let R:=physicalTime 0 q.F age 0
  let G:=jointResolvent 0 q.F q.z 0
  let H:=jointResolvent 0 q.F q.w 0
  let B:=PreparationVacuumRawJointFeedback.rawReader reader 0 q.F 0
  let dL:=sourceFirstTimeInsertion q (-age)
  let dR:=sourceFirstTimeInsertion q age
  let dG:= -sourceFirstGreenInsertion q q.z
  let dH:= -sourceFirstGreenInsertion q q.w
  let dB:=sourceFirstRawReaderInsertion reader 0 q.F
  wordInsertion (timeSlope f 0 q.F (-age)) G B H R
    (sourceFirstTimeSlopeInsertion q f (-age)) dG dB dH dR+
  wordInsertion L (-(G*jointCurrent 0 q.F q.z 0 f*G)) B H R
    dL (sourceFirstGreenSlopeInsertion q q.z f) dB dH dR+
  wordInsertion L G B (-(H*jointCurrent 0 q.F q.w 0 f*H)) R
    dL dG dB (sourceFirstGreenSlopeInsertion q q.w f) dR+
  wordInsertion L G B H (timeSlope f 0 q.F age)
    dL dG dB dH (sourceFirstTimeSlopeInsertion q f age)

theorem sourceFirstFiveInsertion_generated (q : PhysicalResponsePoint) (k l : Fin 4) (age : ℝ)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    fiveDerivative (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) 0 0 q.F q.z q.w age*sourceFirstCharge-
      sourceFirstCharge*fiveDerivative (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) 0 0 q.F q.z q.w age=
      sourceFirstFiveInsertion q k l age := by
  simp only [fiveDerivative,sourcePolarizationAxis_readerContact,mul_zero,zero_mul,add_zero,
    sourceFirstFiveInsertion]
  rw [collect_four]
  simp only [word_charge,sourceFirstTimeInsertion_generated,sourceFirstTimeSlopeInsertion_generated,
    sourceFirstGreenInsertion_generated q q.z left,sourceFirstGreenInsertion_generated q q.w right,
    sourceFirstGreenSlopeInsertion_generated q q.z left,sourceFirstGreenSlopeInsertion_generated q q.w right,
    sourceFirstRawReaderInsertion]

/-- The charge derivative of the original full five-term current uses the same actual unit read, at the paid 0/0 momentum restriction. -/
def sourceFirstUnitFiveInsertion (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2) (k l : Fin 4) (age : ℝ) : ℂ :=
  -sourceUnitRead q sL eL sR eR (sourceFirstFiveInsertion q k l age)

theorem sourceFirstUnitFiveInsertion_generated (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (k l : Fin 4) (age : ℝ) (left : q.z.im≠0) (right : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=> -sourceUnitRead q sL eL sR eR
      (fiveKernel (sourceEnergyAxisField 1 k) 0 0 q.F q.z q.w age (r • sourceEnergyAxisField 1 l)*sourceFirstCharge-
        sourceFirstCharge*fiveKernel (sourceEnergyAxisField 1 k) 0 0 q.F q.z q.w age (r • sourceEnergyAxisField 1 l)))
      (sourceFirstUnitFiveInsertion q sL eL sR eR k l age) 0 := by
  have first:=fiveKernel_generated (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) 0 0 q.F q.z q.w left right age
  have charge:=(first.mul_const sourceFirstCharge).sub (first.const_mul sourceFirstCharge)
  have read:=((sourceUnitRead q sL eL sR eR).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 charge |>.neg
  have generated:=sourceFirstFiveInsertion_generated q k l age left right
  have result:=read.congr_deriv (show
      -sourceUnitRead q sL eL sR eR
        (fiveDerivative (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) 0 0 q.F q.z q.w age*sourceFirstCharge-
          sourceFirstCharge*fiveDerivative (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) 0 0 q.F q.z q.w age)=
        sourceFirstUnitFiveInsertion q sL eL sR eR k l age from
    congrArg (fun A : H→L[ℂ]H=>-sourceUnitRead q sL eL sR eR A) generated)
  convert result using 1 <;> rfl

/-- Every full independent-dual/primal correction remains in the final charged five-term response. -/
theorem sourceFirstUnitFiveInsertion_return (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (k l : Fin 4) (age : ℝ) :
    sourceFirstUnitFiveInsertion q sL eL sR eR k l age=
      -sourceActualLegNormalization q sL eL sR eR*
        (sourceQuantumChargedRead q sL eL sR eR (sourceFirstFiveInsertion q k l age)+
          sourceActualLegCorrection q sL eL sR eR (sourceFirstFiveInsertion q k l age)) := by
  rw [sourceFirstUnitFiveInsertion,sourceUnitRead_original,sourceActualUnitLegRead_return,neg_mul]

private theorem charge_norm (A : H→L[ℂ]H) :
    ‖A*sourceFirstCharge-sourceFirstCharge*A‖≤(2*‖sourceFirstCharge‖)*‖A‖ := by
  calc
    _≤‖A*sourceFirstCharge‖+‖sourceFirstCharge*A‖:=norm_sub_le _ _
    _≤‖A‖*‖sourceFirstCharge‖+‖sourceFirstCharge‖*‖A‖:=add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _=_:=by ring

/-- The original fixed-window price survives the computed charge insertion; no uniform low-frequency interchange is assumed. -/
theorem sourceFirstUnitFiveInsertion_bound (q : PhysicalResponsePoint) (sL eL sR eR : Fin 2)
    (k l : Fin 4) (eta age : ℝ) (positive : 0<eta) (future : 0≤age)
    (left : q.z.im≠0) (right : q.w.im≠0) :
    ‖sourceFirstUnitFiveInsertion q sL eL sR eR k l age‖≤
      (2*‖sourceFirstCharge‖)*
        (PreparationVacuumPhysicalTailPrice.fiveCoefficient {q with p:=0,k:=0}
          (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) eta*Real.exp (4*eta*age)) := by
  rw [sourceFirstUnitFiveInsertion,norm_neg,sourceUnitRead_original,
    ←sourceFirstFiveInsertion_generated q k l age left right]
  exact (sourceActualUnitLegRead_bound q sL eL sR eR left right _).trans
    ((charge_norm _).trans (mul_le_mul_of_nonneg_left
      (PreparationVacuumPhysicalTailPrice.fiveKernel_price {q with p:=0,k:=0}
        (sourceEnergyAxisField 1 k) (sourceEnergyAxisField 1 l) eta age positive future)
      (mul_nonneg (by norm_num) (norm_nonneg _))))

end LowEnergy.PreparationPhysicalFirstChargeFourPointReturn
