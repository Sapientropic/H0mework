import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceFixedMomentumHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumFixedMomentumActionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussQuantumMultiplier
open PreparationVacuumGradedTransport PreparationVacuumFieldConstraintResponse
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumActionFieldLift PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActualFieldQuantization
open PreparationVacuumIndependentMomentumReturn PreparationVacuumHalfDensityFiber
open PreparationVacuumFullFieldRiesz PreparationVacuumPhysicalFeedback PreparationVacuumSourceActionJets
open CanonicalGradedSpatialSource FullQuantum.StateGreen StageNineHolonomicField
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def sourceMatterActionFiber (p : PhysicalMomentum) (u : JointParameter) : FockFiber→L[ℂ] FockFiber:=
  quantizer (sourceFixedMomentumAction p (sourceState u.2) (ambientState u))

theorem sourceMatterActionFiber_originalHalves (p : PhysicalMomentum) (u : JointParameter) (v : FockFiber) :
    fiberCoordinates (sourceMatterActionFiber p u v)=
      rawPairDensity
        (affineMatrix (fun i=> -(rawMomentumMatrix (sourceState u.2)*stateHamiltonian (ambientState u) i)) p)
        (affineMatrix (fun i=> -(rawMomentumMatrix (sourceState u.2)*stateHamiltonian (ambientState u) i)) (-p))
        (fiberCoordinates v) :=by
  change Fermion.quantize (sourceFixedMomentumAction p (sourceState u.2) (ambientState u)) (fiberCoordinates v)=_
  rw [sourceFixedMomentumAction_originalHalves]

theorem sourceMatterActionFiber_smooth (p : PhysicalMomentum) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (sourceMatterActionFiber p) u :=by
  have weight:=(sourceActionWeight_smooth (sourceState u.2) (sourceState_valid u.2 base)).comp u
    (sourceState_smooth.contDiffAt.comp u contDiffAt_snd)
  have symbol:=(sourceSymbol_smooth p (ambientState u) valid).comp u ambientState_smooth.contDiffAt
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((weight.mul symbol).const_smul (-(4:ℂ)))

def sourceMatterActionSample (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample u.2 (a u.2) (sourceMatterActionFiber p u (b u.2))

def sourceMatterMovingActionSample (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample (jointCurve u) (transportFiber u.1 u.2 1 (a u.2))
    (sourceMatterActionFiber p u (transportFiber u.1 u.2 1 (b u.2)))

theorem sourceMatterMovingActionSample_actual (p : PhysicalMomentum) (a b : QuantumTest)
    (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    sourceMatterMovingActionSample p a b u=sourceMatterActionSample p a b u :=by
  have commute:=congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T (b u.2))
    (GaussQuantumMultiplier.weight_commute (fun N=>halfRatio u.1 N u.2 1)
      (sourceFixedMomentumAction p (sourceState u.2) (ambientState u))).eq
  change transportFiber u.1 u.2 1 (sourceMatterActionFiber p u (b u.2))=
    sourceMatterActionFiber p u (transportFiber u.1 u.2 1 (b u.2)) at commute
  rw [sourceMatterMovingActionSample,←commute,←jointCurve_original]
  have valid : fieldCoordinateCurve u.1 1 u.2∈physicalChart:=by rw [jointCurve_original];exact moved
  exact pair_transport u.1 ⟨u.2,base⟩ 1 valid _ _

theorem sourceMatterActionSample_zero (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) :
    sourceMatterActionSample p a b (h,z)=0 :=by
  simp only [sourceMatterActionSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem sourceMatterActionSample_smooth (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (sourceMatterActionSample p a b) (h,z) :=by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (sourceMatterActionFiber_smooth p (h,z) (a.tsupport_subset inside)
        (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact sourceMatterActionSample_zero p a b u.1 u.2 hu

attribute [local irreducible] sourceFixedMomentumAction transportedRawSymbol

theorem sourceMatterActionSample_generated (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (z : physicalChart) (valid : ambientState (h,z.val)∈validStates) :
    HasDerivAt (fun r : ℝ=>sourceMatterActionSample p a b (h+r • reader,z.val))
      (noetherSample reader p a b (h,z.val)) 0 :=by
  have symbol:=sourceFixedMomentumAction_generated reader p (sourceState z.val) (ambientState (h,z.val)) valid
  have quantified:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 symbol
  let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z.val)).restrictScalars ℝ
  let P:=(pairRight z.val (a z.val)).restrictScalars ℝ
  have actual:=P.hasFDerivAt.comp_hasDerivAt 0 (E.hasFDerivAt.comp_hasDerivAt 0 quantified)
  change HasDerivAt
    (fun r : ℝ=>pairSample z.val (a z.val)
      (quantizer (sourceFixedMomentumAction p (sourceState z.val)
        (ambientState (h,z.val)+r • fieldDirection reader)) (b z.val)))
    (pairSample z.val (a z.val)
      (quantizer (transportedRawSymbol reader (sourceState z.val) (ambientState (h,z.val)) p) (b z.val))) 0 at actual
  have state (r : ℝ) : ambientState (h+r • reader,z.val)=ambientState (h,z.val)+r • fieldDirection reader:=by
    simp only [ambientState,map_add,map_smul,add_assoc]
    rfl
  have aligned : (fun r : ℝ=>sourceMatterActionSample p a b (h+r • reader,z.val))=
      (fun r : ℝ=>pairSample z.val (a z.val)
        (quantizer (sourceFixedMomentumAction p (sourceState z.val)
          (ambientState (h,z.val)+r • fieldDirection reader)) (b z.val))):=by
    funext r
    change pairSample z.val (a z.val)
      (quantizer (sourceFixedMomentumAction p (sourceState z.val) (ambientState (h+r • reader,z.val))) (b z.val))=_
    rw [state]
  rw [aligned]
  exact actual

def sourceMatterActionForm (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,sourceMatterActionSample p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem sourceMatterActionForm_C2 (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (sourceMatterActionForm p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (sourceMatterActionSample_smooth p a b) (sourceMatterActionSample_zero p a b)

theorem sourceMatterActionForm_generated (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (small : ‖h‖<ambientRadius a/2) :
    HasDerivAt (fun r : ℝ=>sourceMatterActionForm p a b (h+r • reader))
      (noetherForm reader p a b h) 0 :=by
  have differential:=source_integral_fderivative (sourceMatterActionSample p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) (ambientRadius_positive a) (sourceMatterActionSample_smooth p a b)
    (sourceMatterActionSample_zero p a b) h small
  have curve : HasDerivAt (fun r : ℝ=>h+r • reader) reader 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const reader).const_add h using 1
    simp only [one_smul]
  have original:=differential.comp_hasDerivAt_of_eq 0 curve (by simp only [zero_smul,add_zero])
  have smaller : ‖h‖<ambientRadius a:=small.trans (half_lt_self (ambientRadius_positive a))
  have integrable:=parameter_slice_integrable (parameterPartial (sourceMatterActionSample p a b))
    (tsupport a) a.hasCompactSupport h
    (fun z=>parameterPartial_smooth _ _ (sourceMatterActionSample_smooth p a b h z smaller))
    (parameterPartial_zero _ _ (isClosed_tsupport a) (sourceMatterActionSample_zero p a b))
  have each (z : SourceCoordinateSlice) : parameterPartial (sourceMatterActionSample p a b) (h,z) reader=
      noetherSample reader p a b (h,z):=by
    by_cases inside : z∈tsupport a
    · have d:=parameterPartial_derivative (sourceMatterActionSample p a b) h z
        (sourceMatterActionSample_smooth p a b h z smaller)
      have first:=d.comp_hasDerivAt_of_eq 0 curve (by simp only [zero_smul,add_zero])
      exact first.unique (sourceMatterActionSample_generated reader p a b h ⟨z,a.tsupport_subset inside⟩
        (ambientRadius_valid a h z smaller.le inside))
    · rw [parameterPartial_zero _ _ (isClosed_tsupport a) (sourceMatterActionSample_zero p a b) h z inside,
        noetherSample_zero reader p a b h z inside,zero_apply]
  have value : (∫z,parameterPartial (sourceMatterActionSample p a b) (h,z)
      ∂GaussHistoryHilbert.configurationMeasure) reader=noetherForm reader p a b h:=by
    rw [ContinuousLinearMap.integral_apply integrable]
    exact integral_congr_ae (Filter.Eventually.of_forall each)
  exact original.congr_deriv value

def sourceMatterActionOperator (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : SourceOperator:=
  finiteRiesz F (fun i j=>sourceMatterActionForm p (frameTest F i) (frameTest F j) h)

theorem sourceMatterActionOperator_C2 (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ContDiffAt ℝ 2 (sourceMatterActionOperator p F) 0 :=by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (sourceMatterActionForm_C2 p (frameTest F i) (frameTest F j)).smul contDiffAt_const

theorem sourceMatterActionOperator_gradient_near (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    (fun h=>fderiv ℝ (sourceMatterActionOperator p F) h reader)=ᶠ[𝓝 0] noetherReader reader p F :=by
  have bounds:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr (fun j=>
    ((continuous_norm.tendsto (0:Field289)).eventually
      (gt_mem_nhds (by simpa only [norm_zero] using half_pos (ambientRadius_positive (frameTest F i))))).and
    ((continuous_norm.tendsto (0:Field289)).eventually
      (gt_mem_nhds (by simpa only [norm_zero] using half_pos (ambientRadius_positive (frameTest F j)))))))
  filter_upwards [(sourceMatterActionOperator_C2 p F).eventually (by norm_num),bounds] with h smooth small
  have native : HasDerivAt (fun r : ℝ=>sourceMatterActionOperator p F (h+r • reader))
      (noetherReader reader p F h) 0:=by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (sourceMatterActionForm_generated reader p (frameTest F i) (frameTest F j) h (small i j).1).smul_const
      (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
  have curve : HasDerivAt (fun r : ℝ=>h+r • reader) reader 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const reader).const_add h using 1
    simp only [one_smul]
  have differential:=((smooth.differentiableAt (by norm_num)).hasFDerivAt).comp_hasDerivAt_of_eq 0 curve
    (by simp only [zero_smul,add_zero])
  exact differential.unique native

theorem sourceMatterActionOperator_gradient (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    fderiv ℝ (sourceMatterActionOperator p F) 0 reader=rawReader reader p F 0 :=
  (sourceMatterActionOperator_gradient_near reader p F).self_of_nhds.trans (noetherReader_source reader p F)

theorem sourceMatterActionOperator_contact (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    fderiv ℝ (fun h=>fderiv ℝ (sourceMatterActionOperator p F) h reader) 0 force=
      noetherReaderContact reader force p F :=
  congrArg (fun D : Field289→L[ℝ] SourceOperator=>D force)
    (sourceMatterActionOperator_gradient_near reader p F).fderiv_eq

def sourceMatterEulerPrepared (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age ((fderiv ℝ (sourceMatterActionOperator q.p q.F) h reader) (preparedPrimal q h age))

theorem sourceMatterEulerPrepared_near (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    (fun h=>sourceMatterEulerPrepared q reader h age)=ᶠ[𝓝 0]
      (fun h=>sourceMovingIndependentPrepared q reader h age) :=by
  filter_upwards [sourceMatterActionOperator_gradient_near reader q.p q.F,
    sourceMovingIndependentReader_near reader q.p q.F] with h current moving
  simp only [sourceMatterEulerPrepared,sourceMovingIndependentPrepared,current,moving]

theorem sourceMatterEulerPrepared_source (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    sourceMatterEulerPrepared q reader 0 age=densityRead q reader 0 age :=
  (sourceMatterEulerPrepared_near q reader age).self_of_nhds.trans
    (sourceMovingIndependentPrepared_source q reader age)

theorem sourceMatterEulerPrepared_response (q : PhysicalResponsePoint) (reader force : Field289)
    (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceMatterEulerPrepared q reader (r • force) age)
      (noetherPreparedSlope q reader force age) 0 :=by
  apply (sourceMovingIndependentPrepared_generated q reader force age hz hw).congr_of_eventuallyEq
  exact (sourceMatterEulerPrepared_near q reader age).comp_tendsto
    (by simpa using ((show Continuous (fun r : ℝ=>r • force) from
      continuous_id.smul continuous_const).tendsto (0:ℝ)))

theorem sourceMatterEulerPrepared_C2 (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (fun h=>sourceMatterEulerPrepared q reader h age) 0 :=
  (sourceMovingIndependentPrepared_C2 q reader age hz hw).congr_of_eventuallyEq
    (sourceMatterEulerPrepared_near q reader age)

attribute [local irreducible] sourceMatterEulerPrepared sourceMovingIndependentPrepared

theorem sourceMatterEulerPrepared_mixed (q : PhysicalResponsePoint) (reader f g : Field289) (age : ℝ) :
    fderiv ℝ (fderiv ℝ (fun h=>sourceMatterEulerPrepared q reader h age)) 0 f g=
      fderiv ℝ (fderiv ℝ (fun h=>sourceMovingIndependentPrepared q reader h age)) 0 f g :=by
  exact congrArg (fun D : Field289→L[ℝ] (Field289→L[ℝ] ℂ)=>D f g)
    ((sourceMatterEulerPrepared_near q reader age).fderiv (𝕜:=ℝ)).fderiv_eq

end LowEnergy.PreparationVacuumFixedMomentumActionReturn
