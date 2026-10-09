import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationMovingNoetherDensityTransport

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNoetherChart
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
abbrev Operator:=H→L[ℂ] H
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : NormedAlgebra ℝ SourceMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : NormedAlgebra ℝ FullMatrix:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : FiniteDimensional ℂ FullMatrix:=Matrix.finiteDimensional
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace
local instance : NormedAlgebra ℝ Operator:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] transportedRawSymbol noetherContactSymbol rawActionSymbol
  rawMomentumMatrix rawMomentumInverse densityActionMatrix densityActionInverse

def noetherFiber (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) : FockFiber→L[ℂ] FockFiber:=
  quantizer (transportedRawSymbol reader (sourceState u.2) (ambientState u) p)

theorem noetherFiber_source (reader : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    noetherFiber reader p (0,z.val)=rawFiber reader p (0,z.val) :=by
  have valid : sourceState z.val∈validStates:=⟨coframe_nondegenerate z,temporal_noncharacteristic z⟩
  have source:=transportedRawSymbol_source reader (sourceState z.val) valid p
  change quantizer (transportedRawSymbol reader (sourceState z.val) (ambientState (0,z.val)) p)=
    quantizer (rawActionSymbol reader p (ambientState (0,z.val)))
  rw [ambientState_zero,source]

theorem noetherFiber_generated (reader force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>noetherFiber reader p (r • force,z.val))
      (quantizer (noetherContactSymbol reader force (sourceState z.val) p)) 0 :=by
  have source:=(quantizer.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (noetherContactSymbol_generated reader force z p)
  have ray (r : ℝ) : ambientState (r • force,z.val)=sourceState z.val+r • fieldDirection force:=by
    simp only [ambientState,map_smul]
    rfl
  have aligned : (fun r : ℝ=>noetherFiber reader p (r • force,z.val))=
      (fun r : ℝ=>quantizer (transportedRawSymbol reader (sourceState z.val)
        (sourceState z.val+r • fieldDirection force) p)):=by
    funext r
    unfold noetherFiber
    rw [ray]
  rw [aligned]
  convert! source using 1

theorem transportedDensity_smooth (reader : Field289) (i : Fin 4) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (fun w=>transportedDensity reader (sourceState w.2) (ambientState w) i) u :=by
  have bvalid : sourceState u.2∈validStates:=⟨coframe_nondegenerate ⟨u.2,base⟩,temporal_noncharacteristic ⟨u.2,base⟩⟩
  have bs:=sourceState_smooth.contDiffAt.comp u contDiffAt_snd
  have cs : ContDiffAt ℝ ∞ ambientState u:=ambientState_smooth.contDiffAt
  have b:=(inversePhase_smooth _ bvalid).comp u bs
  have c:=(statePhase_smooth _ valid.1 valid.2).comp u cs
  have d:=(densityVariation_smooth reader _ valid.1 valid.2 i).comp u cs
  have bm : ContDiffAt ℝ ∞ (fun w : JointParameter=>rawMomentumMatrix (sourceState w.2)) u:=by
    unfold rawMomentumMatrix
    exact contDiffAt_const.mul b
  have ci : ContDiffAt ℝ ∞ (fun w : JointParameter=>rawMomentumInverse (ambientState w)) u:=by
    unfold rawMomentumInverse
    exact c.mul contDiffAt_const
  change ContDiffAt ℝ ∞ (fun w : JointParameter=>
    rawMomentumMatrix (sourceState w.2)*rawMomentumInverse (ambientState w)*densityActionMatrix*
      densityVariation reader (ambientState w) i) u
  exact ((bm.mul ci).mul contDiffAt_const).mul d

theorem noetherFiber_smooth (reader : Field289) (p : PhysicalMomentum) (u : JointParameter)
    (base : u.2∈physicalChart) (valid : ambientState u∈validStates) :
    ContDiffAt ℝ ∞ (noetherFiber reader p) u :=by
  unfold noetherFiber transportedRawSymbol
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((rawFourier p).toContinuousLinearMap.contDiff.contDiffAt.comp u
      (contDiffAt_pi.mpr (fun i=>transportedDensity_smooth reader i u base valid)))

def noetherSample (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample u.2 (a u.2) (noetherFiber reader p u (b u.2))

theorem noetherSample_zero (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) : noetherSample reader p a b (h,z)=0 :=by
  simp only [noetherSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

theorem noetherSample_near_smooth (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest)
    (h : Field289) (z : SourceCoordinateSlice) (small : ‖h‖<ambientRadius a) :
    ContDiffAt ℝ ∞ (noetherSample reader p a b) (h,z) :=by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (noetherFiber_smooth reader p (h,z) (a.tsupport_subset inside) (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact noetherSample_zero reader p a b u.1 u.2 hu

def noetherForm (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,noetherSample reader p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem noetherForm_C2 (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (noetherForm reader p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (noetherSample_near_smooth reader p a b) (noetherSample_zero reader p a b)

theorem noetherForm_source (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    noetherForm reader p a b 0=rawForm reader p a b 0 :=by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases inside : z∈tsupport a
  · change pairSample z (a z) (noetherFiber reader p (0,z) (b z))=pairSample z (a z) (rawFiber reader p (0,z) (b z))
    rw [noetherFiber_source reader p ⟨z,a.tsupport_subset inside⟩]
  · simp only [noetherForm,rawForm,noetherSample,rawSample,image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left]

def noetherContactForm (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∫z,pairSample z (a z) (quantizer (noetherContactSymbol reader force (sourceState z) p) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

theorem noetherForm_generated (reader force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>noetherForm reader p a b (r • force))
      (noetherContactForm reader force p a b) 0 :=by
  have differential:=source_integral_fderivative (noetherSample reader p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) (ambientRadius_positive a) (noetherSample_near_smooth reader p a b)
    (noetherSample_zero reader p a b) 0 (by simpa only [norm_zero] using half_pos (ambientRadius_positive a))
  have original:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have integrable:=parameter_slice_integrable (parameterPartial (noetherSample reader p a b))
    (tsupport a) a.hasCompactSupport 0
    (fun z=>parameterPartial_smooth _ _ (noetherSample_near_smooth reader p a b 0 z (by simpa using ambientRadius_positive a)))
    (parameterPartial_zero _ _ (isClosed_tsupport a) (noetherSample_zero reader p a b))
  have each (z : SourceCoordinateSlice) : parameterPartial (noetherSample reader p a b) (0,z) force=
      pairSample z (a z) (quantizer (noetherContactSymbol reader force (sourceState z) p) (b z)):=by
    by_cases inside : z∈tsupport a
    · have d:=parameterPartial_derivative (noetherSample reader p a b) 0 z
        (noetherSample_near_smooth reader p a b 0 z (by simpa using ambientRadius_positive a))
      have first:=d.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
      let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z)).restrictScalars ℝ
      let P:=(PreparationVacuumHalfDensityFiber.pairRight z (a z)).restrictScalars ℝ
      have second:=P.hasFDerivAt.comp_hasDerivAt 0
        (E.hasFDerivAt.comp_hasDerivAt 0 (noetherFiber_generated reader force p ⟨z,a.tsupport_subset inside⟩))
      exact first.unique second
    · rw [parameterPartial_zero _ _ (isClosed_tsupport a) (noetherSample_zero reader p a b) 0 z inside]
      simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,zero_apply]
  have value : (∫z,parameterPartial (noetherSample reader p a b) (0,z) ∂GaussHistoryHilbert.configurationMeasure) force=
      noetherContactForm reader force p a b:=by
    rw [ContinuousLinearMap.integral_apply integrable]
    exact integral_congr_ae (Filter.Eventually.of_forall each)
  exact original.congr_deriv value

def noetherReader (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : Operator:=
  finiteRiesz F (fun i j=>noetherForm reader p (frameTest F i) (frameTest F j) h)

theorem noetherReader_C2 (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    ContDiffAt ℝ 2 (noetherReader reader p F) 0 :=by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (noetherForm_C2 reader p (frameTest F i) (frameTest F j)).smul contDiffAt_const

theorem noetherReader_source (reader : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReader reader p F 0=PreparationVacuumRawJointFeedback.rawReader reader p F 0 :=by
  unfold noetherReader PreparationVacuumRawJointFeedback.rawReader
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>noetherForm_source reader p _ _)))

def noetherReaderContact (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Operator:=
  fderiv ℝ (noetherReader reader p F) 0 force

theorem noetherReader_generated (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>noetherReader reader p F (r • force)) (noetherReaderContact reader force p F) 0 :=
  (noetherReader_C2 reader p F).differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (fieldRay_derivative force 0) (by simp)

theorem noetherReaderContact_source (reader force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    noetherReaderContact reader force p F=
      finiteRiesz F (fun i j=>noetherContactForm reader force p (frameTest F i) (frameTest F j)) :=by
  have original:=noetherReader_generated reader force p F
  have generated : HasDerivAt (fun r : ℝ=>noetherReader reader p F (r • force))
      (finiteRiesz F (fun i j=>noetherContactForm reader force p (frameTest F i) (frameTest F j))) 0:=by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (noetherForm_generated reader force p (frameTest F i) (frameTest F j)).smul_const
      (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
  exact original.unique generated

def noetherPreparedCurrent (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (noetherReader reader q.p q.F h (preparedPrimal q h age))

theorem noetherPreparedCurrent_source (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    noetherPreparedCurrent q reader 0 age=densityRead q reader 0 age :=by
  rw [noetherPreparedCurrent,densityRead,noetherReader_source]

def noetherPreparedSlope (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ) : ℂ:=
  densitySlope q reader force age-
    preparedDual q 0 age (rawReaderContact reader force q.p q.F (preparedPrimal q 0 age))+
    preparedDual q 0 age (noetherReaderContact reader force q.p q.F (preparedPrimal q 0 age))

theorem noetherPreparedCurrent_generated (q : PhysicalResponsePoint) (reader force : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>noetherPreparedCurrent q reader (r • force) age)
      (noetherPreparedSlope q reader force age) 0 :=by
  let kernel (h : Field289) : Operator:=
    physicalTime (q.p+q.k) q.F (-age) h*jointResolvent (q.p+q.k) q.F q.z h*
      noetherReader reader q.p q.F h*jointResolvent q.p q.F q.w h*physicalTime q.p q.F age h
  have tl:=physicalTime_direction force (q.p+q.k) q.F (-age)
  have rl:=inverse_direction (q.p+q.k) q.F q.z hz force
  have j:=noetherReader_generated reader force q.p q.F
  have rr:=inverse_direction q.p q.F q.w hw force
  have tr:=physicalTime_direction force q.p q.F age
  have original:=((((tl.mul rl).mul j).mul rr).mul tr)
  have read:=paired_derivative original (responseLeft q) (responseRight q)
  convert! read using 1
  all_goals simp only [noetherPreparedSlope,densitySlope,dualSlope,preparedDual,independentDual,preparedPrimal,primalSlope,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,add_apply,map_add,inner_add_right,mul_apply_eq_comp,
      noetherReader_source,zero_smul,Pi.mul_apply,mul_add,add_mul]
  all_goals abel

end LowEnergy.PreparationVacuumNoetherChart
