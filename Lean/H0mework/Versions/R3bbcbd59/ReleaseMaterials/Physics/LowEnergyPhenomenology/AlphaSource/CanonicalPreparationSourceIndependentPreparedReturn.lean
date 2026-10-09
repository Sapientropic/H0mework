import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceIndependentHalfDensityFields

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumIndependentMomentumReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open GaussHistoryHilbert GaussCoreHilbert GaussFockPair GaussQuantumMultiplier
open GaussCoreDifferential
open PreparationVacuumGradedTransport PreparationVacuumFieldConstraintResponse
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumSourceFieldFamily PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumFullFieldRiesz PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource FullQuantum.StateGreen
open PreparationVacuumSourceActionJets
open MeasureTheory Filter Set
open scoped Topology ContDiff BigOperators Matrix InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
abbrev SourceOperator:=H→L[ℂ] H
local instance : NormedAlgebra ℝ SourceOperator:=NormedAlgebra.restrictScalars ℝ ℂ _

def sourceMovingIndependentEnd (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) : FockEnd:=
  sourceConjugateField u.1 1 u.2
    (rawPairDensity
      (Quantum.operatorMatrix (sourceMovingDensityMother reader p (sourceState u.2) (ambientState u)))
      (Quantum.operatorMatrix (sourceMovingDensityMother reader (-p) (sourceState u.2) (ambientState u))))

def sourceMovingIndependentFiber (reader : Field289) (p : PhysicalMomentum) (u : JointParameter) :
    FockFiber→L[ℂ] FockFiber:=
  LinearMap.toContinuousLinearMap
    (fiberCoordinates.symm.toLinearMap.comp
      ((sourceMovingIndependentEnd reader p u).comp fiberCoordinates.toLinearMap))

theorem sourceMovingIndependentFiber_actual (reader : Field289) (p : PhysicalMomentum)
    (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    sourceMovingIndependentFiber reader p u=noetherFiber reader p u :=by
  have valid : fieldCoordinateCurve u.1 1 u.2∈physicalChart:=by
    rw [jointCurve_original]
    exact moved
  have actual:=sourceConjugateField_independentDensity u.1 1 ⟨u.2,base⟩ valid reader p
    (sourceState u.2) (ambientState u)
  apply ContinuousLinearMap.ext
  intro v
  apply fiberCoordinates.injective
  change sourceMovingIndependentEnd reader p u (fiberCoordinates v)=
    Fermion.quantize (transportedRawSymbol reader (sourceState u.2) (ambientState u) p) (fiberCoordinates v)
  exact LinearMap.congr_fun actual _

theorem sourceMovingIndependentFiber_transport (reader : Field289) (p : PhysicalMomentum)
    (u : JointParameter) (v : FockFiber) :
    noetherFiber reader p u (transportFiber u.1 u.2 1 v)=
      transportFiber u.1 u.2 1 (noetherFiber reader p u v) :=by
  exact (congrArg (fun T : FockFiber→L[ℂ] FockFiber=>T v)
    (GaussQuantumMultiplier.weight_commute (fun N=>halfRatio u.1 N u.2 1)
      (transportedRawSymbol reader (sourceState u.2) (ambientState u) p)).eq).symm

def sourceMovingIndependentSample (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample (jointCurve u) (transportFiber u.1 u.2 1 (a u.2))
    (sourceMovingIndependentFiber reader p u (transportFiber u.1 u.2 1 (b u.2)))

theorem sourceMovingIndependentSample_actual (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (u : JointParameter) (base : u.2∈physicalChart) (moved : jointCurve u∈physicalChart) :
    sourceMovingIndependentSample reader p a b u=noetherSample reader p a b u :=by
  rw [sourceMovingIndependentSample,sourceMovingIndependentFiber_actual reader p u base moved,
    sourceMovingIndependentFiber_transport]
  have curve : fieldCoordinateCurve u.1 1 u.2∈physicalChart:=by rw [jointCurve_original];exact moved
  rw [←jointCurve_original,pair_transport u.1 ⟨u.2,base⟩ 1 curve]
  rfl

theorem sourceMovingIndependentSample_zero (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice) (outside : z∉tsupport a) :
    sourceMovingIndependentSample reader p a b (h,z)=0 :=by
  simp only [sourceMovingIndependentSample,image_eq_zero_of_notMem_tsupport outside,map_zero,pairSample_zero_left]

def sourceMovingIndependentForm (reader : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,sourceMovingIndependentSample reader p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

theorem sourceMovingIndependentForm_near (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    sourceMovingIndependentForm reader p a b=ᶠ[𝓝 0] noetherForm reader p a b :=by
  have nearby : ∀ᶠh : Field289 in 𝓝 0,‖h‖<jointRadius a:=
    (continuous_norm.tendsto 0).eventually (gt_mem_nhds (by simpa using jointRadius_positive a))
  filter_upwards [nearby] with h small
  unfold sourceMovingIndependentForm noetherForm
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change sourceMovingIndependentSample reader p a b (h,z)=noetherSample reader p a b (h,z)
  by_cases inside : z∈tsupport a
  · exact sourceMovingIndependentSample_actual reader p a b (h,z) (a.tsupport_subset inside)
      (jointRadius_valid a h z small.le inside)
  · rw [sourceMovingIndependentSample_zero reader p a b h z inside,
      noetherSample_zero reader p a b h z inside]

theorem sourceMovingIndependentForm_C2 (reader : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    ContDiffAt ℝ 2 (sourceMovingIndependentForm reader p a b) 0 :=
  (noetherForm_C2 reader p a b).congr_of_eventuallyEq (sourceMovingIndependentForm_near reader p a b)

theorem sourceMovingIndependentForm_contact (reader force : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>sourceMovingIndependentForm reader p a b (r • force))
      (noetherContactForm reader force p a b) 0 :=by
  apply (noetherForm_generated reader force p a b).congr_of_eventuallyEq
  exact (sourceMovingIndependentForm_near reader p a b).comp_tendsto
    (by simpa using ((show Continuous (fun r : ℝ=>r • force) from
      continuous_id.smul continuous_const).tendsto (0:ℝ)))

theorem sourceMovingIndependentForm_mixed (reader f g : Field289) (p : PhysicalMomentum)
    (a b : QuantumTest) :
    fderiv ℝ (fderiv ℝ (sourceMovingIndependentForm reader p a b)) 0 f g=
      fderiv ℝ (fderiv ℝ (noetherForm reader p a b)) 0 f g :=by
  exact congrArg (fun D : Field289→L[ℝ] (Field289→L[ℝ] ℂ)=>D f g)
    ((sourceMovingIndependentForm_near reader p a b).fderiv (𝕜:=ℝ)).fderiv_eq

def sourceMovingIndependentReader (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (h : Field289) : SourceOperator:=
  finiteRiesz F (fun i j=>sourceMovingIndependentForm reader p (frameTest F i) (frameTest F j) h)

theorem sourceMovingIndependentReader_near (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    sourceMovingIndependentReader reader p F=ᶠ[𝓝 0] noetherReader reader p F :=by
  have nearby:=Filter.eventually_all.mpr (fun i=>Filter.eventually_all.mpr
    (fun j=>sourceMovingIndependentForm_near reader p (frameTest F i) (frameTest F j)))
  filter_upwards [nearby] with h same
  exact congrArg (finiteRiesz F) (funext (fun i=>funext (fun j=>same i j)))

theorem sourceMovingIndependentReader_C2 (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) : ContDiffAt ℝ 2 (sourceMovingIndependentReader reader p F) 0 :=
  (noetherReader_C2 reader p F).congr_of_eventuallyEq (sourceMovingIndependentReader_near reader p F)

theorem sourceMovingIndependentReader_source (reader : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    sourceMovingIndependentReader reader p F 0=rawReader reader p F 0 :=
  (sourceMovingIndependentReader_near reader p F).self_of_nhds.trans (noetherReader_source reader p F)

theorem sourceMovingIndependentReader_contact (reader force : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    fderiv ℝ (sourceMovingIndependentReader reader p F) 0 force=noetherReaderContact reader force p F :=
  congrArg (fun D : Field289→L[ℝ] SourceOperator=>D force)
    (sourceMovingIndependentReader_near reader p F).fderiv_eq

theorem sourceMovingIndependentReader_mixed (reader f g : Field289) (p : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) :
    fderiv ℝ (fderiv ℝ (sourceMovingIndependentReader reader p F)) 0 f g=
      fderiv ℝ (fderiv ℝ (noetherReader reader p F)) 0 f g :=by
  exact congrArg (fun D : Field289→L[ℝ] (Field289→L[ℝ] SourceOperator)=>D f g)
    ((sourceMovingIndependentReader_near reader p F).fderiv (𝕜:=ℝ)).fderiv_eq

def sourceMovingIndependentPrepared (q : PhysicalResponsePoint) (reader h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (sourceMovingIndependentReader reader q.p q.F h (preparedPrimal q h age))

theorem sourceMovingIndependentPrepared_near (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    (fun h=>sourceMovingIndependentPrepared q reader h age)=ᶠ[𝓝 0]
      (fun h=>noetherPreparedCurrent q reader h age) :=by
  filter_upwards [sourceMovingIndependentReader_near reader q.p q.F] with h same
  simp only [sourceMovingIndependentPrepared,noetherPreparedCurrent,same]

theorem sourceMovingIndependentPrepared_source (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ) :
    sourceMovingIndependentPrepared q reader 0 age=densityRead q reader 0 age :=
  (sourceMovingIndependentPrepared_near q reader age).self_of_nhds.trans
    (noetherPreparedCurrent_source q reader age)

theorem sourceMovingIndependentPrepared_generated (q : PhysicalResponsePoint) (reader force : Field289)
    (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>sourceMovingIndependentPrepared q reader (r • force) age)
      (noetherPreparedSlope q reader force age) 0 :=by
  apply (noetherPreparedCurrent_generated q reader force age hz hw).congr_of_eventuallyEq
  exact (sourceMovingIndependentPrepared_near q reader age).comp_tendsto
    (by simpa using ((show Continuous (fun r : ℝ=>r • force) from
      continuous_id.smul continuous_const).tendsto (0:ℝ)))

def sourceMovingIndependentKernel (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ)
    (h : Field289) : SourceOperator:=
  physicalTime (q.p+q.k) q.F (-age) h*jointResolvent (q.p+q.k) q.F q.z h*
    sourceMovingIndependentReader reader q.p q.F h*jointResolvent q.p q.F q.w h*
    physicalTime q.p q.F age h

theorem sourceMovingIndependentPrepared_kernel (q : PhysicalResponsePoint) (reader h : Field289)
    (age : ℝ) :
    sourceMovingIndependentPrepared q reader h age=
      inner ℂ (responseLeft q) (sourceMovingIndependentKernel q reader age h (responseRight q)) :=by
  simp only [sourceMovingIndependentPrepared,preparedDual,independentDual,preparedPrimal,
    sourceMovingIndependentKernel,mul_apply_eq_comp,ContinuousLinearMap.comp_apply,innerSL_apply_apply]

theorem sourceMovingIndependentKernel_C2 (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (sourceMovingIndependentKernel q reader age) 0 :=by
  have curve : ContDiffAt ℝ 2 (fun h : Field289=>(h,age)) 0:=contDiffAt_id.prodMk contDiffAt_const
  have left:=(jointPhysicalTime_C2 (q.p+q.k) q.F (-1) age).comp 0 curve
  have right:=(jointPhysicalTime_C2 q.p q.F 1 age).comp 0 curve
  have original:=(((left.mul (jointResolvent_C2 (q.p+q.k) q.F q.z hz)).mul
    (sourceMovingIndependentReader_C2 reader q.p q.F)).mul (jointResolvent_C2 q.p q.F q.w hw)).mul right
  convert! original using 1
  funext h
  simp only [sourceMovingIndependentKernel,jointPhysicalTime,Function.comp_apply,neg_one_mul,one_mul]

theorem sourceMovingIndependentPrepared_C2 (q : PhysicalResponsePoint) (reader : Field289) (age : ℝ)
    (hz : q.z.im≠0) (hw : q.w.im≠0) :
    ContDiffAt ℝ 2 (fun h=>sourceMovingIndependentPrepared q reader h age) 0 :=by
  let E : SourceOperator→L[ℝ] ℂ:=
    ((innerSL ℂ (responseLeft q)).comp (ContinuousLinearMap.apply ℂ H (responseRight q))).restrictScalars ℝ
  have actual:=E.contDiff.contDiffAt.comp 0 (sourceMovingIndependentKernel_C2 q reader age hz hw)
  convert! actual using 1

attribute [local irreducible] sourceMovingIndependentPrepared noetherPreparedCurrent

theorem sourceMovingIndependentPrepared_mixed (q : PhysicalResponsePoint) (reader f g : Field289) (age : ℝ) :
    fderiv ℝ (fderiv ℝ (fun h=>sourceMovingIndependentPrepared q reader h age)) 0 f g=
      fderiv ℝ (fderiv ℝ (fun h=>noetherPreparedCurrent q reader h age)) 0 f g :=by
  exact congrArg (fun D : Field289→L[ℝ] (Field289→L[ℝ] ℂ)=>D f g)
    ((sourceMovingIndependentPrepared_near q reader age).fderiv (𝕜:=ℝ)).fderiv_eq

end LowEnergy.PreparationVacuumIndependentMomentumReturn
