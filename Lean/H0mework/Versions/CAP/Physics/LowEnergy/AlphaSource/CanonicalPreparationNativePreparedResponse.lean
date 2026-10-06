import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeActionJets

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeLocalWard
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart
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

def nativeJointFiber (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (u : JointParameter) : FockFiber→L[ℂ] FockFiber:=
  nativeNoetherFiber n theta derivative p (sourceState u.2) (ambientState u)

 theorem nativeJointFiber_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (u : JointParameter) (base : u.2∈physicalChart)
    (valid : ambientState u∈validStates) : ContDiffAt ℝ ∞ (nativeJointFiber n theta derivative p) u :=by
  have bvalid : sourceState u.2∈validStates:=
    ⟨coframe_nondegenerate ⟨u.2,base⟩,temporal_noncharacteristic ⟨u.2,base⟩⟩
  have bs:=sourceState_smooth.contDiffAt.comp u contDiffAt_snd
  have weight:=(sourceActionWeight_smooth (sourceState u.2) bvalid).comp u bs
  have current:=(nativeFirst_smooth n theta derivative p (ambientState u) valid).comp u ambientState_smooth.contDiffAt
  change ContDiffAt ℝ ∞ (fun w=>quantizer (-(4:ℂ) •
    (sourceActionWeight (sourceState w.2)*nativeFirst n theta derivative p (ambientState w)))) u
  exact (quantizer.toContinuousLinearMap.restrictScalars ℝ).contDiff.contDiffAt.comp u
    ((weight.mul current).const_smul _)

 theorem nativeJointFiber_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun r : ℝ=>nativeJointFiber n theta derivative p (r • force,z.val))
      (quantizer (nativeNoetherMixed n theta derivative force p (sourceState z.val) (sourceState z.val))) 0 :=by
  have ray (r : ℝ) : ambientState (r • force,z.val)=sourceState z.val+r • fieldDirection force:=by
    simp only [ambientState,map_smul]
    rfl
  simpa only [nativeJointFiber,ray] using nativeNoetherFiber_generated n theta derivative force p z

 def nativeSample (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) (u : JointParameter) : ℂ:=
  pairSample u.2 (a u.2) (nativeJointFiber n theta derivative p u (b u.2))

 theorem nativeSample_zero (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice)
    (outside : z∉tsupport a) : nativeSample n theta derivative p a b (h,z)=0 :=by
  simp only [nativeSample,image_eq_zero_of_notMem_tsupport outside,pairSample_zero_left]

 theorem nativeSample_near_smooth (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) (z : SourceCoordinateSlice)
    (small : ‖h‖<ambientRadius a) : ContDiffAt ℝ ∞ (nativeSample n theta derivative p a b) (h,z) :=by
  by_cases inside : z∈tsupport a
  · let R:=ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have coefficient:=R.contDiff.contDiffAt.comp (h,z)
      (nativeJointFiber_smooth n theta derivative p (h,z) (a.tsupport_subset inside)
        (ambientRadius_valid a h z small.le inside))
    exact pairSample_param Prod.snd _ _ (h,z) (a.tsupport_subset inside) contDiffAt_snd
      (a.contDiff.contDiffAt.comp (h,z) contDiffAt_snd)
      (coefficient.clm_apply (b.contDiff.contDiffAt.comp (h,z) contDiffAt_snd))
  · apply (contDiffAt_const (c:=(0:ℂ))).congr_of_eventuallyEq
    filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
      ((isClosed_tsupport a).isOpen_compl.mem_nhds inside)] with u hu
    exact nativeSample_zero n theta derivative p a b u.1 u.2 hu

 def nativeForm (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) (h : Field289) : ℂ:=
  ∫z,nativeSample n theta derivative p a b (h,z) ∂GaussHistoryHilbert.configurationMeasure

 theorem nativeForm_C2 (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) : ContDiffAt ℝ 2 (nativeForm n theta derivative p a b) 0 :=
  source_integral_C2 _ (tsupport a) a.hasCompactSupport (ambientRadius a) (ambientRadius_positive a)
    (nativeSample_near_smooth n theta derivative p a b) (nativeSample_zero n theta derivative p a b)

 theorem nativeForm_source (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (a b : QuantumTest) :
    nativeForm n theta derivative p a b 0=
      ∫z,pairSample z (a z) (quantizer (nativeRaw n theta derivative p (sourceState z)) (b z))
        ∂GaussHistoryHilbert.configurationMeasure :=by
  simp only [nativeForm,nativeSample,nativeJointFiber,nativeNoetherFiber,ambientState_zero,nativeNoether_source]

 theorem nativeMixed_complement (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (z : SourceCoordinateSlice) :
    nativeMixed n theta derivative force p (sourceState z)=
      symbolSecond p (sourceState z) (stateVariation n theta derivative (sourceState z))
        (sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z))+
      symbolSecond p (sourceState z) (stateVariation n theta derivative (sourceState z)) (complement force z)+
      symbolFirst p (sourceState z) (stateContact n theta
        (sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z)))+
      symbolFirst p (sourceState z) (stateContact n theta (complement force z)) :=by
  have split : fieldDirection force=sliceState (PreparationVacuumFieldConstraintResponse.fieldVector force z)+complement force z:=by
    rw [complement]
    abel
  rw [nativeMixed,stateContact_coordinate_complement n theta force z]
  conv_lhs=>arg 1;unfold symbolSecond;rw [split,map_add,add_apply]
  rw [symbolFirst,map_add]
  abel

 def nativeContactForm (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) : ℂ:=
  ∫z,pairSample z (a z) (quantizer (nativeNoetherMixed n theta derivative force p (sourceState z) (sourceState z)) (b z))
    ∂GaussHistoryHilbert.configurationMeasure

 theorem nativeForm_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (a b : QuantumTest) :
    HasDerivAt (fun r : ℝ=>nativeForm n theta derivative p a b (r • force))
      (nativeContactForm n theta derivative force p a b) 0 :=by
  have differential:=source_integral_fderivative (nativeSample n theta derivative p a b) (tsupport a) a.hasCompactSupport
    (ambientRadius a) (ambientRadius_positive a) (nativeSample_near_smooth n theta derivative p a b)
    (nativeSample_zero n theta derivative p a b) 0 (by simpa only [norm_zero] using half_pos (ambientRadius_positive a))
  have original:=differential.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
  have integrable:=parameter_slice_integrable (parameterPartial (nativeSample n theta derivative p a b))
    (tsupport a) a.hasCompactSupport 0
    (fun z=>parameterPartial_smooth _ _ (nativeSample_near_smooth n theta derivative p a b 0 z
      (by simpa using ambientRadius_positive a)))
    (parameterPartial_zero _ _ (isClosed_tsupport a) (nativeSample_zero n theta derivative p a b))
  have each (z : SourceCoordinateSlice) : parameterPartial (nativeSample n theta derivative p a b) (0,z) force=
      pairSample z (a z) (quantizer (nativeNoetherMixed n theta derivative force p (sourceState z) (sourceState z)) (b z)):=by
    by_cases inside : z∈tsupport a
    · have d:=parameterPartial_derivative (nativeSample n theta derivative p a b) 0 z
        (nativeSample_near_smooth n theta derivative p a b 0 z (by simpa using ambientRadius_positive a))
      have first:=d.comp_hasDerivAt_of_eq 0 (fieldRay_derivative force 0) (by simp)
      let E:=(ContinuousLinearMap.apply ℂ FockFiber (b z)).restrictScalars ℝ
      let P:=(PreparationVacuumHalfDensityFiber.pairRight z (a z)).restrictScalars ℝ
      have second:=P.hasFDerivAt.comp_hasDerivAt 0
        (E.hasFDerivAt.comp_hasDerivAt 0 (nativeJointFiber_generated n theta derivative force p ⟨z,a.tsupport_subset inside⟩))
      exact first.unique second
    · rw [parameterPartial_zero _ _ (isClosed_tsupport a) (nativeSample_zero n theta derivative p a b) 0 z inside]
      simp only [image_eq_zero_of_notMem_tsupport inside,pairSample_zero_left,zero_apply]
  have value : (∫z,parameterPartial (nativeSample n theta derivative p a b) (0,z) ∂GaussHistoryHilbert.configurationMeasure) force=
      nativeContactForm n theta derivative force p a b:=by
    rw [ContinuousLinearMap.integral_apply integrable]
    exact integral_congr_ae (Filter.Eventually.of_forall each)
  exact original.congr_deriv value

 def nativeReader (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) : Operator:=
  finiteRiesz F (fun i j=>nativeForm n theta derivative p (frameTest F i) (frameTest F j) h)

 theorem nativeReader_C2 (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : ContDiffAt ℝ 2 (nativeReader n theta derivative p F) 0 :=by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (nativeForm_C2 n theta derivative p (frameTest F i) (frameTest F j)).smul contDiffAt_const

 def nativeReaderContact (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Operator:=
  fderiv ℝ (nativeReader n theta derivative p F) 0 force

 theorem nativeReader_generated (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (fun r : ℝ=>nativeReader n theta derivative p F (r • force))
      (nativeReaderContact n theta derivative force p F) 0 :=
  (nativeReader_C2 n theta derivative p F).differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt_of_eq 0
    (fieldRay_derivative force 0) (by simp)

 theorem nativeReaderContact_source (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    nativeReaderContact n theta derivative force p F=
      finiteRiesz F (fun i j=>nativeContactForm n theta derivative force p (frameTest F i) (frameTest F j)) :=by
  have original:=nativeReader_generated n theta derivative force p F
  have generated : HasDerivAt (fun r : ℝ=>nativeReader n theta derivative p F (r • force))
      (finiteRiesz F (fun i j=>nativeContactForm n theta derivative force p (frameTest F i) (frameTest F j))) 0:=by
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro j _
    exact (nativeForm_generated n theta derivative force p (frameTest F i) (frameTest F j)).smul_const
      (InnerProductSpace.rankOne ℂ (frameVector F i) (frameVector F j))
  exact original.unique generated

attribute [local irreducible] nativeReader nativeReaderContact physicalTime timeSlope jointResolvent jointCurrent

 def nativePreparedCurrent (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (h : Field289) (age : ℝ) : ℂ:=
  preparedDual q h age (nativeReader n theta derivative q.p q.F h (preparedPrimal q h age))

 def nativePreparedKernel (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (h : Field289) (age : ℝ) : Operator:=
  physicalTime (q.p+q.k) q.F (-age) h*jointResolvent (q.p+q.k) q.F q.z h*
    nativeReader n theta derivative q.p q.F h*jointResolvent q.p q.F q.w h*physicalTime q.p q.F age h

 def nativePreparedFive (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (age : ℝ) : Operator:=
  (((timeSlope force (q.p+q.k) q.F (-age)*jointResolvent (q.p+q.k) q.F q.z 0+
      physicalTime (q.p+q.k) q.F (-age) 0*(-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 force*jointResolvent (q.p+q.k) q.F q.z 0)))*
        nativeReader n theta derivative q.p q.F 0+
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0)*
        nativeReaderContact n theta derivative force q.p q.F)*jointResolvent q.p q.F q.w 0+
      (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
        nativeReader n theta derivative q.p q.F 0)*(-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 force*jointResolvent q.p q.F q.w 0)))*physicalTime q.p q.F age 0+
    (physicalTime (q.p+q.k) q.F (-age) 0*jointResolvent (q.p+q.k) q.F q.z 0*
      nativeReader n theta derivative q.p q.F 0*jointResolvent q.p q.F q.w 0)*timeSlope force q.p q.F age

 theorem nativePreparedFive_generated (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>nativePreparedKernel q n theta derivative (r • force) age)
      (nativePreparedFive q n theta derivative force age) 0 :=by
  have tl:=physicalTime_direction force (q.p+q.k) q.F (-age)
  have rl:=inverse_direction (q.p+q.k) q.F q.z hz force
  have j:=nativeReader_generated n theta derivative force q.p q.F
  have rr:=inverse_direction q.p q.F q.w hw force
  have tr:=physicalTime_direction force q.p q.F age
  have actual:=((((tl.mul rl).mul j).mul rr).mul tr)
  convert! actual using 1
  simp only [nativePreparedKernel,nativePreparedFive,Pi.mul_apply,zero_smul]

 theorem nativePreparedCurrent_generated (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ) (derivative : Fin 4→ℝ)
    (force : Field289) (age : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    HasDerivAt (fun r : ℝ=>nativePreparedCurrent q n theta derivative (r • force) age)
      (inner ℂ (responseLeft q) (nativePreparedFive q n theta derivative force age (responseRight q))) 0 :=by
  have actual:=paired_derivative (nativePreparedFive_generated q n theta derivative force age hz hw)
    (responseLeft q) (responseRight q)
  convert! actual using 1

 theorem nativePreparedCurrent_initial (q : PhysicalResponsePoint) (n : Fin 9) (theta : ℝ)
    (derivative : Fin 4→ℝ) (h : Field289) :
    nativePreparedCurrent q n theta derivative h 0=
      inner ℂ (responseLeft q) (jointResolvent (q.p+q.k) q.F q.z h
        (nativeReader n theta derivative q.p q.F h (jointResolvent q.p q.F q.w h (responseRight q)))) :=by
  simp only [nativePreparedCurrent,preparedDual,preparedPrimal,independentDual,neg_zero,physicalTime_initial,
    ContinuousLinearMap.comp_apply,one_apply_eq_self]
  rfl

end LowEnergy.PreparationVacuumNativeLocalWard
