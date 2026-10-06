import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualPreparedHistoryVariation

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourcePropagationNativeEulerHistory
open PreparationVacuumMixedFieldReturn PreparationVacuumJointFieldResponse
open PreparationVacuumRawJointFeedback PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil PreparationVacuumNoetherChart SourcePropagationNoetherTime
open SourcePropagationTimeDependentFeedback SourcePropagationNativeActionHessian
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFieldConstraintResponse
open PreparationVacuumGaugeSourceInjection GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumActionFieldLift
open Filter MeasureTheory
open scoped Topology ContDiff BigOperators Matrix
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] historyPrimal historyDual sourceHistoryWindow
  jointResolvent jointCurrent noetherReader noetherReaderContact rawReader rawReaderContact physicalTime sourceRead
  originalJacobi originalRowLift sourceCompatibility originalReader36 nativeHessian

/-- Both time legs use their source-generated common positive history interval. -/
def preparedHistoryDuration (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) : ℝ :=
  min (sourceHistoryWindow q.p q.F history smooth).duration
    (sourceHistoryWindow (q.p+q.k) q.F history smooth).duration

theorem preparedHistoryDuration_positive (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) : 0<preparedHistoryDuration q history smooth :=
  lt_min (sourceHistoryWindow q.p q.F history smooth).duration_positive
    (sourceHistoryWindow (q.p+q.k) q.F history smooth).duration_positive

/-- Material resolvents vary at preparation; the fixed-pi reader varies at the observation time. -/
def actualPreparedHistoryKernel (q : PhysicalResponsePoint) (reader : Field289) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) (amplitude t : ℝ) : Op :=
  historyDual (q.p+q.k) q.F history smooth amplitude t*
    jointResolvent (q.p+q.k) q.F q.z (amplitude • history 0)*
      noetherReader reader q.p q.F (amplitude • history t)*
        jointResolvent q.p q.F q.w (amplitude • history 0)*
          historyPrimal q.p q.F history smooth amplitude t

private theorem five_derivative {R : Type*} [Ring R] (a b c d e da db dc dd de : R) :
    (((da*b+a*db)*c+a*b*dc)*d+a*b*c*dd)*e+a*b*c*d*de=
      da*b*c*d*e+a*db*c*d*e+a*b*dc*d*e+a*b*c*dd*e+a*b*c*d*de := by
  simp only [add_mul]

private theorem five_noether_value (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    orderedDual q (fun s=>(signal s).value) t*
      jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
        jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0+
    physicalTime (q.p+q.k) q.F (-t) 0*
      (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 (signal 0).value*
        jointResolvent (q.p+q.k) q.F q.z 0))*rawReader reader q.p q.F 0*
          jointResolvent q.p q.F q.w 0*physicalTime q.p q.F t 0+
    physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*
      noetherReaderContact reader (signal t).value q.p q.F*jointResolvent q.p q.F q.w 0*
        physicalTime q.p q.F t 0+
    physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
      (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 (signal 0).value*
        jointResolvent q.p q.F q.w 0))*physicalTime q.p q.F t 0+
    physicalTime (q.p+q.k) q.F (-t) 0*jointResolvent (q.p+q.k) q.F q.z 0*rawReader reader q.p q.F 0*
      jointResolvent q.p q.F q.w 0*orderedPrimal q (fun s=>(signal s).value) t=
        (noetherHistoryOperatorJet q reader signal t).value := by
  rw [noetherHistoryOperatorJet_value]
  unfold historyOperator historyMiddle rawInitial
  simp only [mul_add,add_mul,mul_sub,sub_mul,mul_assoc]
  abel

theorem actualPreparedHistoryKernel_generated (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<preparedHistoryDuration q (fun s=>(signal s).value) smooth) :
    HasDerivAt (fun a=>actualPreparedHistoryKernel q reader (fun s=>(signal s).value) smooth a t)
      ((noetherHistoryOperatorJet q reader signal t).value) 0 := by
  have intervals := lt_min_iff.mp inside
  have dual := actualDual_ordered_direction q (fun s=>(signal s).value) smooth t nonnegative intervals.2
  have left := inverse_direction (q.p+q.k) q.F q.z hz (signal 0).value
  have contact := noetherReader_generated reader (signal t).value q.p q.F
  have right := inverse_direction q.p q.F q.w hw (signal 0).value
  have primal := actualPrimal_ordered_direction q (fun s=>(signal s).value) smooth t nonnegative intervals.1
  have generated := (((dual.mul left).mul contact).mul right).mul primal
  have timeInsideR : t∈Set.Ioo (-(sourceHistoryWindow q.p q.F (fun s=>(signal s).value) smooth).duration)
      (sourceHistoryWindow q.p q.F (fun s=>(signal s).value) smooth).duration := by
    constructor
    · linarith [(sourceHistoryWindow q.p q.F (fun s=>(signal s).value) smooth).duration_positive]
    · exact intervals.1
  have timeInsideL : t∈Set.Ioo (-(sourceHistoryWindow (q.p+q.k) q.F (fun s=>(signal s).value) smooth).duration)
      (sourceHistoryWindow (q.p+q.k) q.F (fun s=>(signal s).value) smooth).duration := by
    constructor
    · linarith [(sourceHistoryWindow (q.p+q.k) q.F (fun s=>(signal s).value) smooth).duration_positive]
    · exact intervals.2
  have baseR := historyPrimal_zero q.p q.F (fun s=>(signal s).value) smooth t
    ((sourceHistoryWindow q.p q.F (fun s=>(signal s).value) smooth).time_inside timeInsideR)
  have baseL := historyDual_zero (q.p+q.k) q.F (fun s=>(signal s).value) smooth t
    ((sourceHistoryWindow (q.p+q.k) q.F (fun s=>(signal s).value) smooth).time_inside timeInsideL)
  simp only [Pi.mul_apply,zero_smul,baseR,baseL,noetherReader_source] at generated
  have algebra := five_derivative (R:=Op)
    (physicalTime (q.p+q.k) q.F (-t) 0) (jointResolvent (q.p+q.k) q.F q.z 0)
    (rawReader reader q.p q.F 0) (jointResolvent q.p q.F q.w 0) (physicalTime q.p q.F t 0)
    (orderedDual q (fun s=>(signal s).value) t)
    (-(jointResolvent (q.p+q.k) q.F q.z 0*jointCurrent (q.p+q.k) q.F q.z 0 (signal 0).value*
      jointResolvent (q.p+q.k) q.F q.z 0))
    (noetherReaderContact reader (signal t).value q.p q.F)
    (-(jointResolvent q.p q.F q.w 0*jointCurrent q.p q.F q.w 0 (signal 0).value*jointResolvent q.p q.F q.w 0))
    (orderedPrimal q (fun s=>(signal s).value) t)
  convert! generated.congr_deriv (algebra.trans (five_noether_value q reader signal t)) using 1

def actualPreparedHistorySource (q : PhysicalResponsePoint) (history : ℝ→Field289)
    (smooth : ContDiffAt ℝ 1 history 0) (amplitude t : ℝ) (i : Fin 289) : ℂ :=
  -sourceRead q (actualPreparedHistoryKernel q (fieldUnit i) history smooth amplitude t)

theorem actualPreparedHistorySource_generated (q : PhysicalResponsePoint)
    (signal : ℝ→SourceJet Field289) (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (t : ℝ) (nonnegative : 0≤t)
    (inside : t<preparedHistoryDuration q (fun s=>(signal s).value) smooth) (i : Fin 289) :
    HasDerivAt (fun a=>actualPreparedHistorySource q (fun s=>(signal s).value) smooth a t i)
      (noetherHistorySourceJet q signal t i).value 0 := by
  have generated := ((sourceRead q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (actualPreparedHistoryKernel_generated q (fieldUnit i) signal smooth hz hw t nonnegative inside)
  convert! generated.neg using 1
  unfold noetherHistorySourceJet negativeJet pairJet sourceRead
  rfl

def actualHistoryLinearSource (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (t : ℝ) (i : Fin 289) : ℂ :=
  deriv (fun a=>actualPreparedHistorySource q (fun s=>(signal s).value) smooth a t i) 0

theorem actualHistoryLinearSource_value (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (t : ℝ) (nonnegative : 0≤t) (inside : t<preparedHistoryDuration q (fun s=>(signal s).value) smooth)
    (i : Fin 289) : actualHistoryLinearSource q signal smooth t i=(noetherHistorySourceJet q signal t i).value :=
  (actualPreparedHistorySource_generated q signal smooth hz hw t nonnegative inside i).deriv

theorem actualHistoryLinearSource_time (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (continuousSignal : Continuous (fun s=>(signal s).value)) (paid : ∀s,HasSourceJets signal s)
    (t : ℝ) (positive : 0<t) (inside : t<preparedHistoryDuration q (fun s=>(signal s).value) smooth)
    (i : Fin 289) :
    HasDerivAt (fun s=>actualHistoryLinearSource q signal smooth s i)
      (noetherHistorySourceJet q signal t i).first t := by
  have nearTime : ∀ᶠ s in 𝓝 t, s∈Set.Ioo 0 (preparedHistoryDuration q (fun r=>(signal r).value) smooth) :=
    isOpen_Ioo.mem_nhds ⟨positive,inside⟩
  have values : (fun s=>actualHistoryLinearSource q signal smooth s i)=ᶠ[𝓝 t]
      (fun s=>(noetherHistorySourceJet q signal s i).value) :=
    nearTime.mono (fun s hs=>actualHistoryLinearSource_value q signal smooth hz hw s hs.1.le hs.2 i)
  exact (noetherHistorySourceJet_generated q signal continuousSignal t (paid t) i).1.congr_of_eventuallyEq values

theorem actualHistoryLinearSource_second_time (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (continuousSignal : Continuous (fun s=>(signal s).value)) (paid : ∀s,HasSourceJets signal s)
    (t : ℝ) (positive : 0<t) (inside : t<preparedHistoryDuration q (fun s=>(signal s).value) smooth)
    (i : Fin 289) :
    HasDerivAt (fun s=>deriv (fun r=>actualHistoryLinearSource q signal smooth r i) s)
      (noetherHistorySourceJet q signal t i).second t := by
  have nearTime : ∀ᶠ s in 𝓝 t, s∈Set.Ioo 0 (preparedHistoryDuration q (fun r=>(signal r).value) smooth) :=
    isOpen_Ioo.mem_nhds ⟨positive,inside⟩
  have values : (fun s=>deriv (fun r=>actualHistoryLinearSource q signal smooth r i) s)=ᶠ[𝓝 t]
      (fun s=>(noetherHistorySourceJet q signal s i).first) :=
    nearTime.mono (fun s hs=>(actualHistoryLinearSource_time q signal smooth hz hw continuousSignal paid s hs.1 hs.2 i).deriv)
  exact (noetherHistorySourceJet_generated q signal continuousSignal t (paid t) i).2.congr_of_eventuallyEq values

/-- This forcing integrates the derivative of the generated nonlinear current, with the original Euler sign. -/
def actualHistoryForcing (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (lambda : ℂ) (T : ℝ) : Fin 289→ℂ :=
  fun i=>∫ t in (0 : ℝ)..T,laplaceWeight lambda t*actualHistoryLinearSource q signal smooth t i

theorem actualHistoryForcing_noether (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (fun s=>(signal s).value) smooth) :
    actualHistoryForcing q signal smooth lambda T=noetherForcing q signal lambda T := by
  funext i
  unfold actualHistoryForcing noetherForcing
  apply intervalIntegral.integral_congr
  intro t ht
  have timeBounds : 0≤t ∧ t≤T := by simpa only [Set.uIcc_of_le nonnegative,Set.mem_Icc] using ht
  dsimp only
  rw [actualHistoryLinearSource_value q signal smooth hz hw t timeBounds.1 (lt_of_le_of_lt timeBounds.2 inside)]

def actualHistoryField (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (lambda : physicalSpectralDomain q.k) (T : ℝ) : Fin 289→ℂ :=
  PreparationVacuumOriginalGreenFeedback.sourceField
    ⟨fullMomentum (physicalSpatial q.k) lambda.val,lambda.property⟩ (actualHistoryForcing q signal smooth lambda.val T)

theorem actualHistoryField_noether (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (fun s=>(signal s).value) smooth) :
    actualHistoryField q signal smooth lambda T=noetherField q signal lambda T := by
  unfold actualHistoryField noetherField
  rw [actualHistoryForcing_noether q signal smooth hz hw lambda.val T nonnegative inside]

theorem nativeAction_actualHistoryField (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (fun s=>(signal s).value) smooth) :
    nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      actualHistoryField q signal smooth lambda T=
        actualHistoryForcing q signal smooth lambda.val T-
          originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
              (actualHistoryForcing q signal smooth lambda.val T) := by
  rw [actualHistoryField_noether q signal smooth hz hw lambda T nonnegative inside,
    actualHistoryForcing_noether q signal smooth hz hw lambda.val T nonnegative inside]
  exact nativeAction_noetherField q signal lambda T

theorem nativeAction_actualHistoryField36 (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (lambda : physicalSpectralDomain q.k) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (fun s=>(signal s).value) smooth) :
    originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
      (nativeFourierHessian nativeHessian (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
        actualHistoryField q signal smooth lambda T)=
          originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
            actualHistoryForcing q signal smooth lambda.val T-
              originalReader36 (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                (originalRowLift (fullMomentum (physicalSpatial q.k) lambda.val) *ᵥ
                  sourceCompatibility (fullMomentum (physicalSpatial q.k) lambda.val)
                    (actualHistoryForcing q signal smooth lambda.val T)) := by
  rw [nativeAction_actualHistoryField q signal smooth hz hw lambda T nonnegative inside,Matrix.mulVec_sub]

/-- The actual nonlinear-current derivative feeds the native full-time readback with both cosources retained. -/
theorem actualHistoryForcing_cosources (q : PhysicalResponsePoint) (signal : ℝ→SourceJet Field289)
    (smooth : ContDiffAt ℝ 1 (fun s=>(signal s).value) 0) (hz : q.z.im≠0) (hw : q.w.im≠0)
    (continuousSignal : ContinuousJets signal) (paid : ∀s,HasSourceJets signal s)
    (lambda : ℂ) (T : ℝ) (nonnegative : 0≤T)
    (inside : T<preparedHistoryDuration q (fun s=>(signal s).value) smooth) (row : Fin 289) :
    (originalReadback (fullMomentum (physicalSpatial q.k) lambda) *ᵥ
      actualHistoryForcing q signal smooth lambda T) row=
        (∫ t in (0 : ℝ)..T,laplaceWeight lambda t*noetherTimeSource q signal (physicalSpatial q.k) t row)-
          (noetherBoundary q signal (physicalSpatial q.k) lambda T row-
            noetherBoundary q signal (physicalSpatial q.k) lambda 0 row) := by
  rw [actualHistoryForcing_noether q signal smooth hz hw lambda T nonnegative inside]
  exact noetherForcing_readback q signal continuousSignal paid (physicalSpatial q.k) lambda T row

end LowEnergy.SourcePropagationNativeEulerHistory
