import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourcePreparedSignalEuler

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentSignalOperator
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback PreparationVacuumRawJointFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil PreparationVacuumSourcePreparedResponse
open PreparationVacuumCurrentSignalRealization PreparationVacuumGaugeSourceInjection
open PreparationVacuumNoetherChart PreparationVacuumOriginalDensity
open PreparationVacuumActionFieldLift
open SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime SourcePropagationMotherEulerKernel
open SourceFiniteUnitary PreparationVacuumFieldPerturbation
open Filter MeasureTheory
open scoped Topology BigOperators ContDiff Interval
abbrev SignalAmplitude:=Fin 289→ℂ
abbrev SourceOp:=PreparationVacuumPropagationPencil.Op
local instance : NormedAlgebra ℝ SourceOp:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader noetherReader
  physicalTime sourceRead rawInitial rawReaderContact noetherReaderContact

private def realAmplitude : SignalAmplitude→L[ℝ] Field289:=
  ContinuousLinearMap.pi (fun i=>Complex.reCLM.comp (ContinuousLinearMap.proj i))

def sourceHistoryInput (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] Field289:=
  realAmplitude.comp (Complex.exp ((t : ℂ)*p 0) • ContinuousLinearMap.id ℝ SignalAmplitude)

theorem sourceHistoryInput_actual (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourceHistoryInput p t a=nativeTimeHistory (sourceRealSignal p a) t :=by
  funext i
  simp only [sourceHistoryInput,realAmplitude,ContinuousLinearMap.comp_apply,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply,Complex.reCLM_apply,smul_apply,ContinuousLinearMap.id_apply,
    Pi.smul_apply,smul_eq_mul,sourceTimeHistory_actual]

theorem sourceHistoryInput_continuous (p : Fin 4→ℂ) : Continuous (sourceHistoryInput p) :=by
  have weight : Continuous (fun t : ℝ=>Complex.exp ((t : ℂ)*p 0)):=by fun_prop
  exact continuous_const.clm_comp (weight.smul continuous_const)

def sourceRightDrive (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (s : ℝ) : SignalAmplitude→L[ℝ] SourceOp:=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp
    (time (jointGenerator q.p q.F 0 0) (-s)) (time (jointGenerator q.p q.F 0 0) s)).comp
      (((-Complex.I) • jointCurrent q.p q.F 0 0).comp (sourceHistoryInput p s))

def sourceLeftDrive (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (s : ℝ) : SignalAmplitude→L[ℝ] SourceOp:=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp
    (time (jointGenerator (q.p+q.k) q.F 0 0) (-s)) (time (jointGenerator (q.p+q.k) q.F 0 0) s)).comp
      ((-((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0)).comp (sourceHistoryInput p s))

theorem sourceRightDrive_continuous (q : PhysicalResponsePoint) (p : Fin 4→ℂ) :
    Continuous (sourceRightDrive q p) :=by
  have transport : Continuous (fun s : ℝ=>ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (time (jointGenerator q.p q.F 0 0) (-s)) (time (jointGenerator q.p q.F 0 0) s)):=
    ((ContinuousLinearMap.mulLeftRight ℝ SourceOp).continuous.comp
      ((time_continuous _).comp continuous_neg)).clm_apply (time_continuous _)
  exact transport.clm_comp (continuous_const.clm_comp (sourceHistoryInput_continuous p))

theorem sourceLeftDrive_continuous (q : PhysicalResponsePoint) (p : Fin 4→ℂ) :
    Continuous (sourceLeftDrive q p) :=by
  have transport : Continuous (fun s : ℝ=>ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (time (jointGenerator (q.p+q.k) q.F 0 0) (-s)) (time (jointGenerator (q.p+q.k) q.F 0 0) s)):=
    ((ContinuousLinearMap.mulLeftRight ℝ SourceOp).continuous.comp
      ((time_continuous _).comp continuous_neg)).clm_apply (time_continuous _)
  exact transport.clm_comp (continuous_const.clm_comp (sourceHistoryInput_continuous p))

def sourcePrimalOperator (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] SourceOp:=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp (time (jointGenerator q.p q.F 0 0) t) 1).comp
    (∫s in (0 : ℝ)..t,sourceRightDrive q p s)

def sourceIndependentDualOperator (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) : SignalAmplitude→L[ℝ] SourceOp:=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp 1 (time (jointGenerator (q.p+q.k) q.F 0 0) (-t))).comp
    (∫s in (0 : ℝ)..t,sourceLeftDrive q p s)

theorem sourcePrimalOperator_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourcePrimalOperator q p t a=orderedPrimal q (nativeTimeHistory (sourceRealSignal p a)) t :=by
  rw [sourcePrimalOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.intervalIntegral_apply ((sourceRightDrive_continuous q p).intervalIntegrable 0 t)]
  simp only [sourceRightDrive,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mulLeftRight_apply,
    smul_apply,mul_one,sourceHistoryInput_actual]
  rfl

theorem sourceIndependentDualOperator_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ)
    (t : ℝ) (a : SignalAmplitude) :
    sourceIndependentDualOperator q p t a=orderedDual q (nativeTimeHistory (sourceRealSignal p a)) t :=by
  rw [sourceIndependentDualOperator,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.intervalIntegral_apply ((sourceLeftDrive_continuous q p).intervalIntegrable 0 t)]
  simp only [sourceLeftDrive,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mulLeftRight_apply,
    smul_apply,neg_apply,one_mul,sourceHistoryInput_actual]
  rfl

def sourceMiddleOperator (q : PhysicalResponsePoint) (reader : Field289) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] SourceOp:=
  let L:=jointResolvent (q.p+q.k) q.F q.z 0
  let R:=jointResolvent q.p q.F q.w 0
  let J:=rawReader reader q.p q.F 0
  ((ContinuousLinearMap.mulLeftRight ℝ SourceOp (-L) (L*J*R)).comp
    (jointCurrent (q.p+q.k) q.F q.z 0)).comp (sourceHistoryInput p 0)+
  ((ContinuousLinearMap.mulLeftRight ℝ SourceOp L R).comp
    (fderiv ℝ (noetherReader reader q.p q.F) 0)).comp (sourceHistoryInput p t)+
  ((ContinuousLinearMap.mulLeftRight ℝ SourceOp (L*J*R) (-R)).comp
    (jointCurrent q.p q.F q.w 0)).comp (sourceHistoryInput p 0)

private theorem middle_algebra {A : Type*} [Ring A] (L R J CL CR old next : A) :
    (-L)*CL*(L*J*R)+L*next*R+(L*J*R)*CR*(-R)=
      ((-(L*CL*L))*J*R+L*old*R+L*J*(-(R*CR*R)))+L*(next-old)*R :=by
  noncomm_ring

private theorem sourceMiddleOperator_actual (q : PhysicalResponsePoint) (reader : Field289)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourceMiddleOperator q reader p t a=
      historyMiddle q reader (nativeTimeHistory (sourceRealSignal p a)) t+
        jointResolvent (q.p+q.k) q.F q.z 0*
          (noetherReaderContact reader (nativeTimeHistory (sourceRealSignal p a) t) q.p q.F-
            rawReaderContact reader (nativeTimeHistory (sourceRealSignal p a) t) q.p q.F)*
              jointResolvent q.p q.F q.w 0 :=by
  simp only [sourceMiddleOperator,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,sourceHistoryInput_actual]
  rw [noetherReaderContact]
  unfold historyMiddle
  exact middle_algebra _ _ _ _ _ _ _

def sourceHistoryOperator (q : PhysicalResponsePoint) (reader : Field289) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] SourceOp:=
  let L:=physicalTime (q.p+q.k) q.F (-t) 0
  let R:=physicalTime q.p q.F t 0
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp 1 (rawInitial q reader*R)).comp
      (sourceIndependentDualOperator q p t)+
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp L R).comp (sourceMiddleOperator q reader p t)+
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp (L*rawInitial q reader) 1).comp
      (sourcePrimalOperator q p t)

private theorem history_algebra {A : Type*} [Ring A] (D L R J P M C : A) :
    D*(J*R)+L*(M+C)*R+(L*J)*P=
      (D*J*R+L*M*R+L*J*P)+L*C*R :=by
  noncomm_ring

theorem sourceHistoryOperator_actual (q : PhysicalResponsePoint) (reader : Field289)
    (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourceHistoryOperator q reader p t a=
      (noetherHistoryOperatorJet q reader (nativeTimeSignal (sourceRealSignal p a)) t).value :=by
  rw [noetherHistoryOperatorJet_value]
  simp only [nativeTimeSignal]
  simp only [sourceHistoryOperator,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,one_mul,mul_one,sourcePrimalOperator_actual,
    sourceIndependentDualOperator_actual,sourceMiddleOperator_actual]
  unfold historyOperator
  exact history_algebra _ _ _ _ _ _ _

def sourceCurrentOperator (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) :
    SignalAmplitude→L[ℝ] (Fin 289→ℂ):=
  ContinuousLinearMap.pi (fun i=>
    (-((sourceRead q).restrictScalars ℝ)).comp (sourceHistoryOperator q (fieldUnit i) p t))

theorem sourceCurrentOperator_actual (q : PhysicalResponsePoint) (p : Fin 4→ℂ) (t : ℝ) (a : SignalAmplitude) :
    sourceCurrentOperator q p t a=
      fun i=>(noetherHistorySourceJet q (nativeTimeSignal (sourceRealSignal p a)) t i).value :=by
  funext i
  rw [sourceCurrentOperator,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    neg_apply]
  change -(sourceRead q (sourceHistoryOperator q (fieldUnit i) p t a))=_
  rw [sourceHistoryOperator_actual]
  simp only [sourceRead,noetherHistorySourceJet,negativeJet,pairJet,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,innerSL_apply_apply]

end LowEnergy.PreparationVacuumCurrentSignalOperator
