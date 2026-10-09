import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalTensor

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedHistoryKernel
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection PreparationVacuumNoetherChart
open PreparationVacuumCurrentSignalOperator
open SourceFiniteUnitary SourcePropagationTimeDependentFeedback SourcePropagationNoetherTime
open CanonicalGradedVariation PreparationVacuumFieldPerturbation
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent noetherReader rawReader rawReaderContact
  physicalTime rawInitial dressedEulerObserver dressedNoetherJet noetherHistoryOperatorJet

private def historyRightDrive (q : PhysicalResponsePoint) (s : ℝ) : Field289→L[ℝ] SourceOp :=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp
    (time (jointGenerator q.p q.F 0 0) (-s)) (time (jointGenerator q.p q.F 0 0) s)).comp
      ((-Complex.I) • jointCurrent q.p q.F 0 0)

private def historyLeftDrive (q : PhysicalResponsePoint) (s : ℝ) : Field289→L[ℝ] SourceOp :=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp
    (time (jointGenerator (q.p+q.k) q.F 0 0) (-s)) (time (jointGenerator (q.p+q.k) q.F 0 0) s)).comp
      (-((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0))

private theorem history_right_continuous (q : PhysicalResponsePoint) : Continuous (historyRightDrive q) := by
  have transport : Continuous (fun s : ℝ=>ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (time (jointGenerator q.p q.F 0 0) (-s)) (time (jointGenerator q.p q.F 0 0) s)) :=
    ((ContinuousLinearMap.mulLeftRight ℝ SourceOp).continuous.comp
      ((time_continuous _).comp continuous_neg)).clm_apply (time_continuous _)
  exact transport.clm_comp continuous_const

private theorem history_left_continuous (q : PhysicalResponsePoint) : Continuous (historyLeftDrive q) := by
  have transport : Continuous (fun s : ℝ=>ContinuousLinearMap.mulLeftRight ℝ SourceOp
      (time (jointGenerator (q.p+q.k) q.F 0 0) (-s)) (time (jointGenerator (q.p+q.k) q.F 0 0) s)) :=
    ((ContinuousLinearMap.mulLeftRight ℝ SourceOp).continuous.comp
      ((time_continuous _).comp continuous_neg)).clm_apply (time_continuous _)
  exact transport.clm_comp continuous_const

private theorem ordered_primal_history (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) :
    orderedPrimal q history t=physicalTime q.p q.F t 0*
      (∫s in (0:ℝ)..t,historyRightDrive q s (history s)) := by
  simp only [historyRightDrive,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mulLeftRight_apply,
    smul_apply,physicalTime]
  rfl

private theorem ordered_dual_history (q : PhysicalResponsePoint) (history : ℝ→Field289) (t : ℝ) :
    orderedDual q history t=(∫s in (0:ℝ)..t,historyLeftDrive q s (history s))*
      physicalTime (q.p+q.k) q.F (-t) 0 := by
  simp only [historyLeftDrive,ContinuousLinearMap.comp_apply,ContinuousLinearMap.mulLeftRight_apply,
    neg_apply,smul_apply,physicalTime]
  rfl

def noetherInitialMap (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) : Field289→L[ℝ] SourceOp :=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp (physicalTime (q.p+q.k) q.F (-t) 0)
    (physicalTime q.p q.F t 0)).comp (sourceMaterialMap q reader)

def noetherContactMap (q : PhysicalResponsePoint) (reader : Field289) (t : ℝ) : Field289→L[ℝ] SourceOp :=
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp (physicalTime (q.p+q.k) q.F (-t) 0)
    (physicalTime q.p q.F t 0)).comp (sourceContactMap q reader)

/-- The two independent time legs retain their original multiplication order. -/
def noetherMemoryMap (q : PhysicalResponsePoint) (reader : Field289) (t s : ℝ) : Field289→L[ℝ] SourceOp :=
  let C:=physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*physicalTime q.p q.F t 0
  (ContinuousLinearMap.mulLeftRight ℝ SourceOp 1 C).comp (historyLeftDrive q s)+
    (ContinuousLinearMap.mulLeftRight ℝ SourceOp C 1).comp (historyRightDrive q s)

private theorem middle_algebra {A : Type*} [Ring A] (L R J CL CR old next : A) :
    ((-(L*CL*L))*J*R+L*old*R+L*J*(-(R*CR*R)))+L*(next-old)*R=
      (-L)*CL*(L*J*R)+(L*J*R)*CR*(-R)+L*next*R := by
  noncomm_ring

private theorem noether_middle_maps (q : PhysicalResponsePoint) (reader : Field289)
    (history : ℝ→Field289) (t : ℝ) :
    historyMiddle q reader history t+
      jointResolvent (q.p+q.k) q.F q.z 0*
        (noetherReaderContact reader (history t) q.p q.F-rawReaderContact reader (history t) q.p q.F)*
          jointResolvent q.p q.F q.w 0=
      sourceMaterialMap q reader (history 0)+sourceContactMap q reader (history t) := by
  simp only [historyMiddle,sourceMaterialMap,sourceContactMap,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,noetherReaderContact]
  exact middle_algebra (A := SourceOp) _ _ _ _ _ _ _

private theorem memory_continuous (q : PhysicalResponsePoint) (reader : Field289)
    (history : ℝ→Field289) (continuousHistory : Continuous history) (t : ℝ) :
    Continuous (fun s=>noetherMemoryMap q reader t s (history s)) := by
  unfold noetherMemoryMap
  exact ((continuous_const.clm_comp (history_left_continuous q)).clm_apply continuousHistory).add
    ((continuous_const.clm_comp (history_right_continuous q)).clm_apply continuousHistory)

private theorem parts_algebra {A : Type*} [Ring A]
    (TL TR J DL PR M C initial contact : A) (paid : M+C=initial+contact) :
    (DL*J*TR+TL*M*TR+TL*J*PR)+TL*C*TR=
      TL*initial*TR+TL*contact*TR+DL*J*TR+TL*J*PR := by
  calc
    _=TL*(M+C)*TR+DL*J*TR+TL*J*PR := by noncomm_ring
    _=_ := by rw [paid];noncomm_ring

private theorem noether_kernel_parts (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      noetherInitialMap q reader t (signal 0).value+noetherContactMap q reader t (signal t).value+
      orderedDual q (fun s=>(signal s).value) t*rawInitial q reader*physicalTime q.p q.F t 0+
      physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*orderedPrimal q (fun s=>(signal s).value) t := by
  have generated:=noetherHistoryOperatorJet_value q reader signal t
  have original:=parts_algebra (A := SourceOp)
    (physicalTime (q.p+q.k) q.F (-t) 0) (physicalTime q.p q.F t 0) (rawInitial q reader)
    (orderedDual q (fun s=>(signal s).value) t) (orderedPrimal q (fun s=>(signal s).value) t)
    (historyMiddle q reader (fun s=>(signal s).value) t)
    (jointResolvent (q.p+q.k) q.F q.z 0*
      (noetherReaderContact reader (signal t).value q.p q.F-rawReaderContact reader (signal t).value q.p q.F)*
        jointResolvent q.p q.F q.w 0)
    (sourceMaterialMap q reader (signal 0).value) (sourceContactMap q reader (signal t).value)
    (noether_middle_maps q reader (fun s=>(signal s).value) t)
  apply generated.trans
  simpa only [historyOperator,noetherInitialMap,noetherContactMap,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,mul_assoc] using! original

private theorem memory_integral_return {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (C : A) (left right : ℝ→A) (continuousLeft : Continuous left)
    (continuousRight : Continuous right) (t : ℝ) :
    (∫s in (0:ℝ)..t,left s*C+C*right s)=(∫s in (0:ℝ)..t,left s)*C+C*(∫s in (0:ℝ)..t,right s) := by
  have leftIntegral : IntervalIntegrable left volume 0 t:=continuousLeft.intervalIntegrable 0 t
  have rightIntegral : IntervalIntegrable right volume 0 t:=continuousRight.intervalIntegrable 0 t
  have leftRead:=(ContinuousLinearMap.mulLeftRight ℝ A 1 C).intervalIntegral_comp_comm leftIntegral
  have rightRead:=(ContinuousLinearMap.mulLeftRight ℝ A C 1).intervalIntegral_comp_comm rightIntegral
  simp only [ContinuousLinearMap.mulLeftRight_apply,one_mul,mul_one] at leftRead rightRead
  have sum : (∫s in (0:ℝ)..t,left s*C+C*right s)=
      (∫s in (0:ℝ)..t,left s*C)+(∫s in (0:ℝ)..t,C*right s) :=
    intervalIntegral.integral_add (μ:=volume) (a:=0) (b:=t)
      (f:=fun s=>left s*C) (g:=fun s=>C*right s)
      ((continuousLeft.mul continuous_const).intervalIntegrable 0 t)
      ((continuous_const.mul continuousRight).intervalIntegrable 0 t)
  exact sum.trans (congrArg₂ (fun x y : A=>x+y) leftRead rightRead)

private theorem noether_memory_integral (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value)) (t : ℝ) :
    (∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value)=
      (∫s in (0:ℝ)..t,historyLeftDrive q s (signal s).value)*
        (physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*physicalTime q.p q.F t 0)+
      (physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*physicalTime q.p q.F t 0)*
        (∫s in (0:ℝ)..t,historyRightDrive q s (signal s).value) := by
  simpa only [noetherMemoryMap,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mulLeftRight_apply,one_mul,mul_one] using!
    memory_integral_return (A := SourceOp)
      (physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*physicalTime q.p q.F t 0)
      (fun s=>historyLeftDrive q s (signal s).value) (fun s=>historyRightDrive q s (signal s).value)
      ((history_left_continuous q).clm_apply continuousSignal)
      ((history_right_continuous q).clm_apply continuousSignal) t

private theorem ordered_parts_algebra {A : Type*} [Ring A]
    (initial contact D P TL J TR : A) :
    initial+contact+(D*TL)*J*TR+TL*J*(TR*P)=
      initial+contact+(D*(TL*J*TR)+(TL*J*TR)*P) := by
  noncomm_ring

/-- The complete Noether response is generated for every original continuous real history. -/
theorem noether_history_kernel (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value)) (t : ℝ) :
    (noetherHistoryOperatorJet q reader signal t).value=
      noetherInitialMap q reader t (signal 0).value+noetherContactMap q reader t (signal t).value+
        ∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value := by
  have parts:=noether_kernel_parts q reader signal t
  have memory:=noether_memory_integral q reader signal continuousSignal t
  have legs := congrArg₂
    (fun dual primal : SourceOp =>
      noetherInitialMap q reader t (signal 0).value+noetherContactMap q reader t (signal t).value+
        dual*rawInitial q reader*physicalTime q.p q.F t 0+
        physicalTime (q.p+q.k) q.F (-t) 0*rawInitial q reader*primal)
    (ordered_dual_history q (fun s=>(signal s).value) t)
    (ordered_primal_history q (fun s=>(signal s).value) t)
  have ordered := ordered_parts_algebra (A := SourceOp)
    (noetherInitialMap q reader t (signal 0).value) (noetherContactMap q reader t (signal t).value)
    (∫s in (0:ℝ)..t,historyLeftDrive q s (signal s).value)
    (∫s in (0:ℝ)..t,historyRightDrive q s (signal s).value)
    (physicalTime (q.p+q.k) q.F (-t) 0) (rawInitial q reader) (physicalTime q.p q.F t 0)
  exact parts.trans (legs.trans (ordered.trans
    (congrArg (fun z : SourceOp=>noetherInitialMap q reader t (signal 0).value+
      noetherContactMap q reader t (signal t).value+z) memory.symm)))

private theorem observed_history_kernel (q : PhysicalResponsePoint) (reader : Field289)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value))
    (observer : SourceOp→L[ℂ]ℂ) (t : ℝ) :
    observer (noetherHistoryOperatorJet q reader signal t).value=
      observer (noetherInitialMap q reader t (signal 0).value)+
        observer (noetherContactMap q reader t (signal t).value)+
        ∫s in (0:ℝ)..t,observer (noetherMemoryMap q reader t s (signal s).value) := by
  have generated := congrArg (fun x : SourceOp => observer x)
    (noether_history_kernel q reader signal continuousSignal t)
  have distribute :
      observer (noetherInitialMap q reader t (signal 0).value+
        noetherContactMap q reader t (signal t).value+
        ∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value)=
      observer (noetherInitialMap q reader t (signal 0).value)+
        observer (noetherContactMap q reader t (signal t).value)+
        observer (∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value) := by
    exact (map_add observer _ _).trans
      (congrArg (fun z : ℂ => z+observer (∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value))
        (map_add observer _ _))
  have integrable : IntervalIntegrable
      (fun s=>noetherMemoryMap q reader t s (signal s).value) volume 0 t :=
    (memory_continuous q reader _ continuousSignal t).intervalIntegrable 0 t
  have original:=(observer.restrictScalars ℝ).intervalIntegral_comp_comm integrable
  have actual : observer (∫s in (0:ℝ)..t,noetherMemoryMap q reader t s (signal s).value)=
      ∫s in (0:ℝ)..t,observer (noetherMemoryMap q reader t s (signal s).value) := by
    simpa only [ContinuousLinearMap.coe_restrictScalars'] using original.symm
  exact generated.trans (distribute.trans
    (congrArg (fun z : ℂ=>observer (noetherInitialMap q reader t (signal 0).value)+
      observer (noetherContactMap q reader t (signal t).value)+z) actual))

def dressedHistoryInitial (event : DressedEvent) (transfer : PhysicalMomentum) (t : ℝ) :
    Field289→L[ℝ](Fin 289→ℂ) :=
  ContinuousLinearMap.pi (fun i=>((dressedEulerObserver event).restrictScalars ℝ).comp
    (noetherInitialMap (dressedKinematicPoint event transfer) (fieldUnit i) t))

def dressedHistoryContact (event : DressedEvent) (transfer : PhysicalMomentum) (t : ℝ) :
    Field289→L[ℝ](Fin 289→ℂ) :=
  ContinuousLinearMap.pi (fun i=>((dressedEulerObserver event).restrictScalars ℝ).comp
    (noetherContactMap (dressedKinematicPoint event transfer) (fieldUnit i) t))

def dressedHistoryMemory (event : DressedEvent) (transfer : PhysicalMomentum) (t s : ℝ) :
    Field289→L[ℝ](Fin 289→ℂ) :=
  ContinuousLinearMap.pi (fun i=>((dressedEulerObserver event).restrictScalars ℝ).comp
    (noetherMemoryMap (dressedKinematicPoint event transfer) (fieldUnit i) t s))

theorem dressed_history_kernel_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (signal : ℝ→SourceJet Field289) (continuousSignal : Continuous (fun t=>(signal t).value))
    (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event transfer signal t i).value=
      dressedHistoryInitial event transfer t (signal 0).value i+
        dressedHistoryContact event transfer t (signal t).value i+
        ∫s in (0:ℝ)..t,dressedHistoryMemory event transfer t s (signal s).value i := by
  rw [dressed_noether_jet_original]
  simpa only [dressedHistoryInitial,dressedHistoryContact,dressedHistoryMemory,
    ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars'] using
    observed_history_kernel (dressedKinematicPoint event transfer) (fieldUnit i) signal continuousSignal
      (dressedEulerObserver event) t

end LowEnergy.GaussComposite.ActualDressedHistoryKernel
