import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedVoltageKernel
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedSignalPencil
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedClockMoment
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource GaussCoreHilbert
open PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open PreparationVacuumRawJointFeedback PreparationVacuumJointFieldResponse PreparationVacuumPropagationPencil
open SourcePropagationNoetherTime SourcePropagationMotherEulerKernel SourcePropagationNativeEulerHistory
open CanonicalGradedVariation PreparationVacuumFieldPerturbation
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent rawReader rawInitial dressedEulerObserver
  dressedHistoryInitial dressedHistoryContact dressedHistoryMemory dressedSignalMatrix dressedSignalQuadrature

private theorem operator_memory_continuous (q : PhysicalResponsePoint) (reader field : Field289) :
    Continuous (fun ts : ℝ×ℝ=>noetherMemoryMap q reader ts.1 ts.2 field) := by
  have left : Continuous (SourceFiniteUnitary.time (jointGenerator (q.p+q.k) q.F 0 0)) := time_continuous _
  have right : Continuous (SourceFiniteUnitary.time (jointGenerator q.p q.F 0 0)) := time_continuous _
  change Continuous (fun ts : ℝ×ℝ=>
    (1*(SourceFiniteUnitary.time (jointGenerator (q.p+q.k) q.F 0 0) (-ts.2)*
      (-((-Complex.I) • jointCurrent (q.p+q.k) q.F 0 0 field))*
        SourceFiniteUnitary.time (jointGenerator (q.p+q.k) q.F 0 0) ts.2))*
      (SourceFiniteUnitary.time (jointGenerator (q.p+q.k) q.F 0 0) (-ts.1)*rawInitial q reader*
        SourceFiniteUnitary.time (jointGenerator q.p q.F 0 0) ts.1)+
    ((SourceFiniteUnitary.time (jointGenerator (q.p+q.k) q.F 0 0) (-ts.1)*rawInitial q reader*
      SourceFiniteUnitary.time (jointGenerator q.p q.F 0 0) ts.1)*
      (SourceFiniteUnitary.time (jointGenerator q.p q.F 0 0) (-ts.2)*
        ((-Complex.I) • jointCurrent q.p q.F 0 0 field)*
          SourceFiniteUnitary.time (jointGenerator q.p q.F 0 0) ts.2))*1)
  exact ((continuous_const.mul (((left.comp continuous_snd.neg).mul continuous_const).mul
    (left.comp continuous_snd))).mul (((left.comp continuous_fst.neg).mul continuous_const).mul
      (right.comp continuous_fst))).add
    ((((left.comp continuous_fst.neg).mul continuous_const).mul (right.comp continuous_fst)).mul
      (((right.comp continuous_snd.neg).mul continuous_const).mul (right.comp continuous_snd)) |>.mul continuous_const)

theorem dressed_history_memory_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : Continuous (fun ts : ℝ×ℝ=>dressedHistoryMemory event transfer ts.1 ts.2 (fieldUnit j) i) := by
  simpa only [dressedHistoryMemory,ContinuousLinearMap.pi_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars',Function.comp_def] using
    (dressedEulerObserver event).continuous.comp
      (operator_memory_continuous (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j))

private theorem source_real_basis (p : Fin 4→ℂ) (t : ℝ) (j : Fin 289) :
    (nativeTimeSignal (sourceRealSignal p (Pi.single j 1)) t).value=
      (Complex.exp ((t:ℂ)*p 0)).re • fieldUnit j := by
  rw [show (nativeTimeSignal (sourceRealSignal p (Pi.single j 1)) t).value=
      sourceHistoryInput p t (Pi.single j 1) by rw [sourceHistoryInput_actual];rfl]
  funext i
  rw [sourceHistoryInput_actual,sourceTimeHistory_actual]
  simp [fieldUnit,Pi.single_apply]
  split_ifs <;> simp

private theorem source_imaginary_basis (p : Fin 4→ℂ) (t : ℝ) (j : Fin 289) :
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature (Pi.single j 1))) t).value=
      (Complex.exp ((t:ℂ)*p 0)).im • fieldUnit j := by
  change nativeTimeHistory (sourceRealSignal p (sourceQuadrature (Pi.single j 1))) t=_
  rw [sourceTimeHistory_actual]
  funext i
  simp [sourceQuadrature,fieldUnit,Pi.single_apply]
  split_ifs <;> simp


private theorem complex_quadrature_return (c A : ℂ) :
    (c.re:ℂ)*A+Complex.I*((c.im:ℂ)*A)=c*A := by
  rw [mul_left_comm Complex.I,←mul_assoc,←add_mul,Complex.re_add_im]

private theorem memory_quadrature_return (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (i j : Fin 289) :
    (∫s in (0:ℝ)..t,(Complex.exp ((s:ℂ)*p 0)).re •
      (dressedHistoryMemory event transfer t s (fieldUnit j) i))+
    Complex.I*(∫s in (0:ℝ)..t,(Complex.exp ((s:ℂ)*p 0)).im •
      (dressedHistoryMemory event transfer t s (fieldUnit j) i))=
      ∫s in (0:ℝ)..t,Complex.exp ((s:ℂ)*p 0)*dressedHistoryMemory event transfer t s (fieldUnit j) i := by
  have memory : Continuous (fun s : ℝ=>dressedHistoryMemory event transfer t s (fieldUnit j) i) :=
    (dressed_history_memory_continuous event transfer i j).comp (continuous_const.prodMk continuous_id)
  have exponential : Continuous (fun s : ℝ=>Complex.exp ((s:ℂ)*p 0)) := by fun_prop
  have real : Continuous (fun s : ℝ=>(Complex.exp ((s:ℂ)*p 0)).re •
      dressedHistoryMemory event transfer t s (fieldUnit j) i) := by
    exact (Complex.continuous_re.comp exponential).smul memory
  have imaginary : Continuous (fun s : ℝ=>(Complex.exp ((s:ℂ)*p 0)).im •
      dressedHistoryMemory event transfer t s (fieldUnit j) i) := by
    exact (Complex.continuous_im.comp exponential).smul memory
  simp only [Complex.real_smul] at real imaginary ⊢
  have weightedImaginary : Continuous (fun s : ℝ=>Complex.I*((Complex.exp ((s:ℂ)*p 0)).im:ℂ)*
      dressedHistoryMemory event transfer t s (fieldUnit j) i) := by
    have coefficient : Continuous (fun s : ℝ=>Complex.I*((Complex.exp ((s:ℂ)*p 0)).im:ℂ)) := by fun_prop
    exact coefficient.mul memory
  rw [←intervalIntegral.integral_const_mul]
  simp only [←mul_assoc]
  rw [←intervalIntegral.integral_add (μ:=volume) (a:=0) (b:=t)
    (f:=fun s=>((Complex.exp ((s:ℂ)*p 0)).re:ℂ)*dressedHistoryMemory event transfer t s (fieldUnit j) i)
    (g:=fun s=>Complex.I*((Complex.exp ((s:ℂ)*p 0)).im:ℂ)*dressedHistoryMemory event transfer t s (fieldUnit j) i)
    (real.intervalIntegrable 0 t) (weightedImaginary.intervalIntegrable 0 t)]
  apply intervalIntegral.integral_congr
  intro s _
  simpa only [mul_assoc] using complex_quadrature_return
    (Complex.exp ((s:ℂ)*p 0)) (dressedHistoryMemory event transfer t s (fieldUnit j) i)

/-- Every actual quantum entry keeps its preparation, local contact and both source memories. -/
theorem dressed_signal_history_matrix (event : DressedEvent) (transfer : PhysicalMomentum)
    (p : Fin 4→ℂ) (t : ℝ) (i j : Fin 289) :
    dressedSignalMatrix event transfer p t i j=
      dressedHistoryInitial event transfer t (fieldUnit j) i+
        Complex.exp ((t:ℂ)*p 0)*dressedHistoryContact event transfer t (fieldUnit j) i+
        ∫s in (0:ℝ)..t,Complex.exp ((s:ℂ)*p 0)*
          dressedHistoryMemory event transfer t s (fieldUnit j) i := by
  have real:=dressed_history_kernel_generated event transfer
    (nativeTimeSignal (sourceRealSignal p (Pi.single j 1)))
    (sourceTimeSignal_continuous p (Pi.single j 1)).1 t i
  have imaginary:=dressed_history_kernel_generated event transfer
    (nativeTimeSignal (sourceRealSignal p (sourceQuadrature (Pi.single j 1))))
    (sourceTimeSignal_continuous p (sourceQuadrature (Pi.single j 1))).1 t i
  simp_rw [source_real_basis] at real
  simp_rw [source_imaginary_basis] at imaginary
  simp only [map_smul,Pi.smul_apply] at real imaginary
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,Complex.one_re,one_smul,Complex.one_im,
    zero_smul,zero_add] at real imaginary
  rw [dressedSignalMatrix,dressed_signal_complex_original,dressed_signal_quadrature_actual]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [real,imaginary]
  have localContact:=complex_quadrature_return (Complex.exp ((t:ℂ)*p 0))
    (dressedHistoryContact event transfer t (fieldUnit j) i)
  have memory:=memory_quadrature_return event transfer p t i j
  simp only [Complex.real_smul] at localContact memory ⊢
  linear_combination localContact+memory


private theorem original_outer_continuous (q : PhysicalResponsePoint) (A : SourceOp) :
    Continuous (fun t : ℝ=>physicalTime (q.p+q.k) q.F (-t) 0*A*physicalTime q.p q.F t 0) := by
  exact (((time_continuous _).comp continuous_neg).mul continuous_const).mul (time_continuous _)

theorem dressed_history_initial_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : Continuous (fun t : ℝ=>dressedHistoryInitial event transfer t (fieldUnit j) i) := by
  simpa only [dressedHistoryInitial,noetherInitialMap,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.mulLeftRight_apply,Function.comp_def] using
      (dressedEulerObserver event).continuous.comp
        (original_outer_continuous (dressedKinematicPoint event transfer)
          (sourceMaterialMap (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j)))

theorem dressed_history_contact_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : Continuous (fun t : ℝ=>dressedHistoryContact event transfer t (fieldUnit j) i) := by
  simpa only [dressedHistoryContact,noetherContactMap,ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.mulLeftRight_apply,Function.comp_def] using
      (dressedEulerObserver event).continuous.comp
        (original_outer_continuous (dressedKinematicPoint event transfer)
          (sourceContactMap (dressedKinematicPoint event transfer) (fieldUnit i) (fieldUnit j)))

end LowEnergy.GaussComposite.ActualDressedClockMoment
