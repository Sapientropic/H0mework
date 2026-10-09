import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedClockKernel

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedClockMoment
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open Filter Set MeasureTheory
open scoped Matrix BigOperators Topology Interval
attribute [local irreducible] dressedHistoryInitial dressedHistoryContact dressedHistoryMemory dressedSignalMatrix

private theorem interval_input_jet (F D : ℂ→ℝ→ℂ)
    (continuousF : Continuous (fun zt : ℂ×ℝ=>F zt.1 zt.2))
    (continuousD : Continuous (fun zt : ℂ×ℝ=>D zt.1 zt.2))
    (generated : ∀z t,HasDerivAt (fun w=>F w t) (D z t) z) (z : ℂ) (a b : ℝ) :
    HasDerivAt (fun w=>∫t in a..b,F w t) (∫t in a..b,D z t) z := by
  obtain ⟨C,bound⟩:=(isCompact_closedBall z 1 |>.prod (isCompact_uIcc : IsCompact (uIcc a b))).exists_bound_of_continuousOn
    continuousD.continuousOn
  have sliceF (w : ℂ) : Continuous (F w) := continuousF.comp (continuous_const.prodMk continuous_id)
  have sliceD : Continuous (D z) := continuousD.comp (continuous_const.prodMk continuous_id)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F:=F) (F':=D) (bound:=fun _=>C) (s:=Metric.ball z 1) (x₀:=z)
    (Metric.ball_mem_nhds z (by norm_num)) (Filter.Eventually.of_forall (fun w=>(sliceF w).aestronglyMeasurable))
    ((sliceF z).intervalIntegrable a b) sliceD.aestronglyMeasurable
    (Filter.Eventually.of_forall ?_) (continuous_const.intervalIntegrable a b)
    (Filter.Eventually.of_forall (fun t _ w _=>generated w t))).2
  intro t member w inside
  exact bound (w,t) ⟨Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp inside)),
    uIoc_subset_uIcc member⟩


/-- This varies the original Fourier input clock while holding the source and observation fixed. -/
def sourceInputClock (z : ℂ) : Fin 4→ℂ := Pi.single 0 z

/-- The initial preparation term has no input-clock derivative. -/
def dressedInputClockKernel (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (t : ℝ) : Matrix (Fin 289) (Fin 289) ℂ := fun i j=>
  (t:ℂ)*Complex.exp ((t:ℂ)*z)*dressedHistoryContact event transfer t (fieldUnit j) i+
    ∫s in (0:ℝ)..t,(s:ℂ)*Complex.exp ((s:ℂ)*z)*
      dressedHistoryMemory event transfer t s (fieldUnit j) i

theorem dressed_input_clock_kernel_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (t : ℝ) (i j : Fin 289) :
    HasDerivAt (fun w=>dressedSignalMatrix event transfer (sourceInputClock w) t i j)
      (dressedInputClockKernel event transfer z t i j) z := by
  have memory : Continuous (fun s : ℝ=>dressedHistoryMemory event transfer t s (fieldUnit j) i) :=
    (dressed_history_memory_continuous event transfer i j).comp (continuous_const.prodMk continuous_id)
  have base : Continuous (fun ws : ℂ×ℝ=>Complex.exp ((ws.2:ℂ)*ws.1)) := by fun_prop
  have number : Continuous (fun ws : ℂ×ℝ=>(ws.2:ℂ)) := by fun_prop
  have kernel : Continuous (fun ws : ℂ×ℝ=>dressedHistoryMemory event transfer t ws.2 (fieldUnit j) i) :=
    memory.comp continuous_snd
  have realMemory : Continuous (fun ws : ℂ×ℝ=>Complex.exp ((ws.2:ℂ)*ws.1)*
      dressedHistoryMemory event transfer t ws.2 (fieldUnit j) i) := base.mul kernel
  have clockMemory : Continuous (fun ws : ℂ×ℝ=>(ws.2:ℂ)*Complex.exp ((ws.2:ℂ)*ws.1)*
      dressedHistoryMemory event transfer t ws.2 (fieldUnit j) i) := (number.mul base).mul kernel
  have timeDerivative (w : ℂ) (s : ℝ) : HasDerivAt (fun v=>Complex.exp ((s:ℂ)*v)*
      dressedHistoryMemory event transfer t s (fieldUnit j) i)
      ((s:ℂ)*Complex.exp ((s:ℂ)*w)*dressedHistoryMemory event transfer t s (fieldUnit j) i) w := by
    simpa only [id_eq,one_mul,mul_comm (s:ℂ)] using!
      ((hasDerivAt_id w).const_mul (s:ℂ)).cexp.mul_const
        (dressedHistoryMemory event transfer t s (fieldUnit j) i)
  have integrated:=interval_input_jet _ _ realMemory clockMemory timeDerivative z 0 t
  have contact : HasDerivAt (fun w=>Complex.exp ((t:ℂ)*w)*dressedHistoryContact event transfer t (fieldUnit j) i)
      ((t:ℂ)*Complex.exp ((t:ℂ)*z)*dressedHistoryContact event transfer t (fieldUnit j) i) z := by
    simpa only [id_eq,one_mul,mul_comm (t:ℂ)] using!
      ((hasDerivAt_id z).const_mul (t:ℂ)).cexp.mul_const
        (dressedHistoryContact event transfer t (fieldUnit j) i)
  have original : (fun w=>dressedSignalMatrix event transfer (sourceInputClock w) t i j)=
      fun w=>dressedHistoryInitial event transfer t (fieldUnit j) i+
        Complex.exp ((t:ℂ)*w)*dressedHistoryContact event transfer t (fieldUnit j) i+
        ∫s in (0:ℝ)..t,Complex.exp ((s:ℂ)*w)*dressedHistoryMemory event transfer t s (fieldUnit j) i := by
    funext w
    simpa only [sourceInputClock,Pi.single_eq_same] using
      dressed_signal_history_matrix event transfer (sourceInputClock w) t i j
  rw [original]
  simpa only [dressedInputClockKernel,zero_add,Pi.add_def] using!
    ((hasDerivAt_const z (dressedHistoryInitial event transfer t (fieldUnit j) i)).add contact).add integrated

private theorem input_clock_memory_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) (moment : Bool) :
    Continuous (fun zt : ℂ×ℝ=>∫s in (0:ℝ)..zt.2,
      (if moment then (s:ℂ) else 1)*Complex.exp ((s:ℂ)*zt.1)*
        dressedHistoryMemory event transfer zt.2 s (fieldUnit j) i) := by
  have number : Continuous (fun zs : (ℂ×ℝ)×ℝ=>if moment then (zs.2:ℂ) else 1) := by
    cases moment <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  have exponential : Continuous (fun zs : (ℂ×ℝ)×ℝ=>Complex.exp ((zs.2:ℂ)*zs.1.1)) := by fun_prop
  have kernel : Continuous (fun zs : (ℂ×ℝ)×ℝ=>dressedHistoryMemory event transfer zs.1.2 zs.2 (fieldUnit j) i) :=
    (dressed_history_memory_continuous event transfer i j).comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((number.mul exponential).mul kernel) continuous_snd

private theorem input_clock_response_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : Continuous (fun zt : ℂ×ℝ=>dressedSignalMatrix event transfer (sourceInputClock zt.1) zt.2 i j) := by
  have initial : Continuous (fun zt : ℂ×ℝ=>dressedHistoryInitial event transfer zt.2 (fieldUnit j) i) :=
    (dressed_history_initial_continuous event transfer i j).comp continuous_snd
  have contact : Continuous (fun zt : ℂ×ℝ=>dressedHistoryContact event transfer zt.2 (fieldUnit j) i) :=
    (dressed_history_contact_continuous event transfer i j).comp continuous_snd
  have exponential : Continuous (fun zt : ℂ×ℝ=>Complex.exp ((zt.2:ℂ)*zt.1)) := by fun_prop
  have memory:=input_clock_memory_continuous event transfer i j false
  simp only [Bool.false_eq_true,if_false,one_mul] at memory
  have generated := (initial.add (exponential.mul contact)).add memory
  convert! generated using 1
  funext zt
  simp only [Pi.add_apply,Pi.mul_apply]
  simpa only [sourceInputClock,Pi.single_eq_same] using
    dressed_signal_history_matrix event transfer (sourceInputClock zt.1) zt.2 i j

private theorem input_clock_jet_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) : Continuous (fun zt : ℂ×ℝ=>dressedInputClockKernel event transfer zt.1 zt.2 i j) := by
  have number : Continuous (fun zt : ℂ×ℝ=>(zt.2:ℂ)) := by fun_prop
  have exponential : Continuous (fun zt : ℂ×ℝ=>Complex.exp ((zt.2:ℂ)*zt.1)) := by fun_prop
  have contact : Continuous (fun zt : ℂ×ℝ=>dressedHistoryContact event transfer zt.2 (fieldUnit j) i) :=
    (dressed_history_contact_continuous event transfer i j).comp continuous_snd
  have memory:=input_clock_memory_continuous event transfer i j true
  simp only [if_true] at memory
  exact ((number.mul exponential).mul contact).add memory

def dressedWindowInputClockJet (event : DressedEvent) (transfer : PhysicalMomentum)
    (z lambda : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j=>∫t in (0:ℝ)..T,laplaceWeight lambda t*dressedInputClockKernel event transfer z t i j

/-- The derivative is generated inside the true finite quantum integral. -/
theorem dressed_window_input_clock_jet_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (z lambda : ℂ) (T : ℝ) :
    HasDerivAt (fun w=>dressedWindowPolarization event transfer (sourceInputClock w) lambda T)
      (dressedWindowInputClockJet event transfer z lambda T) z := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have weight : Continuous (fun zt : ℂ×ℝ=>laplaceWeight lambda zt.2) := by
    unfold laplaceWeight
    fun_prop
  exact interval_input_jet _ _
    (weight.mul (input_clock_response_continuous event transfer i j))
    (weight.mul (input_clock_jet_continuous event transfer i j))
    (fun w t=>(dressed_input_clock_kernel_generated event transfer w t i j).const_mul (laplaceWeight lambda t))
    z 0 T


private theorem voltage_input_clock_pointwise (event : DressedEvent) (t : ℝ) (i : Fin 289) :
    (dressedNoetherJet event 0 (ActualEMCauchyDynamic.voltageNativeTimeJet
      (PreparationVacuumPhysicalFeedback.physicalSpatial 0) false) t i).value=
      dressedSignalMatrix event 0 (sourceInputClock 0) t i 20-
        dressedInputClockKernel event 0 0 t i 8 := by
  have memory20 : Continuous (fun s : ℝ=>dressedHistoryMemory event 0 t s (fieldUnit 20) i) :=
    (dressed_history_memory_continuous event 0 i 20).comp (continuous_const.prodMk continuous_id)
  have memory8 : Continuous (fun s : ℝ=>(s:ℂ)*dressedHistoryMemory event 0 t s (fieldUnit 8) i) := by
    have number : Continuous (fun s : ℝ=>(s:ℂ)) := by fun_prop
    exact number.mul ((dressed_history_memory_continuous event 0 i 8).comp
      (continuous_const.prodMk continuous_id))
  rw [dressed_voltage_origin_real_current,dressed_signal_history_matrix,dressedInputClockKernel]
  simp only [sourceInputClock,Pi.single_eq_same,mul_zero,Complex.exp_zero,one_mul,mul_one,
    map_sub,map_smul,Pi.sub_apply,Pi.smul_apply,Complex.real_smul]
  rw [intervalIntegral.integral_sub (memory20.intervalIntegrable 0 t) (memory8.intervalIntegrable 0 t)]
  abel

/-- The actual zero-transfer voltage reads the quantum tensor and its genuine input-clock jet. -/
theorem dressed_voltage_origin_clock_return (event : DressedEvent) (lambda : ℂ) (T : ℝ) :
    dressedVoltageForcing event 0 lambda T=
      dressedWindowPolarization event 0 (sourceInputClock 0) lambda T*ᵥ(Pi.single 20 1)-
        dressedWindowInputClockJet event 0 0 lambda T*ᵥ(Pi.single 8 1) := by
  funext i
  have response : Continuous (fun t : ℝ=>dressedSignalMatrix event 0 (sourceInputClock 0) t i 20) :=
    (input_clock_response_continuous event 0 i 20).comp (continuous_const.prodMk continuous_id)
  have clock : Continuous (fun t : ℝ=>dressedInputClockKernel event 0 0 t i 8) :=
    (input_clock_jet_continuous event 0 i 8).comp (continuous_const.prodMk continuous_id)
  have weight : Continuous (laplaceWeight lambda) := by unfold laplaceWeight;fun_prop
  simp only [Matrix.mulVec_single_one,Pi.sub_apply,Matrix.col_apply,dressedWindowPolarization,
    dressedWindowInputClockJet,dressedVoltageForcing,dressedNoetherForcing,Pi.add_apply,Pi.smul_apply,
    smul_eq_mul,dressed_voltage_origin_imaginary_current,mul_zero,intervalIntegral.integral_zero,add_zero]
  rw [←intervalIntegral.integral_sub (μ:=volume) (a:=0) (b:=T)
    (f:=fun t=>laplaceWeight lambda t*dressedSignalMatrix event 0 (sourceInputClock 0) t i 20)
    (g:=fun t=>laplaceWeight lambda t*dressedInputClockKernel event 0 0 t i 8)
    ((weight.mul response).intervalIntegrable 0 T) ((weight.mul clock).intervalIntegrable 0 T)]
  apply intervalIntegral.integral_congr
  intro t _
  simpa only [mul_sub] using!
    congrArg (fun c : ℂ=>laplaceWeight lambda t*c) (voltage_input_clock_pointwise event t i)

end LowEnergy.GaussComposite.ActualDressedClockMoment
