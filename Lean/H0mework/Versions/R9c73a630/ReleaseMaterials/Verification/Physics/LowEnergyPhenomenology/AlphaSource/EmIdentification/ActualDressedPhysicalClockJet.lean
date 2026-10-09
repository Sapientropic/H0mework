import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedInputClockJet

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalClock
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open PreparationVacuumActionFieldLift PreparationVacuumGaugeSourceInjection
open PreparationVacuumCurrentSignalOperator PreparationVacuumCurrentSignalRealization
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedSignal ActualDressedPencil ActualDressedHistoryKernel
open ActualDressedClockMoment Filter Set MeasureTheory
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


private theorem original_lag_weight (z : ℂ) (t s : ℝ) :
    laplaceWeight z t*Complex.exp ((s:ℂ)*z)=Complex.exp (((s-t:ℝ):ℂ)*z) := by
  rw [laplaceWeight,←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem coincident_quantum_entry (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (t : ℝ) (i j : Fin 289) :
    laplaceWeight z t*dressedSignalMatrix event transfer (sourceInputClock z) t i j=
      Complex.exp (-(t:ℂ)*z)*dressedHistoryInitial event transfer t (fieldUnit j) i+
        dressedHistoryContact event transfer t (fieldUnit j) i+
        ∫s in (0:ℝ)..t,Complex.exp (((s-t:ℝ):ℂ)*z)*dressedHistoryMemory event transfer t s (fieldUnit j) i := by
  rw [dressed_signal_history_matrix]
  simp only [sourceInputClock,Pi.single_eq_same,mul_add]
  have localWeight : laplaceWeight z t*Complex.exp ((t:ℂ)*z)=1 := by
    rw [original_lag_weight,sub_self,Complex.ofReal_zero,zero_mul,Complex.exp_zero]
  rw [←mul_assoc,localWeight,one_mul,←intervalIntegral.integral_const_mul]
  simp_rw [←mul_assoc,original_lag_weight]
  congr 2
  rw [laplaceWeight]
  congr 2
  ring

/-- Synchronizing the original two clocks retains preparation and retarded time lag. -/
theorem dressed_coincident_polarization_kernel (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) :
    dressedWindowPolarization event transfer (sourceInputClock z) z T=
      fun i j=>∫t in (0:ℝ)..T,
        Complex.exp (-(t:ℂ)*z)*dressedHistoryInitial event transfer t (fieldUnit j) i+
          dressedHistoryContact event transfer t (fieldUnit j) i+
          ∫s in (0:ℝ)..t,Complex.exp (((s-t:ℝ):ℂ)*z)*dressedHistoryMemory event transfer t s (fieldUnit j) i := by
  funext i j
  unfold dressedWindowPolarization
  apply intervalIntegral.integral_congr
  intro t _
  exact coincident_quantum_entry event transfer z t i j

/-- The local contact cancels in the total clock derivative, while both original memories remain. -/
def dressedCoincidentClockJet (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) : Matrix (Fin 289) (Fin 289) ℂ := fun i j=>
  ∫t in (0:ℝ)..T,
    (-(t:ℂ))*Complex.exp (-(t:ℂ)*z)*dressedHistoryInitial event transfer t (fieldUnit j) i+
      ∫s in (0:ℝ)..t,((s-t:ℝ):ℂ)*Complex.exp (((s-t:ℝ):ℂ)*z)*
        dressedHistoryMemory event transfer t s (fieldUnit j) i

private theorem lag_memory_continuous (event : DressedEvent) (transfer : PhysicalMomentum)
    (i j : Fin 289) (moment : Bool) :
    Continuous (fun zt : ℂ×ℝ=>∫s in (0:ℝ)..zt.2,
      (if moment then ((s-zt.2:ℝ):ℂ) else 1)*Complex.exp (((s-zt.2:ℝ):ℂ)*zt.1)*
        dressedHistoryMemory event transfer zt.2 s (fieldUnit j) i) := by
  have number : Continuous (fun zs : (ℂ×ℝ)×ℝ=>if moment then ((zs.2-zs.1.2:ℝ):ℂ) else 1) := by
    cases moment <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  have exponential : Continuous (fun zs : (ℂ×ℝ)×ℝ=>Complex.exp (((zs.2-zs.1.2:ℝ):ℂ)*zs.1.1)) := by fun_prop
  have kernel : Continuous (fun zs : (ℂ×ℝ)×ℝ=>dressedHistoryMemory event transfer zs.1.2 zs.2 (fieldUnit j) i) :=
    (dressed_history_memory_continuous event transfer i j).comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((number.mul exponential).mul kernel) continuous_snd

private theorem lag_entry_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (t : ℝ) (i j : Fin 289) :
    HasDerivAt (fun w=>
      Complex.exp (-(t:ℂ)*w)*dressedHistoryInitial event transfer t (fieldUnit j) i+
        dressedHistoryContact event transfer t (fieldUnit j) i+
        ∫s in (0:ℝ)..t,Complex.exp (((s-t:ℝ):ℂ)*w)*dressedHistoryMemory event transfer t s (fieldUnit j) i)
      ((-(t:ℂ))*Complex.exp (-(t:ℂ)*z)*dressedHistoryInitial event transfer t (fieldUnit j) i+
        ∫s in (0:ℝ)..t,((s-t:ℝ):ℂ)*Complex.exp (((s-t:ℝ):ℂ)*z)*
          dressedHistoryMemory event transfer t s (fieldUnit j) i) z := by
  have memory : Continuous (fun s : ℝ=>dressedHistoryMemory event transfer t s (fieldUnit j) i) :=
    (dressed_history_memory_continuous event transfer i j).comp (continuous_const.prodMk continuous_id)
  have base : Continuous (fun ws : ℂ×ℝ=>Complex.exp (((ws.2-t:ℝ):ℂ)*ws.1)) := by fun_prop
  have number : Continuous (fun ws : ℂ×ℝ=>((ws.2-t:ℝ):ℂ)) := by fun_prop
  have kernel : Continuous (fun ws : ℂ×ℝ=>dressedHistoryMemory event transfer t ws.2 (fieldUnit j) i) :=
    memory.comp continuous_snd
  have timeDerivative (w : ℂ) (s : ℝ) : HasDerivAt
      (fun v=>Complex.exp (((s-t:ℝ):ℂ)*v)*dressedHistoryMemory event transfer t s (fieldUnit j) i)
      (((s-t:ℝ):ℂ)*Complex.exp (((s-t:ℝ):ℂ)*w)*dressedHistoryMemory event transfer t s (fieldUnit j) i) w := by
    simpa only [id_eq,one_mul,mul_comm ((s-t:ℝ):ℂ)] using!
      ((hasDerivAt_id w).const_mul ((s-t:ℝ):ℂ)).cexp.mul_const
        (dressedHistoryMemory event transfer t s (fieldUnit j) i)
  have integrated:=interval_input_jet _ _ (base.mul kernel) ((number.mul base).mul kernel) timeDerivative z 0 t
  have initial : HasDerivAt (fun w=>Complex.exp (-(t:ℂ)*w)*dressedHistoryInitial event transfer t (fieldUnit j) i)
      ((-(t:ℂ))*Complex.exp (-(t:ℂ)*z)*dressedHistoryInitial event transfer t (fieldUnit j) i) z := by
    simpa only [id_eq,one_mul,mul_comm (-(t:ℂ))] using!
      ((hasDerivAt_id z).const_mul (-(t:ℂ))).cexp.mul_const
        (dressedHistoryInitial event transfer t (fieldUnit j) i)
  simpa only [Pi.add_def,add_zero] using!
    (initial.add (hasDerivAt_const z (dressedHistoryContact event transfer t (fieldUnit j) i))).add integrated

/-- The complete finite quantum response supplies its true synchronized-clock frequency jet. -/
theorem dressed_coincident_clock_jet_generated (event : DressedEvent) (transfer : PhysicalMomentum)
    (z : ℂ) (T : ℝ) :
    HasDerivAt (fun w=>dressedWindowPolarization event transfer (sourceInputClock w) w T)
      (dressedCoincidentClockJet event transfer z T) z := by
  have original : (fun w=>dressedWindowPolarization event transfer (sourceInputClock w) w T)=
      fun w i j=>∫t in (0:ℝ)..T,
        Complex.exp (-(t:ℂ)*w)*dressedHistoryInitial event transfer t (fieldUnit j) i+
          dressedHistoryContact event transfer t (fieldUnit j) i+
          ∫s in (0:ℝ)..t,Complex.exp (((s-t:ℝ):ℂ)*w)*dressedHistoryMemory event transfer t s (fieldUnit j) i := by
    funext w
    exact dressed_coincident_polarization_kernel event transfer w T
  rw [original]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have initial : Continuous (fun zt : ℂ×ℝ=>dressedHistoryInitial event transfer zt.2 (fieldUnit j) i) :=
    (dressed_history_initial_continuous event transfer i j).comp continuous_snd
  have contact : Continuous (fun zt : ℂ×ℝ=>dressedHistoryContact event transfer zt.2 (fieldUnit j) i) :=
    (dressed_history_contact_continuous event transfer i j).comp continuous_snd
  have exponential : Continuous (fun zt : ℂ×ℝ=>Complex.exp (-(zt.2:ℂ)*zt.1)) := by fun_prop
  have number : Continuous (fun zt : ℂ×ℝ=>-(zt.2:ℂ)) := by fun_prop
  have memory:=lag_memory_continuous event transfer i j false
  simp only [Bool.false_eq_true,if_false,one_mul] at memory
  have clockMemory:=lag_memory_continuous event transfer i j true
  simp only [if_true] at clockMemory
  exact interval_input_jet _ _ (((exponential.mul initial).add contact).add memory)
    (((number.mul exponential).mul initial).add clockMemory)
    (fun w t=>lag_entry_derivative event transfer w t i j) z 0 T

end LowEnergy.GaussComposite.ActualDressedPhysicalClock
