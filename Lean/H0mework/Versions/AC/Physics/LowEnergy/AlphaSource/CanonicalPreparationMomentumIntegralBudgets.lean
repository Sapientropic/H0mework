import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationMomentumTargetBudgets

set_option autoImplicit false
set_option maxHeartbeats 240000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMomentumFirst
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationVacuumFourierJets
open CanonicalPreparationSquareCutoff MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap

def sourceTargetIntegralBound (j n : ℕ) : ℝ := sourcePositionVolume*sourceTargetBound j n

theorem sourceTargetIntegralBound_nonnegative (j n : ℕ) : 0 ≤ sourceTargetIntegralBound j n :=
  mul_nonneg sourcePositionVolume_nonnegative (sourceTargetBound_nonnegative j n)

theorem momentumFirstJet_integrable (j n : ℕ) (p : PhysicalMomentum) :
    Integrable (fun x : PhysicalMomentum => ‖momentumFirstJet j n (x,p)‖) := by
  have integrable : Integrable (fun x : PhysicalMomentum =>
      ‖iteratedFDeriv ℝ j (fun y : PhysicalMomentum => sourceMomentumJet n (y,p)) x‖) :=
    (sourceMomentumJet_x_smooth n p).continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤)) |>.integrable_of_hasCompactSupport
      ((sourceMomentumJet_compact n p).iteratedFDeriv j) |>.norm
  simpa only [momentumFirstJet_original] using integrable

private theorem momentumFirstJet_integral_bounds (j n : ℕ) (p : PhysicalMomentum) (weight : ℝ)
    (actualBound : ∀ x : PhysicalMomentum, ‖momentumFirstJet j n (x,p)‖ ≤ sourceTargetBound j n*weight) :
    (∫ x : PhysicalMomentum,‖momentumFirstJet j n (x,p)‖) ≤ sourceTargetIntegralBound j n*weight := by
  have finite : (volume : Measure PhysicalMomentum) positionCompact≠⊤ := positionCompact_compact.measure_ne_top
  have same : (∫ x in positionCompact,‖momentumFirstJet j n (x,p)‖)=
      ∫ x : PhysicalMomentum,‖momentumFirstJet j n (x,p)‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by
        rw [momentumFirstJet_zero_outside j n x p hx]
        exact @norm_zero
          (ContinuousMultilinearMap ℝ (fun _ : Fin j => PhysicalMomentum) (MomentumJet n)) inferInstance)
  calc
    _ = ∫ x in positionCompact,‖momentumFirstJet j n (x,p)‖ := same.symm
    _ ≤ ∫ _x in positionCompact,sourceTargetBound j n*weight :=
      setIntegral_mono_on (momentumFirstJet_integrable j n p).integrableOn (integrableOn_const finite)
        positionCompact_closed.measurableSet (fun x _ => actualBound x)
    _ = sourceTargetIntegralBound j n*weight := by
      rw [setIntegral_const]
      change ((volume : Measure PhysicalMomentum) positionCompact).toReal*(sourceTargetBound j n*weight)=_
      rw [positionCompact_measure]
      change sourcePositionVolume*(sourceTargetBound j n*weight)=_
      rw [sourceTargetIntegralBound,mul_assoc]

theorem momentumFirstJet_integral_order_zero (j : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖momentumFirstJet j 0 (x,p)‖) ≤ sourceTargetIntegralBound j 0*(1+‖p‖) :=
  momentumFirstJet_integral_bounds j 0 p (1+‖p‖) (fun x => momentumFirstJet_order_zero_bound j x p)

theorem momentumFirstJet_integral_order_one (j : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖momentumFirstJet j 1 (x,p)‖) ≤ sourceTargetIntegralBound j 1 := by
  have actual := momentumFirstJet_integral_bounds j 1 p 1
    (fun x => by simpa only [mul_one] using momentumFirstJet_order_one_bound j x p)
  simpa only [mul_one] using actual

theorem momentumFirstJet_integral_order_succ (j n : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖momentumFirstJet j (n+1) (x,p)‖) ≤
      4^n*sourceTargetIntegralBound j (n+1)/(1+‖p‖)^n := by
  have actual := momentumFirstJet_integral_bounds j (n+1) p (4^n/(1+‖p‖)^n)
    (fun x => by simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using
      momentumFirstJet_order_succ_bound j n x p)
  simpa only [div_eq_mul_inv,sourceTargetIntegralBound,mul_assoc,mul_comm,mul_left_comm] using actual

theorem sourceFourierJet_derivative_integral_order_zero (j : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (sourceMomentumJetSchwartz 0 p) x‖) ≤
      sourceTargetIntegralBound j 0*(1+‖p‖) := by
  have same : (sourceMomentumJetSchwartz 0 p : PhysicalMomentum → MomentumJet 0)=
      (fun y => sourceMomentumJet 0 (y,p)) := by funext y; exact sourceMomentumJetSchwartz_apply 0 p y
  rw [same]
  simpa only [momentumFirstJet_original] using momentumFirstJet_integral_order_zero j p

theorem sourceFourierJet_derivative_integral_order_one (j : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (sourceMomentumJetSchwartz 1 p) x‖) ≤
      sourceTargetIntegralBound j 1 := by
  have same : (sourceMomentumJetSchwartz 1 p : PhysicalMomentum → MomentumJet 1)=
      (fun y => sourceMomentumJet 1 (y,p)) := by funext y; exact sourceMomentumJetSchwartz_apply 1 p y
  rw [same]
  simpa only [momentumFirstJet_original] using momentumFirstJet_integral_order_one j p

theorem sourceFourierJet_derivative_integral_order_succ (j n : ℕ) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ j (sourceMomentumJetSchwartz (n+1) p) x‖) ≤
      4^n*sourceTargetIntegralBound j (n+1)/(1+‖p‖)^n := by
  have same : (sourceMomentumJetSchwartz (n+1) p : PhysicalMomentum → MomentumJet (n+1))=
      (fun y => sourceMomentumJet (n+1) (y,p)) := by funext y; exact sourceMomentumJetSchwartz_apply (n+1) p y
  rw [same]
  simpa only [momentumFirstJet_original] using momentumFirstJet_integral_order_succ j n p

end LowEnergy.PreparationVacuumMomentumFirst
