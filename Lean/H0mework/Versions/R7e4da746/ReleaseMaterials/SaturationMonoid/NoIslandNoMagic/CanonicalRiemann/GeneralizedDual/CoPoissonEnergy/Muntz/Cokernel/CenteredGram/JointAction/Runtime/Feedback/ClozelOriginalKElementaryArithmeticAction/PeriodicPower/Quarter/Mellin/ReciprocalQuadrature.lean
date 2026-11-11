import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.GlobalLipschitz
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Forward
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature
open Complex Filter MeasureTheory Set BurnolPhysicalState
open scoped Topology ENNReal

private theorem cell_variation (g dg:ℝ→ℂ) (regular:Continuous dg)
    (source:∀t:ℝ,0≤t → HasDerivAt g (dg t) t)
    (a d:ℝ) (lower:0≤a) (positive:0<d) :
    ‖(d:ℂ)*g (a+d)-∫t:ℝ in a..(a+d),g t‖≤
      d*(∫t:ℝ in a..(a+d),‖dg t‖) := by
  have ordered:a≤a+d:=by linarith
  have continuous:ContinuousOn g (Icc a (a+d)) := by
    intro t inside
    exact (source t (lower.trans inside.1)).continuousAt.continuousWithinAt
  have difference (t:ℝ) (inside:t∈Icc a (a+d)) :
      ‖g (a+d)-g t‖≤∫u:ℝ in a..(a+d),‖dg u‖ := by
    have actual:=intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a:=t) (b:=a+d) (f:=g) (f':=dg) (fun u hu=>source u (by
        rw [uIcc_of_le inside.2] at hu
        exact lower.trans (inside.1.trans hu.1))) (regular.intervalIntegrable t (a+d))
    rw [←actual]
    exact (intervalIntegral.norm_integral_le_integral_norm inside.2).trans
      (intervalIntegral.integral_mono_interval inside.1 inside.2 le_rfl
        (Eventually.of_forall (fun u=>norm_nonneg (dg u))) (regular.norm.intervalIntegrable a (a+d)))
  have identity : (d:ℂ)*g (a+d)-∫t:ℝ in a..(a+d),g t=
      ∫t:ℝ in a..(a+d),g (a+d)-g t := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (continuous.intervalIntegrable_of_Icc ordered),intervalIntegral.integral_const,
      add_sub_cancel_left,Complex.real_smul]
  rw [identity]
  have bounded:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=a) (b:=a+d) (C:=∫t:ℝ in a..(a+d),‖dg t‖) (f:=fun t=>g (a+d)-g t)
    (fun t inside=>difference t (Ioc_subset_Icc_self (by
      simpa only [uIoc_of_le ordered] using inside)))
  simpa only [add_sub_cancel_left,abs_of_pos positive,mul_comm] using bounded

/-- The full finite grid is paid by the actual integrated derivative, independent of its support. -/
theorem actual_finite_grid_variation (g dg:ℝ→ℂ) (regular:Continuous dg)
    (source:∀t:ℝ,0≤t → HasDerivAt g (dg t) t) (d:ℝ) (positive:0<d) (M:ℕ) :
    ‖(d:ℂ)*(∑n∈Finset.range M,g (((n+1:ℕ):ℝ)*d))-
      ∫t:ℝ in (0:ℝ)..((M:ℝ)*d),g t‖≤
      d*(∫t:ℝ in (0:ℝ)..((M:ℝ)*d),‖dg t‖) := by
  have integrable (n:ℕ) (_hn:n<M) :
      IntervalIntegrable g volume ((n:ℝ)*d) (((n+1:ℕ):ℝ)*d) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by push_cast;linarith)
    intro t inside
    exact (source t ((mul_nonneg (Nat.cast_nonneg n) positive.le).trans inside.1)).continuousAt.continuousWithinAt
  have adjacent:=intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun n:ℕ=>(n:ℝ)*d) integrable
  have normAdjacent:=intervalIntegral.sum_integral_adjacent_intervals
    (a:=fun n:ℕ=>(n:ℝ)*d) (fun n (_:n<M)=>regular.norm.intervalIntegrable (μ:=volume) _ _)
  simp only [Nat.cast_zero,zero_mul] at adjacent normAdjacent
  rw [←adjacent,Finset.mul_sum,←Finset.sum_sub_distrib]
  calc
    _≤∑n∈Finset.range M,‖(d:ℂ)*g (((n+1:ℕ):ℝ)*d)-
        ∫t:ℝ in ((n:ℝ)*d)..(((n+1:ℕ):ℝ)*d),g t‖ := norm_sum_le _ _
    _≤∑n∈Finset.range M,d*(∫t:ℝ in ((n:ℝ)*d)..(((n+1:ℕ):ℝ)*d),‖dg t‖) := by
      apply Finset.sum_le_sum
      intro n _
      simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using
        cell_variation g dg regular source ((n:ℝ)*d) d
          (mul_nonneg (Nat.cast_nonneg n) positive.le) positive
    _=_ := by rw [←Finset.mul_sum,normAdjacent]

/-- The same entire grid and derivative current pass to their actual improper limits. -/
theorem actual_infinite_grid_variation (g dg:ℝ→ℂ) (regular:Continuous dg)
    (source:∀t:ℝ,0≤t → HasDerivAt g (dg t) t)
    (gIntegrable:IntegrableOn g (Ioi 0)) (dgIntegrable:IntegrableOn dg (Ioi 0))
    (d:ℝ) (positive:0<d) (summable:Summable (fun n:ℕ=>g (((n+1:ℕ):ℝ)*d))) :
    ‖(d:ℂ)*(∑'n:ℕ,g (((n+1:ℕ):ℝ)*d))-∫t:ℝ in Ioi 0,g t‖≤
      d*(∫t:ℝ in Ioi 0,‖dg t‖) := by
  have infinity:Tendsto (fun M:ℕ=>(M:ℝ)*d) atTop atTop:=
    (tendsto_natCast_atTop_atTop (R:=ℝ)).atTop_mul_const positive
  have left:=((tendsto_const_nhds (x:=(d:ℂ))).mul summable.hasSum.tendsto_sum_nat).sub
    (intervalIntegral_tendsto_integral_Ioi 0 gIntegrable infinity)
  have right:=(intervalIntegral_tendsto_integral_Ioi 0 dgIntegrable.norm infinity).const_mul d
  exact le_of_tendsto_of_tendsto left.norm right
    (Eventually.of_forall (actual_finite_grid_variation g dg regular source d positive))

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Mellin.ReciprocalQuadrature
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
