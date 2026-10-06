import H0mework.Physics.LowEnergy.Quantum.FiniteCoreEvolution

/-! Bounded source compressions retain their exact second time remainder. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.SourceFiniteUnitary
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

def time (C : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := NormedSpace.exp (t • ((-Complex.I) • C))

theorem time_unitary (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    time C t ∈ unitary (E →L[ℂ] E) := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  rw [skewAdjoint.mem_iff]
  simp [star_smul, symmetric.star_eq]

theorem time_norm (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) (x : E) :
    ‖time C t x‖ = ‖x‖ := ContinuousLinearMap.norm_map_of_mem_unitary (time_unitary C symmetric t) x

theorem time_add (C : E →L[ℂ] E) (s t : ℝ) : time C (s+t) = time C s * time C t := by
  unfold time
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute ((Commute.refl ((-Complex.I) • C)).smul_left s |>.smul_right t)

theorem time_zero (C : E →L[ℂ] E) : time C 0 = 1 := by
  rw [time, zero_smul, NormedSpace.exp_zero]

theorem time_commutes (C P : E →L[ℂ] E) (h : Commute P C) (t : ℝ) : Commute P (time C t) :=
  (h.smul_right (-Complex.I) |>.smul_right t).exp_right

theorem time_derivative (C : E →L[ℂ] E) (t : ℝ) (x : E) :
    HasDerivAt (fun s => time C s x) ((-Complex.I) • time C t (C x)) t := by
  have h := hasDerivAt_exp_smul_const ((-Complex.I) • C) t
  let ev := (ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ
  have he := ev.hasFDerivAt.comp_hasDerivAt t h
  change HasDerivAt (fun s => time C s x) ((time C t) (((-Complex.I) • C) x)) t at he
  simpa only [smul_apply, map_smul] using he

theorem time_uniform (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (x : E) (s t : ℝ) :
    ‖time C t x-time C s x‖ ≤ ‖C x‖ * ‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.univ) (fun u _ => (time_derivative C u x).hasDerivWithinAt)
    (fun u _ => ?_) convex_univ (Set.mem_univ s) (Set.mem_univ t)
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul, time_norm C symmetric]

theorem time_remainder (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (x : E) (t h : ℝ) :
    ‖time C (t+h) x-time C t x-h • ((-Complex.I) • time C t (C x))‖ ≤ ‖C (C x)‖*‖h‖^2 := by
  let velocity := (-Complex.I) • time C t (C x)
  let f := fun u : ℝ => time C u x-u • velocity
  let df := fun u : ℝ => (-Complex.I) • time C u (C x)-velocity
  have hd (u : ℝ) : HasDerivAt f (df u) u := by
    have hd0 := (time_derivative C u x).sub ((hasDerivAt_id u).smul_const velocity)
    change HasDerivAt f ((-Complex.I) • time C u (C x)-(1 : ℝ) • velocity) u at hd0
    simpa only [df, one_smul] using hd0
  have hb (u : ℝ) (hu : u ∈ Metric.closedBall t ‖h‖) : ‖df u‖ ≤ ‖C (C x)‖*‖h‖ := by
    have distance : ‖u-t‖ ≤ ‖h‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
    calc
      ‖df u‖ = ‖time C u (C x)-time C t (C x)‖ := by
        simp only [df, velocity, ← smul_sub, norm_smul, norm_neg, Complex.norm_I, one_mul]
      _ ≤ ‖C (C x)‖*‖u-t‖ := time_uniform C symmetric (C x) t u
      _ ≤ ‖C (C x)‖*‖h‖ := mul_le_mul_of_nonneg_left distance (norm_nonneg _)
  have estimate := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Metric.closedBall t ‖h‖) => (hd u).hasDerivWithinAt) hb
    (convex_closedBall t ‖h‖) (Metric.mem_closedBall_self (norm_nonneg h))
    (show t+h ∈ Metric.closedBall t ‖h‖ by simp [Metric.mem_closedBall, dist_eq_norm])
  have identity : f (t+h)-f t = time C (t+h) x-time C t x-h • velocity := by
    simp only [f, add_smul]
    abel
  simpa only [identity, add_sub_cancel_left, mul_assoc, ← pow_two, velocity] using estimate

#print axioms time_unitary
#print axioms time_commutes
#print axioms time_remainder
end LowEnergy.SourceFiniteUnitary
