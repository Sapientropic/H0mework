import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussGradedCompression
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceFiniteUnitary

/-! The original Number/G resolution is retained by the common time occurrence itself. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussGradedUnitary
open GaussCoreHilbert GaussDiagonalHistory SourceFamilyOperator Filter
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open SourceFamilyHilbert (Family value)
open NativeHistoryGrade (Label projection)
open scoped Topology InnerProductSpace ContDiff

def finiteTime (t : ℝ) : Operator Index H :=
  ⟨fun F => SourceFiniteUnitary.time (GaussGradedCompression.compression F) t,
    1, zero_le_one, fun F x => by
      rw [SourceFiniteUnitary.time_norm _ (GaussGradedCompression.compression_selfAdjoint F), one_mul]⟩

def time (t : ℝ) : HistorySpace →L[ℂ] HistorySpace := lift sourceFilter (finiteTime t)

theorem time_zero : time 0 = 1 :=
  (lift_congr sourceFilter (finiteTime 0) (constant 1)
    (fun F => SourceFiniteUnitary.time_zero (GaussGradedCompression.compression F))).trans
      (lift_identity (E := H) sourceFilter)

theorem time_add (s t : ℝ) : time (s+t) = time s * time t :=
  (lift_congr sourceFilter (finiteTime (s+t)) (comp (finiteTime s) (finiteTime t))
    (fun F => SourceFiniteUnitary.time_add (GaussGradedCompression.compression F) s t)).trans
      (lift_comp sourceFilter _ _)

theorem time_inverse_left (t : ℝ) : time (-t)*time t = 1 := by
  rw [← time_add, neg_add_cancel, time_zero]

theorem time_inverse_right (t : ℝ) : time t*time (-t) = 1 := by
  rw [← time_add, add_neg_cancel, time_zero]

theorem time_norm (t : ℝ) (f : HistorySpace) : ‖time t f‖ = ‖f‖ :=
  lift_isometry sourceFilter (finiteTime t) (fun F x =>
    SourceFiniteUnitary.time_norm _ (GaussGradedCompression.compression_selfAdjoint F) t x) f

theorem time_blocks (t : ℝ) (g : Label) : reader (projection g) * time t = time t * reader (projection g) := by
  calc
    _ = lift sourceFilter (comp (constant (projection g)) (finiteTime t)) := (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (finiteTime t) (constant (projection g))) := by
      apply lift_congr sourceFilter
      intro F
      exact (SourceFiniteUnitary.time_commutes (GaussGradedCompression.compression F) (projection g)
        (GaussGradedCompression.compression_commutes F g) t).eq
    _ = _ := lift_comp sourceFilter _ _

def trajectory (t : ℝ) (x : H) : Family H sourceFilter :=
  act sourceFilter (finiteTime t) (SourceFamilyHilbert.constant sourceFilter x)

theorem time_inclusion (t : ℝ) (x : H) : time t (inclusion x) = (trajectory t x : HistorySpace) :=
  lift_coe sourceFilter (finiteTime t) (SourceFamilyHilbert.constant sourceFilter x)

theorem core_remainder (x : diagonal.domain) (t h : ℝ) :
    ‖time (t+h) (inclusion (x : H)) - time t (inclusion (x : H)) -
      h • ((-Complex.I) • time t (inclusion (diagonal x)))‖ ≤
        ‖diagonal ⟨diagonal x, diagonal_invariant x⟩‖ * ‖h‖^2 := by
  classical
  let r : Family H sourceFilter := trajectory (t+h) x - trajectory t x -
    ((h : ℂ)*(-Complex.I)) • trajectory t (diagonal x)
  have hr : (r : HistorySpace) = time (t+h) (inclusion (x : H)) - time t (inclusion (x : H)) -
      h • ((-Complex.I) • time t (inclusion (diagonal x))) := by
    rw [time_inclusion, time_inclusion, time_inclusion,
      ← smul_assoc, Complex.real_smul]
    simp only [r, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_smul]
  rw [← hr, UniformSpace.Completion.norm_coe]
  apply SourceFamilyHilbert.norm_le_of_eventually sourceFilter r
  filter_upwards [GaussGradedCompression.eventually_contains x,
    GaussGradedCompression.eventually_contains ⟨diagonal x, diagonal_invariant x⟩] with F hx hTx
  have he := GaussGradedCompression.compression_core_exact F x hx hTx
  have hb := GaussGradedCompression.compression_core_bound F
    ⟨diagonal x, diagonal_invariant x⟩ hTx
  have hr := SourceFiniteUnitary.time_remainder (GaussGradedCompression.compression F)
    (GaussGradedCompression.compression_selfAdjoint F) (x : H) t h
  rw [he] at hr
  have hr' := hr.trans (mul_le_mul_of_nonneg_right hb (sq_nonneg ‖h‖))
  change ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F) (t+h) (x : H) -
    SourceFiniteUnitary.time (GaussGradedCompression.compression F) t (x : H) -
      ((h : ℂ)*(-Complex.I)) • SourceFiniteUnitary.time (GaussGradedCompression.compression F) t (diagonal x)‖ ≤ _
  simpa only [← smul_assoc, Complex.real_smul] using hr'

theorem core_derivative (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => time s (inclusion (x : H)))
      ((-Complex.I) • time t (inclusion (diagonal x))) t := by
  rw [hasDerivAt_iff_tendsto]
  let C := ‖diagonal ⟨diagonal x, diagonal_invariant x⟩‖
  have hlim : Tendsto (fun s : ℝ => C * ‖s-t‖) (𝓝 t) (𝓝 0) := by
    have hd : Tendsto (fun s : ℝ => s-t) (𝓝 t) (𝓝 (t-t)) :=
      (tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 t) (𝓝 t)).sub tendsto_const_nhds
    simpa only [sub_self, norm_zero, mul_zero] using hd.norm.const_mul C
  apply squeeze_zero (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun s => ?_) hlim
  have hb := core_remainder x t (s-t)
  have hc := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg (s-t)))
  have identity : t+(s-t) = s := by ring
  rw [identity] at hc
  have scalar : ‖s-t‖⁻¹ * (C * ‖s-t‖^2) = C * ‖s-t‖ := by
    by_cases hz : ‖s-t‖ = 0
    · simp [hz]
    · field_simp
  exact hc.trans_eq scalar

theorem core_smooth (x : diagonal.domain) : ContDiff ℝ ∞ (fun t => time t (inclusion (x : H))) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing x with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun t => (core_derivative x t).continuousAt))
  | succ n ih =>
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun t => (core_derivative x t).differentiableAt, ?_, ?_⟩
      · simp
      · have hd : deriv (fun t => time t (inclusion (x : H))) =
            fun t => (-Complex.I) • time t (inclusion (diagonal x)) :=
          funext (fun t => (core_derivative x t).deriv)
        rw [hd]
        exact (ih ⟨diagonal x, diagonal_invariant x⟩).const_smul (-Complex.I)

theorem core_uniform (x : diagonal.domain) (s t : ℝ) :
    ‖time t (inclusion (x : H)) - time s (inclusion (x : H))‖ ≤ ‖diagonal x‖ * ‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := Set.univ)
    (fun u _ => (core_derivative x u).hasDerivWithinAt) (fun u _ => ?_)
    convex_univ (Set.mem_univ s) (Set.mem_univ t)
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul, time_norm, inclusion.norm_map]

theorem source_difference (x : H) (v : diagonal.domain) (s t : ℝ) :
    ‖time t (inclusion x) - time s (inclusion x)‖ ≤
      2*‖x-(v : H)‖ + ‖diagonal v‖*‖t-s‖ := by
  exact (orbit_difference inclusion (time t) (time s) (time_norm t) (time_norm s) x (v : H)).trans
    (add_le_add le_rfl (core_uniform v s t))

theorem source_continuous (x : H) : Continuous (fun t => time t (inclusion x)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply Metric.continuousAt_iff.mpr
  intro epsilon positive
  obtain ⟨v, hv, near⟩ := Metric.mem_closure_iff.mp (diagonal_dense x) (epsilon/4) (by positivity)
  let w : diagonal.domain := ⟨v,hv⟩
  refine ⟨(epsilon/2)/(‖diagonal w‖+1), by positivity, ?_⟩
  intro t ht
  have hs : ‖t-s‖*(‖diagonal w‖+1) < epsilon/2 :=
    (lt_div_iff₀ (by positivity)).mp (by simpa only [dist_eq_norm] using ht)
  have hx : ‖x-(w : H)‖ < epsilon/4 := by simpa only [dist_eq_norm] using near
  have hb := source_difference x w s t
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (t-s)]

def response (A : H →L[ℂ] H) (t s : ℝ) (x y : H) : ℂ :=
  inner ℂ (time t (inclusion x)) (reader A (time s (inclusion y)))

theorem response_left (A : H →L[ℂ] H) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response A u s x y)
      (Complex.I * response A t s (diagonal x) y) t := by
  have h := (core_derivative x t).inner ℂ
    (hasDerivAt_const t (reader A (time s (inclusion (y : H)))))
  simpa [response, inner_smul_left] using h

theorem response_right (A : H →L[ℂ] H) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response A t u x y)
      (-Complex.I * response A t s x (diagonal y)) s := by
  have hA := (reader A).restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt s (core_derivative y s)
  have h := (hasDerivAt_const s (time t (inclusion (x : H)))).inner ℂ hA
  simpa [response, inner_smul_right] using h


#print axioms time_add
#print axioms time_norm
#print axioms time_blocks
#print axioms core_derivative
#print axioms core_smooth
#print axioms source_continuous
#print axioms response_left
#print axioms response_right
end LowEnergy.GaussGradedUnitary
