import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussUnitaryHistory

/-! The common time occurrence differentiates to the literal original H0 on its core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussUnitaryCore
open GaussCoreHilbert GaussDiagonalHistory GaussUnitaryHistory SourceFamilyOperator Filter
open SourceFamilyHilbert (Family value)
open scoped Topology InnerProductSpace ContDiff

instance : NormedSpace ℝ HistorySpace := NormedSpace.restrictScalars ℝ ℂ _
instance : IsScalarTower ℝ ℂ HistorySpace := IsScalarTower.restrictScalars ℝ ℂ _

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
  apply WeakCoreEvolution.sourceFilter_cofinal diagonal
  refine Filter.eventually_atTop.mpr ⟨{x, ⟨diagonal x, diagonal_invariant x⟩}, fun F hF => ?_⟩
  change ‖FiniteCoreEvolution.evolution diagonal F (t+h) (x : H) -
    FiniteCoreEvolution.evolution diagonal F t (x : H) -
      ((h : ℂ)*(-Complex.I)) • FiniteCoreEvolution.evolution diagonal F t (diagonal x)‖ ≤ _
  simpa only [← smul_assoc, Complex.real_smul] using
    FiniteCoreEvolution.evolution_core_remainder diagonal diagonal_pair x (diagonal_invariant x) F
      (hF (by simp)) (hF (by simp)) t h

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

theorem heisenberg_response (A : H →L[ℂ] H) (t : ℝ) (x y : H) :
    inner ℂ (inclusion x) (heisenberg t A (inclusion y)) = response A t t x y := by
  change inner ℂ (inclusion x) (time (-t) (reader A (time t (inclusion y)))) = _
  exact (time_pair t (inclusion x) (reader A (time t (inclusion y)))).symm

#print axioms core_remainder
#print axioms core_derivative
#print axioms core_smooth
#print axioms source_continuous
#print axioms response_left
#print axioms response_right
end LowEnergy.GaussUnitaryCore
