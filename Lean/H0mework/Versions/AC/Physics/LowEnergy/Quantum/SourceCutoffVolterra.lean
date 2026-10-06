import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussYukawaInteraction
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussGradedUnitary
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Ordered original-C_F integrals are generated before taking the same source-family lift. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.FullYSourceCutoffVolterra
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory
open GaussUnitaryHistory (HistorySpace sourceFilter reader)
open SourceFamilyOperator
open scoped Topology InnerProductSpace Interval ContDiff

def cutoff : ℕ → H →L[ℂ] H
  | 0 => GaussYukawaOperator.bounded
  | n+1 => GaussYukawaOperator.bounded +
      (1-GaussRadialDomain.inverseRadius) * cutoff n

theorem cutoff_graph_residual (n : ℕ) :
    GaussRadialDomain.inverseRadius * cutoff n =
      GaussYukawaOperator.bounded - (cutoff (n+1)-cutoff n) := by
  rw [cutoff, sub_mul, one_mul]
  abel

private theorem raises_add_product {R : Type*} [Ring R] (G B T A : R)
    (hB : G*B=B*G+B) (hT : G*T=T*G) (hA : G*A=A*G+A) :
    G*(B+T*A)=(B+T*A)*G+(B+T*A) := by
  calc
    _ = G*B+T*(G*A) := by rw [mul_add, ← mul_assoc G T A, hT, mul_assoc]
    _ = (B*G+B)+T*(A*G+A) := by rw [hB,hA]
    _ = _ := by simp only [mul_add, add_mul, ← mul_assoc]; abel

theorem cutoff_raises (n : ℕ) :
    GaussYukawaGrade.grade * cutoff n =
      cutoff n * GaussYukawaGrade.grade + cutoff n := by
  have hg : GaussYukawaGrade.grade * (1-GaussRadialDomain.inverseRadius) =
      (1-GaussRadialDomain.inverseRadius) * GaussYukawaGrade.grade := by
    simp only [mul_sub, sub_mul, mul_one, one_mul, GaussYukawaGrade.inverse_grade]
  induction n with
  | zero => exact GaussYukawaGrade.bounded_raises
  | succ n ih =>
    exact raises_add_product _ _ _ _ GaussYukawaGrade.bounded_raises hg ih

private theorem inverse_core_mem (x : Core) : GaussRadialDomain.inverseRadius (x : H) ∈ Core := by
  obtain ⟨f,hf⟩ := embed_surjective_core x
  rw [← hf, GaussRadialDomain.inverse_core]
  exact embed_mem_core _

theorem cutoff_core_mem (n : ℕ) (x : Core) : cutoff n (x : H) ∈ Core := by
  induction n with
  | zero => exact GaussYukawaOperator.bounded_preserves_core x
  | succ n ih =>
    change GaussYukawaOperator.bounded (x : H) +
      (cutoff n (x : H)-GaussRadialDomain.inverseRadius (cutoff n (x : H))) ∈ Core
    exact Core.add_mem (GaussYukawaOperator.bounded_preserves_core x)
      (Core.sub_mem ih (inverse_core_mem ⟨_,ih⟩))

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem continuous_time (C : E →L[ℂ] E) : Continuous (SourceFiniteUnitary.time C) := by
  exact continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

def interaction (C A : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  SourceFiniteUnitary.time C t * ((-Complex.I) • A) * SourceFiniteUnitary.time C (-t)

theorem interaction_continuous (C A : E →L[ℂ] E) : Continuous (interaction C A) :=
  ((continuous_time C).mul continuous_const).mul ((continuous_time C).comp continuous_neg)

private theorem conjugate_raises {R : Type*} [Ring R] (G U V B : R)
    (hU : G*U=U*G) (hV : G*V=V*G) (hB : G*B=B*G+B) :
    G*(U*B*V)=(U*B*V)*G+U*B*V := by
  calc
    _ = (G*U)*B*V := by simp only [mul_assoc]
    _ = U*(G*B)*V := by rw [hU]; simp only [mul_assoc]
    _ = U*(B*G+B)*V := by rw [hB]
    _ = U*B*(G*V)+U*B*V := by simp only [mul_add, add_mul, mul_assoc]
    _ = _ := by rw [hV]; simp only [mul_assoc]

theorem interaction_raises (C A G : E →L[ℂ] E) (hC : Commute G C)
    (hA : G*A=A*G+A) (t : ℝ) :
    G*interaction C A t=interaction C A t*G+interaction C A t := by
  have hs : G*((-Complex.I) • A)=((-Complex.I) • A)*G+((-Complex.I) • A) := by
    simp only [mul_smul_comm, smul_mul_assoc, hA, smul_add]
  exact conjugate_raises _ _ _ _
    (SourceFiniteUnitary.time_commutes C G hC t).eq
    (SourceFiniteUnitary.time_commutes C G hC (-t)).eq hs

def gradeBracket (G : E →L[ℂ] E) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  ContinuousLinearMap.mul ℂ (E →L[ℂ] E) G -
    (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip G

private theorem homogeneous_product (G A B : E →L[ℂ] E) (n : ℕ)
    (hA : G*A=A*G+(n : ℂ) • A) (hB : G*B=B*G+B) :
    gradeBracket G (A*B) = ((n+1 : ℕ) : ℂ) • (A*B) := by
  change G*(A*B)-(A*B)*G=_
  rw [← mul_assoc, hA, add_mul, mul_assoc A G B, hB]
  simp only [mul_add, smul_mul_assoc, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
  simp only [← mul_assoc]
  abel

def orderedIntegral (C A : E →L[ℂ] E) : ℕ → ℝ → E →L[ℂ] E
  | 0, _ => 1
  | n+1, t => ∫ s in (0 : ℝ)..t, orderedIntegral C A n s * interaction C A s

theorem orderedIntegral_continuous (C A : E →L[ℂ] E) (n : ℕ) :
    Continuous (orderedIntegral C A n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    exact continuous_iff_continuousAt.mpr (fun t =>
      ((ih.mul (interaction_continuous C A)).integral_hasStrictDerivAt 0 t).hasDerivAt.continuousAt)

theorem orderedIntegral_derivative (C A : E →L[ℂ] E) (n : ℕ) (t : ℝ) :
    HasDerivAt (orderedIntegral C A (n+1))
      (orderedIntegral C A n t * interaction C A t) t :=
  (((orderedIntegral_continuous C A n).mul (interaction_continuous C A)).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem orderedIntegral_homogeneous (C A G : E →L[ℂ] E) (hC : Commute G C)
    (hA : G*A=A*G+A) (n : ℕ) (t : ℝ) :
    G*orderedIntegral C A n t = orderedIntegral C A n t*G +
      (n : ℂ) • orderedIntegral C A n t := by
  induction n generalizing t with
  | zero => simp only [orderedIntegral, mul_one, one_mul, Nat.cast_zero, zero_smul, add_zero]
  | succ n ih =>
    let f := fun s => orderedIntegral C A n s * interaction C A s
    have hf : Continuous f := (orderedIntegral_continuous C A n).mul (interaction_continuous C A)
    have he (s : ℝ) : gradeBracket G (f s)=((n+1 : ℕ) : ℂ) • f s :=
      homogeneous_product G _ _ n (ih s) (interaction_raises C A G hC hA s)
    have hp := (gradeBracket G).intervalIntegral_comp_comm
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 t)
    simp_rw [he] at hp
    rw [intervalIntegral.integral_smul] at hp
    change ((n+1 : ℕ) : ℂ) • orderedIntegral C A (n+1) t =
      G*orderedIntegral C A (n+1) t-orderedIntegral C A (n+1) t*G at hp
    exact (sub_eq_iff_eq_add.mp hp.symm).trans (add_comm _ _)

private theorem time_opNorm (C : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖SourceFiniteUnitary.time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [SourceFiniteUnitary.time_norm C symmetric, one_mul]
  exact le_rfl

theorem interaction_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖interaction C A t‖ ≤ ‖A‖ := by
  have hm : ‖(-Complex.I) • A‖ = ‖A‖ := by simp only [norm_smul, norm_neg, Complex.norm_I, one_mul]
  calc
    _ ≤ (‖SourceFiniteUnitary.time C t‖ * ‖(-Complex.I) • A‖) *
        ‖SourceFiniteUnitary.time C (-t)‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖A‖) * 1 := by
      rw [hm]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (time_opNorm C symmetric t) (norm_nonneg A))
        (time_opNorm C symmetric (-t)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem abs_le_of_mem_interval {t s T : ℝ} (_hT : 0 ≤ T) (ht : |t| ≤ T)
    (hs : s ∈ Ι (0 : ℝ) t) : |s| ≤ T := by
  by_cases ht0 : 0 ≤ t
  · rw [Set.uIoc_of_le ht0] at hs
    rw [abs_of_pos hs.1]
    exact hs.2.trans (by simpa only [abs_of_nonneg ht0] using ht)
  · have htn : t ≤ 0 := le_of_not_ge ht0
    rw [Set.uIoc_of_ge htn] at hs
    rw [abs_of_nonpos hs.2]
    have hlow : -T ≤ t := (abs_le.mp ht).1
    linarith [hs.1]

theorem orderedIntegral_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C)
    (n : ℕ) (T : ℝ) (hT : 0 ≤ T) (t : ℝ) (ht : |t| ≤ T) :
    ‖orderedIntegral C A n t‖ ≤ (T*‖A‖)^n := by
  induction n generalizing t with
  | zero => simpa only [orderedIntegral, pow_zero, SourceFiniteUnitary.time_zero]
      using time_opNorm C symmetric 0
  | succ n ih =>
    have bound (s : ℝ) (hs : s ∈ Ι (0 : ℝ) t) :
        ‖orderedIntegral C A n s * interaction C A s‖ ≤ (T*‖A‖)^n*‖A‖ :=
      (norm_mul_le _ _).trans (mul_le_mul
        (ih s (abs_le_of_mem_interval hT ht hs)) (interaction_bound C A symmetric s)
        (norm_nonneg _) (by positivity))
    calc
      _ ≤ ((T*‖A‖)^n*‖A‖)*|t-0| := intervalIntegral.norm_integral_le_of_norm_le_const bound
      _ ≤ ((T*‖A‖)^n*‖A‖)*T := by
        exact mul_le_mul_of_nonneg_left (by simpa only [sub_zero] using ht) (by positivity)
      _ = _ := by rw [pow_succ]; ring

def finitePrefix (C A : E →L[ℂ] E) (n : ℕ) (t : ℝ) : E →L[ℂ] E :=
  orderedIntegral C A n t * SourceFiniteUnitary.time C t

theorem finitePrefix_right_derivative (C A : E →L[ℂ] E) (n : ℕ) (t : ℝ) :
    HasDerivAt (finitePrefix C A (n+1))
      (finitePrefix C A n t * ((-Complex.I) • A) +
        finitePrefix C A (n+1) t * ((-Complex.I) • C)) t := by
  have hU := hasDerivAt_exp_smul_const ((-Complex.I) • C) t
  change HasDerivAt (SourceFiniteUnitary.time C)
    (SourceFiniteUnitary.time C t * ((-Complex.I) • C)) t at hU
  have hi : SourceFiniteUnitary.time C (-t) * SourceFiniteUnitary.time C t = 1 := by
    rw [← SourceFiniteUnitary.time_add]
    simp only [neg_add_cancel, SourceFiniteUnitary.time_zero]
  have hp := (orderedIntegral_derivative C A n t).mul hU
  convert hp using 1
  all_goals
    first | rfl | simp only [finitePrefix, interaction, mul_assoc, hi, mul_one]

theorem finitePrefix_initial (C A : E →L[ℂ] E) (n : ℕ) :
    finitePrefix C A (n+1) 0 = 0 := by
  simp only [finitePrefix, orderedIntegral, intervalIntegral.integral_same, zero_mul]

theorem finitePrefix_homogeneous (C A G : E →L[ℂ] E) (hC : Commute G C)
    (hA : G*A=A*G+A) (n : ℕ) (t : ℝ) :
    G*finitePrefix C A n t = finitePrefix C A n t*G +
      (n : ℂ) • finitePrefix C A n t := by
  have hg := (SourceFiniteUnitary.time_commutes C G hC t).eq
  change G*(orderedIntegral C A n t*SourceFiniteUnitary.time C t) = _
  rw [← mul_assoc, orderedIntegral_homogeneous C A G hC hA n t,
    add_mul, mul_assoc _ G _, hg]
  simp only [finitePrefix, mul_assoc, smul_mul_assoc]

theorem finitePrefix_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C)
    (n : ℕ) (t : ℝ) : ‖finitePrefix C A n t‖ ≤ (|t| * ‖A‖)^n := by
  calc
    _ ≤ ‖orderedIntegral C A n t‖ * ‖SourceFiniteUnitary.time C t‖ := norm_mul_le _ _
    _ ≤ (|t| * ‖A‖)^n * 1 :=
      mul_le_mul (orderedIntegral_bound C A symmetric n |t| (abs_nonneg t) t le_rfl)
        (time_opNorm C symmetric t) (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

def partialEvolution (C A : E →L[ℂ] E) : ℕ → ℝ → E →L[ℂ] E
  | 0, t => SourceFiniteUnitary.time C t
  | n+1, t => partialEvolution C A n t + finitePrefix C A (n+1) t

theorem partialEvolution_initial (C A : E →L[ℂ] E) (n : ℕ) :
    partialEvolution C A n 0=1 := by
  induction n with
  | zero => exact SourceFiniteUnitary.time_zero C
  | succ n ih => simp only [partialEvolution, ih, finitePrefix_initial, add_zero]

theorem partialEvolution_derivative (C A : E →L[ℂ] E) (n : ℕ) (t : ℝ) :
    HasDerivAt (partialEvolution C A n)
      (partialEvolution C A n t * ((-Complex.I) • (C+A)) -
        finitePrefix C A n t * ((-Complex.I) • A)) t := by
  induction n with
  | zero =>
    have h := hasDerivAt_exp_smul_const ((-Complex.I) • C) t
    change HasDerivAt (SourceFiniteUnitary.time C)
      (SourceFiniteUnitary.time C t * ((-Complex.I) • C)) t at h
    convert h using 1
    all_goals
      first | rfl | simp only [partialEvolution, finitePrefix, orderedIntegral, one_mul,
        smul_add, mul_add, add_sub_cancel_right]
  | succ n ih =>
    have h := ih.add (finitePrefix_right_derivative C A n t)
    convert h using 1
    all_goals
      first | rfl | (simp only [partialEvolution, add_mul, smul_add, mul_add]; abel)

theorem partialEvolution_bound (C A : E →L[ℂ] E) (symmetric : IsSelfAdjoint C)
    (n : ℕ) (t : ℝ) :
    ‖partialEvolution C A n t‖ ≤ ∑ j ∈ Finset.range (n+1), (|t| * ‖A‖)^j := by
  induction n with
  | zero => simpa only [partialEvolution, Nat.zero_add, Finset.sum_range_one, pow_zero]
      using time_opNorm C symmetric t
  | succ n ih =>
    rw [partialEvolution, Finset.sum_range_succ]
    exact (norm_add_le _ _).trans (add_le_add ih (finitePrefix_bound C A symmetric (n+1) t))

theorem autonomous_evolution_unique (M : E →L[ℂ] E) (U : ℝ → E →L[ℂ] E)
    (hU : ∀ t, HasDerivAt U (U t*M) t) (hzero : U 0=1) (t : ℝ) :
    U t=NormedSpace.exp (t • M) := by
  let v := fun s : ℝ => U s * NormedSpace.exp (s • (-M))
  have hv (s : ℝ) : HasDerivAt v 0 s := by
    have h := (hU s).mul (hasDerivAt_exp_smul_const (-M) s)
    have hc : M*NormedSpace.exp (s • (-M))=NormedSpace.exp (s • (-M))*M :=
      ((Commute.refl M).neg_right.smul_right s).exp_right.eq
    convert h using 1
    all_goals
      first | rfl | (simp only [mul_neg, ← mul_assoc, ← hc, add_neg_cancel])
  have hc := is_const_of_deriv_eq_zero (fun s => (hv s).differentiableAt)
    (fun s => (hv s).deriv) t 0
  have he : U t * NormedSpace.exp (t • (-M))=1 := by
    simpa only [v, hzero, zero_smul, NormedSpace.exp_zero, mul_one] using hc
  have hi : NormedSpace.exp (t • (-M)) * NormedSpace.exp (t • M)=1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute (Commute.refl (t • M)).neg_left,
      neg_add_cancel, NormedSpace.exp_zero]
  calc
    U t = U t * (NormedSpace.exp (t • (-M))*NormedSpace.exp (t • M)) := by rw [hi,mul_one]
    _ = (U t*NormedSpace.exp (t • (-M)))*NormedSpace.exp (t • M) := (mul_assoc _ _ _).symm
    _ = _ := by rw [he,one_mul]

theorem time_adjoint (C : E →L[ℂ] E) (t : ℝ) :
    (SourceFiniteUnitary.time C t).adjoint=SourceFiniteUnitary.time C.adjoint (-t) := by
  have hp : star (t • ((-Complex.I) • C))=(-t) • ((-Complex.I) • C.adjoint) := by
    simp [star_smul, ContinuousLinearMap.star_eq_adjoint, neg_smul, smul_neg]
  change star (NormedSpace.exp (t • ((-Complex.I) • C))) = _
  rw [NormedSpace.star_exp, hp]
  rfl

theorem time_sum_adjoint (C A : E →L[ℂ] E) (hC : IsSelfAdjoint C) (t : ℝ) :
    (SourceFiniteUnitary.time (C+A) (-t)).adjoint=
      SourceFiniteUnitary.time (C+A.adjoint) t := by
  rw [time_adjoint, neg_neg]
  have ha : (C+A).adjoint=C+A.adjoint := by
    rw [map_add, hC.adjoint_eq]
  exact congrArg (fun D : E →L[ℂ] E => SourceFiniteUnitary.time D t) ha

theorem time_difference_on_ball (C : E →L[ℂ] E) (center radius M : ℝ)
    (bound : ∀ u ∈ Metric.closedBall center radius, ‖SourceFiniteUnitary.time C u‖ ≤ M)
    (x : E) (s t : ℝ) (hs : s ∈ Metric.closedBall center radius)
    (ht : t ∈ Metric.closedBall center radius) :
    ‖SourceFiniteUnitary.time C t x-SourceFiniteUnitary.time C s x‖ ≤
      (M*‖C x‖)*‖t-s‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Metric.closedBall center radius)
    (fun u _ => (SourceFiniteUnitary.time_derivative C u x).hasDerivWithinAt)
    (fun u hu => ?_) (convex_closedBall center radius) hs ht
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact ((SourceFiniteUnitary.time C u).le_opNorm (C x)).trans
    (mul_le_mul_of_nonneg_right (bound u hu) (norm_nonneg _))

theorem time_remainder_on_ball (C : E →L[ℂ] E) (x : E) (t h M : ℝ)
    (bound : ∀ u ∈ Metric.closedBall t ‖h‖, ‖SourceFiniteUnitary.time C u‖ ≤ M) :
    ‖SourceFiniteUnitary.time C (t+h) x-SourceFiniteUnitary.time C t x-
      h • ((-Complex.I) • SourceFiniteUnitary.time C t (C x))‖ ≤
        (M*‖C (C x)‖)*‖h‖^2 := by
  let velocity := (-Complex.I) • SourceFiniteUnitary.time C t (C x)
  let f := fun u : ℝ => SourceFiniteUnitary.time C u x-u • velocity
  let df := fun u : ℝ => (-Complex.I) • SourceFiniteUnitary.time C u (C x)-velocity
  have hd (u : ℝ) : HasDerivAt f (df u) u := by
    have h := (SourceFiniteUnitary.time_derivative C u x).sub ((hasDerivAt_id u).smul_const velocity)
    change HasDerivAt f ((-Complex.I) • SourceFiniteUnitary.time C u (C x)-
      (1 : ℝ) • velocity) u at h
    simpa only [df,one_smul] using h
  have hb (u : ℝ) (hu : u ∈ Metric.closedBall t ‖h‖) :
      ‖df u‖ ≤ (M*‖C (C x)‖)*‖h‖ := by
    have hdist : ‖u-t‖ ≤ ‖h‖ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
    have he := time_difference_on_ball C t ‖h‖ M bound (C x) t u
      (Metric.mem_closedBall_self (norm_nonneg h)) hu
    have hM : 0 ≤ M := (norm_nonneg (SourceFiniteUnitary.time C t)).trans
      (bound t (Metric.mem_closedBall_self (norm_nonneg h)))
    calc
      ‖df u‖ = ‖SourceFiniteUnitary.time C u (C x)-SourceFiniteUnitary.time C t (C x)‖ := by
        simp only [df,velocity,← smul_sub,norm_smul,norm_neg,Complex.norm_I,one_mul]
      _ ≤ (M*‖C (C x)‖)*‖u-t‖ := he
      _ ≤ _ := mul_le_mul_of_nonneg_left hdist (mul_nonneg hM (norm_nonneg _))
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u (_ : u ∈ Metric.closedBall t ‖h‖) => (hd u).hasDerivWithinAt) hb
    (convex_closedBall t ‖h‖) (Metric.mem_closedBall_self (norm_nonneg h))
    (show t+h ∈ Metric.closedBall t ‖h‖ by simp [Metric.mem_closedBall,dist_eq_norm])
  have hi : f (t+h)-f t = SourceFiniteUnitary.time C (t+h) x-SourceFiniteUnitary.time C t x-h • velocity := by
    simp only [f,add_smul]
    abel
  simpa only [hi,add_sub_cancel_left,mul_assoc,← pow_two,velocity] using he

omit [CompleteSpace E] in
theorem lift_family_remainder {I : Type*} (u : Ultrafilter I)
    (V : ℝ → SourceFamilyOperator.Operator I E) (x y : E) (t h M : ℝ)
    (bound : ∀ᶠ i in (u : Filter I),
      ‖(V (t+h)).component i x-(V t).component i x-
        h • ((-Complex.I) • (V t).component i y)‖ ≤ M) :
    ‖lift u (V (t+h)) (SourceFamilyHilbert.embed u x)-
      lift u (V t) (SourceFamilyHilbert.embed u x)-
      h • ((-Complex.I) • lift u (V t) (SourceFamilyHilbert.embed u y))‖ ≤ M := by
  let trajectory := fun s z => act u (V s) (SourceFamilyHilbert.constant u z)
  let r : SourceFamilyHilbert.Family E u := trajectory (t+h) x-trajectory t x-
    ((h : ℂ)*(-Complex.I)) • trajectory t y
  have hr : (r : SourceFamilyHilbert.Hilbert E u)=
      lift u (V (t+h)) (SourceFamilyHilbert.embed u x)-
      lift u (V t) (SourceFamilyHilbert.embed u x)-
      h • ((-Complex.I) • lift u (V t) (SourceFamilyHilbert.embed u y)) := by
    change (r : SourceFamilyHilbert.Hilbert E u)=
      lift u (V (t+h)) ((SourceFamilyHilbert.constant u x) : SourceFamilyHilbert.Hilbert E u)-
      lift u (V t) ((SourceFamilyHilbert.constant u x) : SourceFamilyHilbert.Hilbert E u)-
      h • ((-Complex.I) • lift u (V t)
        ((SourceFamilyHilbert.constant u y) : SourceFamilyHilbert.Hilbert E u))
    rw [lift_coe,lift_coe,lift_coe,← smul_assoc,Complex.real_smul]
    simp only [r,trajectory,UniformSpace.Completion.coe_sub,UniformSpace.Completion.coe_smul]
  rw [← hr,UniformSpace.Completion.norm_coe]
  apply SourceFamilyHilbert.norm_le_of_eventually u r
  filter_upwards [bound] with i hi
  change ‖(V (t+h)).component i x-(V t).component i x-
    ((h : ℂ)*(-Complex.I)) • (V t).component i y‖ ≤ M
  simpa only [← smul_assoc,Complex.real_smul] using hi

theorem lift_generator_remainder {I : Type*} (u : Ultrafilter I)
    (V : ℝ → SourceFamilyOperator.Operator I E) (T : I → E →L[ℂ] E)
    (x y z : E) (t h M : ℝ)
    (returns : ∀ i s, (V s).component i=SourceFiniteUnitary.time (T i) s)
    (bound : ∀ i s, s ∈ Metric.closedBall t ‖h‖ → ‖SourceFiniteUnitary.time (T i) s‖ ≤ M)
    (first : ∀ᶠ i in (u : Filter I), T i x=y)
    (second : ∀ᶠ i in (u : Filter I), T i y=z) :
    ‖lift u (V (t+h)) (SourceFamilyHilbert.embed u x)-
      lift u (V t) (SourceFamilyHilbert.embed u x)-
      h • ((-Complex.I) • lift u (V t) (SourceFamilyHilbert.embed u y))‖ ≤ (M*‖z‖)*‖h‖^2 := by
  apply lift_family_remainder u V x y t h
  filter_upwards [first,second] with i hi hnext
  have he := time_remainder_on_ball (T i) x t h M (bound i)
  rw [hi,hnext] at he
  simpa only [returns] using he
end Finite

-- Keep the 57 generated integrals folded while matching the actual source family.
attribute [irreducible] partialEvolution

open NativeHistoryGrade (Label projection)
local instance labelFintype : Fintype Label := Fintype.ofFinite _

theorem source_compression_grade (F : GaussUnitaryHistory.Index) :
    Commute GaussYukawaGrade.grade (GaussGradedCompression.compression F) := by
  change GaussYukawaGrade.grade * GaussGradedCompression.compression F =
    GaussGradedCompression.compression F * GaussYukawaGrade.grade
  simp only [GaussYukawaGrade.grade, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm]
  exact Finset.sum_congr rfl (fun g _ => congrArg (fun T : H →L[ℂ] H => (g.2.val : ℂ) • T)
    (GaussGradedCompression.compression_commutes F g).eq)

private theorem source_above_spectrum (y : H) (k : ℕ)
    (he : GaussYukawaGrade.grade y=(k : ℂ) • y) (hk : 56 < k) : y=0 := by
  have hp (g : Label) : projection g y=0 := by
    have h := congrArg (fun T : H →L[ℂ] H => T y) (GaussYukawaInteraction.source_grade_left g)
    change projection g (GaussYukawaGrade.grade y)=(g.2.val : ℂ) • projection g y at h
    rw [he, map_smul] at h
    have hz : ((k : ℂ)-(g.2.val : ℂ)) • projection g y=0 := by
      rw [sub_smul, h, sub_self]
    have hn : k ≠ g.2.val := by have hb := g.2.isLt; omega
    have hc : (k : ℂ)-(g.2.val : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
    exact (smul_eq_zero.mp hz).resolve_left hc
  have h := congrArg (fun T : H →L[ℂ] H => T y) NativeHistoryGrade.projection_resolution
  simpa only [sum_apply, hp, Finset.sum_const_zero, one_apply_eq_self] using h.symm

theorem source_homogeneous_zero (T : H →L[ℂ] H) (n : ℕ)
    (he : GaussYukawaGrade.grade*T=T*GaussYukawaGrade.grade+(n : ℂ) • T)
    (hn : 56 < n) : T=0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hp (g : Label) : T (projection g x)=0 := by
    apply source_above_spectrum (T (projection g x)) (g.2.val+n)
    · have h := congrArg (fun A : H →L[ℂ] H => A (projection g x)) he
      have hg := congrArg (fun A : H →L[ℂ] H => A x) (GaussYukawaInteraction.source_grade_right g)
      change GaussYukawaGrade.grade (projection g x)=(g.2.val : ℂ) • projection g x at hg
      change GaussYukawaGrade.grade (T (projection g x))=
        T (GaussYukawaGrade.grade (projection g x))+(n : ℂ) • T (projection g x) at h
      simpa only [hg, map_smul, Nat.cast_add, add_smul] using h
    · omega
  have hx : ∑ g : Label, projection g x=x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun A : H →L[ℂ] H => A x) NativeHistoryGrade.projection_resolution
  rw [← hx, map_sum]
  exact Finset.sum_eq_zero (fun g _ => hp g)

theorem source_finite_prefix_zero (cut order : ℕ) (t : ℝ)
    (F : GaussUnitaryHistory.Index) (long : 56 < order) :
    finitePrefix (GaussGradedCompression.compression F) (cutoff cut) order t=0 :=
  source_homogeneous_zero _ order
    (finitePrefix_homogeneous _ _ _ (source_compression_grade F) (cutoff_raises cut) order t) long

theorem source_terminal_product_zero (cut : ℕ) (t : ℝ) (F : GaussUnitaryHistory.Index) :
    finitePrefix (GaussGradedCompression.compression F) (cutoff cut) 56 t * cutoff cut=0 := by
  have h := homogeneous_product GaussYukawaGrade.grade
    (finitePrefix (GaussGradedCompression.compression F) (cutoff cut) 56 t) (cutoff cut) 56
    (finitePrefix_homogeneous _ _ _ (source_compression_grade F) (cutoff_raises cut) 56 t)
    (cutoff_raises cut)
  apply source_homogeneous_zero _ 57 _ (by norm_num)
  change GaussYukawaGrade.grade * _ - _ * GaussYukawaGrade.grade = (57 : ℂ) • _ at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem source_partialEvolution_derivative (cut : ℕ) (t : ℝ) (F : GaussUnitaryHistory.Index) :
    HasDerivAt (partialEvolution (GaussGradedCompression.compression F) (cutoff cut) 56)
      (partialEvolution (GaussGradedCompression.compression F) (cutoff cut) 56 t *
        ((-Complex.I) • (GaussGradedCompression.compression F+cutoff cut))) t := by
  have h := partialEvolution_derivative (GaussGradedCompression.compression F) (cutoff cut) 56 t
  simpa only [mul_smul_comm, source_terminal_product_zero, smul_zero, sub_zero] using h

theorem source_finite_evolution_return (cut : ℕ) (t : ℝ) (F : GaussUnitaryHistory.Index) :
    partialEvolution (GaussGradedCompression.compression F) (cutoff cut) 56 t =
      SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t :=
  autonomous_evolution_unique _ _ (fun s => source_partialEvolution_derivative cut s F)
    (partialEvolution_initial _ _ 56) t

def sourceEvolutionFamily (cut : ℕ) (t : ℝ) :
    SourceFamilyOperator.Operator GaussUnitaryHistory.Index H where
  component F := SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t
  bounded := ⟨∑ j ∈ Finset.range 57, (|t| * ‖cutoff cut‖)^j, by positivity, fun F x => by
    have hb := partialEvolution_bound (GaussGradedCompression.compression F) (cutoff cut)
      (GaussGradedCompression.compression_selfAdjoint F) 56 t
    rw [source_finite_evolution_return] at hb
    exact ((SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right hb (norm_nonneg x))⟩

def sourceEvolution (cut : ℕ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (sourceEvolutionFamily cut t)

theorem sourceEvolution_zero (cut : ℕ) : sourceEvolution cut 0=1 := by
  apply (lift_congr sourceFilter _ (SourceFamilyOperator.constant 1) ?_).trans
    (lift_identity sourceFilter)
  intro F
  exact SourceFiniteUnitary.time_zero _

theorem sourceEvolution_add (cut : ℕ) (s t : ℝ) :
    sourceEvolution cut (s+t)=sourceEvolution cut s * sourceEvolution cut t := by
  apply (lift_congr sourceFilter _
    (SourceFamilyOperator.comp (sourceEvolutionFamily cut s) (sourceEvolutionFamily cut t)) ?_).trans
    (lift_comp sourceFilter _ _)
  intro F
  exact SourceFiniteUnitary.time_add _ s t

def sourceSharpEvolutionFamily (cut : ℕ) (t : ℝ) :
    SourceFamilyOperator.Operator GaussUnitaryHistory.Index H where
  component F := SourceFiniteUnitary.time
    (GaussGradedCompression.compression F+(cutoff cut).adjoint) t
  bounded := ⟨∑ j ∈ Finset.range 57, (|t| * ‖cutoff cut‖)^j, by positivity, fun F x => by
    apply ((SourceFiniteUnitary.time
      (GaussGradedCompression.compression F+(cutoff cut).adjoint) t).le_opNorm x).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
    rw [← time_sum_adjoint _ _ (GaussGradedCompression.compression_selfAdjoint F),
      ContinuousLinearMap.adjoint.norm_map, ← source_finite_evolution_return]
    simpa only [abs_neg] using partialEvolution_bound
      (GaussGradedCompression.compression F) (cutoff cut)
      (GaussGradedCompression.compression_selfAdjoint F) 56 (-t)⟩

def sourceSharpEvolution (cut : ℕ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (sourceSharpEvolutionFamily cut t)

theorem source_evolution_sharp_pair (cut : ℕ) (t : ℝ) (x y : HistorySpace) :
    inner ℂ (sourceSharpEvolution cut t x) y=inner ℂ x (sourceEvolution cut (-t) y) := by
  apply lift_pair sourceFilter (sourceSharpEvolutionFamily cut t) (sourceEvolutionFamily cut (-t))
  intro F a b
  change inner ℂ (SourceFiniteUnitary.time
    (GaussGradedCompression.compression F+(cutoff cut).adjoint) t a) b = _
  rw [← time_sum_adjoint _ _ (GaussGradedCompression.compression_selfAdjoint F)]
  exact ContinuousLinearMap.adjoint_inner_left
    (SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) (-t)) b a

theorem source_finite_sharp_return (cut : ℕ) (t : ℝ) (F : GaussUnitaryHistory.Index) :
    (sourceSharpEvolutionFamily cut t).component F =
      SourceFiniteUnitary.time (GaussGradedCompression.compression F+(cutoff cut).adjoint) t := rfl

def sourceGrowth (cut : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 57, (T*‖cutoff cut‖)^j

theorem sourceGrowth_mono (cut : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    sourceGrowth cut a ≤ sourceGrowth cut b := by
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hab (norm_nonneg _)) j

theorem source_finite_time_bound (cut : ℕ) (F : GaussUnitaryHistory.Index) (t : ℝ) :
    ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t‖ ≤
      sourceGrowth cut |t| := by
  rw [← source_finite_evolution_return]
  exact partialEvolution_bound _ _ (GaussGradedCompression.compression_selfAdjoint F) 56 t

def sourceFullCore (cut : ℕ) (x : diagonal.domain) : diagonal.domain :=
  ⟨diagonal x+cutoff cut (x : H),
    Core.add_mem (diagonal_invariant x) (cutoff_core_mem cut x)⟩

theorem eventually_full_exact (cut : ℕ) (x : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter GaussUnitaryHistory.Index),
      (GaussGradedCompression.compression F+cutoff cut) (x : H)=(sourceFullCore cut x : H) := by
  filter_upwards [GaussGradedCompression.eventually_exact x] with F hF
  change GaussGradedCompression.compression F (x : H)+cutoff cut (x : H)=_
  rw [hF]
  rfl

def evolutionTrajectory (cut : ℕ) (t : ℝ) (x : H) : SourceFamilyHilbert.Family H sourceFilter :=
  act sourceFilter (sourceEvolutionFamily cut t) (SourceFamilyHilbert.constant sourceFilter x)

theorem sourceEvolution_inclusion (cut : ℕ) (t : ℝ) (x : H) :
    sourceEvolution cut t (GaussUnitaryHistory.inclusion x)=(evolutionTrajectory cut t x : HistorySpace) :=
  lift_coe sourceFilter (sourceEvolutionFamily cut t) (SourceFamilyHilbert.constant sourceFilter x)

theorem source_core_remainder (cut : ℕ) (x : diagonal.domain) (t h : ℝ) :
    ‖sourceEvolution cut (t+h) (GaussUnitaryHistory.inclusion (x : H))-
      sourceEvolution cut t (GaussUnitaryHistory.inclusion (x : H))-
      h • ((-Complex.I) • sourceEvolution cut t
        (GaussUnitaryHistory.inclusion (sourceFullCore cut x : H)))‖ ≤
      (sourceGrowth cut (|t|+‖h‖)*‖(sourceFullCore cut (sourceFullCore cut x) : H)‖)*‖h‖^2 := by
  apply lift_family_remainder sourceFilter (sourceEvolutionFamily cut) (x : H)
    (sourceFullCore cut x : H) t h
  filter_upwards [eventually_full_exact cut x,eventually_full_exact cut (sourceFullCore cut x)] with F hx hnext
  have bound (u : ℝ) (hu : u ∈ Metric.closedBall t ‖h‖) :
      ‖SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) u‖ ≤
        sourceGrowth cut (|t|+‖h‖) := by
    have hd : |u-t| ≤ ‖h‖ := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hu
    have hu' : |u| ≤ |t|+‖h‖ := by
      have ha := abs_add_le (u-t) t
      rw [sub_add_cancel] at ha
      linarith
    exact (source_finite_time_bound cut F u).trans (sourceGrowth_mono cut (abs_nonneg u) hu')
  have he := time_remainder_on_ball (GaussGradedCompression.compression F+cutoff cut)
    (x : H) t h (sourceGrowth cut (|t|+‖h‖)) bound
  rw [hx,hnext] at he
  exact he

theorem source_core_derivative (cut : ℕ) (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => sourceEvolution cut s (GaussUnitaryHistory.inclusion (x : H)))
      ((-Complex.I) • sourceEvolution cut t (GaussUnitaryHistory.inclusion (sourceFullCore cut x : H))) t := by
  rw [hasDerivAt_iff_tendsto]
  let D := ‖(sourceFullCore cut (sourceFullCore cut x) : H)‖
  have hcont : Continuous (fun s : ℝ => sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖) := by
    unfold sourceGrowth
    fun_prop
  have hlim : Filter.Tendsto (fun s : ℝ => sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖)
      (𝓝 t) (𝓝 0) := by simpa only [sub_self,norm_zero,mul_zero] using hcont.tendsto t
  apply squeeze_zero (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun s => ?_) hlim
  have hb := source_core_remainder cut x t (s-t)
  have he := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (norm_nonneg (s-t)))
  have hi : t+(s-t)=s := by ring
  rw [hi] at he
  have scalar : ‖s-t‖⁻¹*((sourceGrowth cut (|t|+‖s-t‖)*D)*‖s-t‖^2)=
      sourceGrowth cut (|t|+‖s-t‖)*D*‖s-t‖ := by
    by_cases hz : ‖s-t‖=0
    · simp [hz]
    · field_simp
  exact he.trans_eq scalar

theorem source_core_smooth (cut : ℕ) (x : diagonal.domain) :
    ContDiff ℝ ∞ (fun t => sourceEvolution cut t (GaussUnitaryHistory.inclusion (x : H))) := by
  rw [contDiff_infty]
  intro n
  induction n generalizing x with
  | zero => exact contDiff_zero.mpr (continuous_iff_continuousAt.mpr
      (fun t => (source_core_derivative cut x t).continuousAt))
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,contDiff_succ_iff_deriv]
    refine ⟨fun t => (source_core_derivative cut x t).differentiableAt, ?_, ?_⟩
    · simp
    · have hd : deriv (fun t => sourceEvolution cut t (GaussUnitaryHistory.inclusion (x : H)))=
          fun t => (-Complex.I) • sourceEvolution cut t (GaussUnitaryHistory.inclusion (sourceFullCore cut x : H)) :=
        funext (fun t => (source_core_derivative cut x t).deriv)
      rw [hd]
      exact (ih (sourceFullCore cut x)).const_smul (-Complex.I)

def sourcePrefixFamily (A : H →L[ℂ] H) (n : ℕ) (t : ℝ) :
    SourceFamilyOperator.Operator GaussUnitaryHistory.Index H where
  component F := finitePrefix (GaussGradedCompression.compression F) A n t
  bounded := ⟨(|t| * ‖A‖)^n, by positivity, fun F x =>
    ((finitePrefix (GaussGradedCompression.compression F) A n t).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right
        (finitePrefix_bound _ A (GaussGradedCompression.compression_selfAdjoint F) n t)
        (norm_nonneg x))⟩

def sourcePrefix (cut order : ℕ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (sourcePrefixFamily (cutoff cut) order t)

def sourceSharpPrefix (cut order : ℕ) (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (sourcePrefixFamily (cutoff cut).adjoint order t)

theorem sourcePrefix_zero_order (cut : ℕ) (t : ℝ) :
    sourcePrefix cut 0 t = GaussGradedUnitary.time t := by
  apply lift_congr
  intro F
  change 1 * SourceFiniteUnitary.time (GaussGradedCompression.compression F) t = _
  exact one_mul _

theorem sourcePrefix_above56 (cut order : ℕ) (t : ℝ) (long : 56 < order) :
    sourcePrefix cut order t=0 := by
  apply (lift_congr sourceFilter _ (SourceFamilyOperator.constant 0) ?_).trans
    (lift_zero sourceFilter)
  intro F
  exact source_finite_prefix_zero cut order t F long

theorem source_cutoff_graph_limit (x y : HistorySpace)
    (h : Filter.Tendsto (fun n : ℕ => reader (cutoff n) x) Filter.atTop (𝓝 y)) :
    reader GaussYukawaOperator.bounded x=reader GaussRadialDomain.inverseRadius y := by
  have hs := (reader GaussRadialDomain.inverseRadius).continuous.tendsto y |>.comp h
  have hnext := h.comp (Filter.tendsto_add_atTop_nat 1)
  have hd := hnext.sub h
  have hr := (tendsto_const_nhds (x := reader GaussYukawaOperator.bounded x)).sub hd
  have he (n : ℕ) : reader GaussRadialDomain.inverseRadius (reader (cutoff n) x)=
      reader GaussYukawaOperator.bounded x-(reader (cutoff (n+1)) x-reader (cutoff n) x) := by
    have hg := congrArg GaussYukawaInteraction.representation (cutoff_graph_residual n)
    simp only [map_mul, map_sub] at hg
    exact congrArg (fun T : HistorySpace →L[ℂ] HistorySpace => T x) hg
  simp only [sub_self, sub_zero] at hr
  exact (tendsto_nhds_unique hs (by simpa only [Function.comp_def, he] using hr)).symm

#print axioms cutoff_graph_residual
#print axioms cutoff_raises
#print axioms cutoff_core_mem
#print axioms orderedIntegral_derivative
#print axioms orderedIntegral_homogeneous
#print axioms finitePrefix_right_derivative
#print axioms finitePrefix_initial
#print axioms finitePrefix_homogeneous
#print axioms finitePrefix_bound
#print axioms sourcePrefix_zero_order
#print axioms sourcePrefix_above56
#print axioms source_partialEvolution_derivative
#print axioms source_finite_evolution_return
#print axioms sourceEvolution_zero
#print axioms sourceEvolution_add
#print axioms source_evolution_sharp_pair
#print axioms source_finite_sharp_return
#print axioms source_cutoff_graph_limit
#print axioms source_core_derivative
#print axioms source_core_smooth
end LowEnergy.FullYSourceCutoffVolterra
