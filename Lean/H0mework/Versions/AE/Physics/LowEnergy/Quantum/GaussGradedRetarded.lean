import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussGradedUnitary

/-! The common graded time has its own source-generated retarded observation. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussGradedRetarded
open GaussCoreHilbert GaussDiagonalHistory GaussGradedUnitary SourceFamilyOperator Filter
open GaussUnitaryHistory (Index HistorySpace sourceFilter inclusion reader)
open SourceFamilyHilbert (inner_coe pair_tendsto)
open NativeHistoryGrade (Label projection)
open scoped Topology InnerProductSpace Interval

def inclusionMap : H →L[ℂ] HistorySpace := inclusion.toContinuousLinearMap
def shadow (t : ℝ) : H →L[ℂ] H := inclusionMap.adjoint.comp ((time t).comp inclusionMap)

theorem shadow_apply (t : ℝ) (x : H) :
    shadow t x = inclusionMap.adjoint (time t (inclusion x)) := rfl

theorem shadow_pair (t : ℝ) (x y : H) :
    inner ℂ (shadow t x) y = inner ℂ (time t (inclusion x)) (inclusion y) :=
  ContinuousLinearMap.adjoint_inner_left inclusionMap y (time t (inclusion x))

theorem shadow_zero : shadow 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [shadow_pair, time_zero, one_apply_eq_self, one_apply_eq_self]
  exact inclusion.inner_map_map x y

theorem shadow_continuous (x : H) : Continuous (fun t => shadow t x) :=
  inclusionMap.adjoint.continuous.comp (source_continuous x)

theorem shadow_derivative (x : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => shadow s (x : H)) ((-Complex.I) • shadow t (diagonal x)) t := by
  have h := inclusionMap.adjoint.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt t (core_derivative x t)
  change HasDerivAt (fun s => shadow s (x : H))
    (inclusionMap.adjoint ((-Complex.I) • time t (inclusion (diagonal x)))) t at h
  simpa only [map_smul, shadow_apply] using h

theorem projection_pair (g : Label) (x y : HistorySpace) :
    inner ℂ (reader (projection g) x) y = inner ℂ x (reader (projection g) y) :=
  lift_pair sourceFilter (constant (projection g)) (constant (projection g))
    (fun _ => NativeHistoryGrade.projection_symmetric g) x y

private theorem compressed_pair {X K : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (J : X →L[ℂ] K) (P : X →L[ℂ] X) (Q U : K →L[ℂ] K)
    (hp : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y))
    (hq : ∀ x y, inner ℂ (Q x) y = inner ℂ x (Q y))
    (hJ : ∀ x, Q (J x) = J (P x)) (hU : ∀ z, Q (U z) = U (Q z)) (x y : X) :
    inner ℂ (P (J.adjoint (U (J x)))) y = inner ℂ (J.adjoint (U (J (P x)))) y := by
  calc
    _ = inner ℂ (J.adjoint (U (J x))) (P y) := hp _ _
    _ = inner ℂ (U (J x)) (J (P y)) := J.adjoint_inner_left _ _
    _ = inner ℂ (U (J x)) (Q (J y)) := by rw [hJ]
    _ = inner ℂ (Q (U (J x))) (J y) := (hq _ _).symm
    _ = inner ℂ (U (J (P x))) (J y) := by rw [hU, hJ]
    _ = _ := (J.adjoint_inner_left _ _).symm

theorem shadow_blocks (t : ℝ) (g : Label) : projection g * shadow t = shadow t * projection g := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  exact compressed_pair inclusionMap (projection g) (reader (projection g)) (time t)
    (NativeHistoryGrade.projection_symmetric g) (projection_pair g)
    (GaussUnitaryHistory.reader_inclusion (projection g))
    (fun z => congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A z) (time_blocks t g)) x y

theorem shadow_pair_limit (t : ℝ) (x y : H) :
    Tendsto (fun F : Index => inner ℂ
      (SourceFiniteUnitary.time (GaussGradedCompression.compression F) t x) y)
      sourceFilter (𝓝 (inner ℂ (shadow t x) y)) := by
  rw [shadow_pair, time_inclusion]
  change Tendsto _ _ (𝓝 (inner ℂ (trajectory t x : HistorySpace)
    ((SourceFamilyHilbert.constant sourceFilter y) : HistorySpace)))
  rw [inner_coe]
  exact pair_tendsto sourceFilter (trajectory t x) (SourceFamilyHilbert.constant sourceFilter y)

theorem shadow_left_equation (x y : diagonal.domain) (t : ℝ) :
    inner ℂ (shadow t (x : H)) (diagonal y) = inner ℂ (shadow t (diagonal x)) (y : H) := by
  apply tendsto_nhds_unique (shadow_pair_limit t (x : H) (diagonal y))
  apply (shadow_pair_limit t (diagonal x) (y : H)).congr'
  filter_upwards [GaussGradedCompression.eventually_exact x,
    GaussGradedCompression.eventually_exact y] with F hx hy
  let C := GaussGradedCompression.compression F
  let U := SourceFiniteUnitary.time C t
  have comm : U (C (x : H)) = C (U (x : H)) :=
    (congrArg (fun A : H →L[ℂ] H => A (x : H))
      (SourceFiniteUnitary.time_commutes C C (Commute.refl C) t).eq).symm
  calc
    inner ℂ (U (diagonal x)) (y : H) = inner ℂ (U (C (x : H))) (y : H) := by rw [hx]
    _ = inner ℂ (C (U (x : H))) (y : H) := by rw [comm]
    _ = inner ℂ (U (x : H)) (C (y : H)) := GaussGradedCompression.compression_pair F _ _
    _ = inner ℂ (U (x : H)) (diagonal y) := by rw [hy]

theorem shadow_pair_derivative (x y : diagonal.domain) (t : ℝ) :
    HasDerivAt (fun s => inner ℂ (shadow s (x : H)) (y : H))
      (Complex.I * inner ℂ (shadow t (x : H)) (diagonal y)) t := by
  have h := (shadow_derivative x t).inner ℂ (hasDerivAt_const t (y : H))
  simpa [inner_smul_left, ← shadow_left_equation x y t] using h

theorem retarded_source (x y : diagonal.domain) (eta eta' : ℝ → ℂ)
    (differentiable : ∀ t, HasDerivAt eta (eta' t) t) (derivative_continuous : Continuous eta')
    (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * inner ℂ (shadow t (x : H)) (y : H) +
      eta t * (Complex.I * inner ℂ (shadow t (x : H)) (diagonal y))) =
      -eta 0 * inner ℂ (x : H) (y : H) := by
  let c := fun t => inner ℂ (shadow t (x : H)) (y : H)
  let k := fun t => inner ℂ (shadow t (x : H)) (diagonal y)
  have hc : Continuous c := (shadow_continuous (x : H)).inner continuous_const
  have hk : Continuous k := (shadow_continuous (x : H)).inner continuous_const
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*(Complex.I*k t)) t :=
    (differentiable t).mul (shadow_pair_derivative x y t)
  have integrable := ((derivative_continuous.mul hc).add
    (he.mul ((continuous_const : Continuous (fun _ : ℝ => Complex.I)).mul hk))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, shadow_zero, one_apply_eq_self, zero_sub, neg_mul] using identity

#print axioms shadow_blocks
#print axioms shadow_derivative
#print axioms shadow_left_equation
#print axioms retarded_source
end LowEnergy.GaussGradedRetarded
