import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumGradeTransport
import H0mework.Physics.LowEnergy.Quantum.WeakCoreEvolution
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussHistoryHilbert
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussHalfDensity
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The original full-Fock grade resolution used by the history consumer. -/
set_option autoImplicit false
noncomputable section
namespace LowEnergy.NativeHistoryGrade
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open SourceGradeTransport
open scoped BigOperators InnerProductSpace
attribute [local instance] modeOrder

abbrev HistoryHilbert := GaussHistoryHilbert.FockHilbert

def sourceGrade (word : Occupation) : Fin 57 :=
  ⟨count target word, by have h := count_le target word; rw [target_card] at h; omega⟩

def sourceNumber (word : Occupation) : Fin 505 :=
  ⟨word.card, by have h := Finset.card_le_univ word; rw [full_mode_card] at h; omega⟩

abbrev Label := Fin 505 × Fin 57

-- Keep the full resolution symbolic instead of reducing 28,785 labels.
local instance labelFintype : Fintype Label := Fintype.ofFinite _

def sourceLabel (word : Occupation) : Label := (sourceNumber word, sourceGrade word)

def piece (g : Label) (f : HistoryHilbert) : HistoryHilbert :=
  WithLp.toLp 2 (fun word => if sourceLabel word = g then f word else 0)

@[simp] theorem piece_apply (g : Label) (f : HistoryHilbert) (word : Occupation) :
    piece g f word = if sourceLabel word = g then f word else 0 := rfl

theorem piece_bound (g : Label) (f : HistoryHilbert) : ‖piece g f‖ ≤ ‖f‖ := by
  have h : ‖piece g f‖^2 ≤ ‖f‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro word _
    by_cases hg : sourceLabel word = g
    · simp [hg]
    · simp [hg]
  nlinarith [norm_nonneg (piece g f), norm_nonneg f]

def projection (g : Label) : HistoryHilbert →L[ℂ] HistoryHilbert :=
  (show HistoryHilbert →ₗ[ℂ] HistoryHilbert from {
    toFun := piece g
    map_add' := by
      intro f h
      ext word
      by_cases hg : sourceLabel word = g <;> simp [hg]
    map_smul' := by
      intro c f
      ext word
      by_cases hg : sourceLabel word = g <;> simp [hg] }).mkContinuous 1
    (fun f => by change ‖piece g f‖ ≤ 1*‖f‖; simpa only [one_mul] using piece_bound g f)

@[simp] theorem projection_apply (g : Label) (f : HistoryHilbert) (word : Occupation) :
    projection g f word = if sourceLabel word = g then f word else 0 := rfl

theorem projection_symmetric (g : Label) : (projection g).toLinearMap.IsSymmetric := by
  intro f h
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hg : sourceLabel word = g <;> simp [hg]

theorem projection_product (g h : Label) :
    projection g * projection h = if g = h then projection g else 0 := by
  ext f word
  by_cases equal : g = h
  · subst h
    by_cases hg : sourceLabel word = g <;> simp [hg]
  · by_cases hg : sourceLabel word = g <;> by_cases hh : sourceLabel word = h <;>
      simp_all

theorem projection_resolution : ∑ g : Label, projection g = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  simp [sum_apply, WithLp.ofLp_sum, Finset.sum_apply, projection_apply, eq_comm]

theorem projection_preserves_core (g : Label) (f : HistoryHilbert) (hf : f ∈ GaussHistoryHilbert.fockTestDomain) :
    projection g f ∈ GaussHistoryHilbert.fockTestDomain := by
  intro word
  by_cases hg : sourceLabel word = g
  · simpa only [projection_apply, if_pos hg] using hf word
  · simp only [projection_apply, if_neg hg]
    exact (GaussHistoryHilbert.testDomain word.card).zero_mem

theorem sum_projection_apply (f : Label → HistoryHilbert) (word : Occupation) :
    (∑ g, projection g (f g)) word = f (sourceLabel word) word := by
  simp [WithLp.ofLp_sum, Finset.sum_apply, projection_apply, eq_comm]

theorem norm_sum_projection (f : Label → HistoryHilbert) :
    ‖∑ g, projection g (f g)‖^2 = ∑ g, ‖projection g (f g)‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [sum_projection_apply]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  simp [projection_apply, apply_ite, eq_comm]

theorem norm_resolution (f : HistoryHilbert) : ∑ g, ‖projection g f‖^2 = ‖f‖^2 := by
  rw [← norm_sum_projection (fun _ => f), ← sum_apply, projection_resolution, one_apply_eq_self]

open SymmetricGraphClosure WeakCoreEvolution

def history (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) : HistoryHilbert →L[ℂ] HistoryHilbert :=
  ∑ g : Label, projection g * weakEvolution T symmetric t * projection g

theorem history_apply (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (f : HistoryHilbert) :
    history T symmetric t f = ∑ g, projection g (weakEvolution T symmetric t (projection g f)) := by
  simp [history, sum_apply]

theorem history_contraction (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (f : HistoryHilbert) : ‖history T symmetric t f‖ ≤ ‖f‖ := by
  have hb (g : Label) :
      ‖projection g (weakEvolution T symmetric t (projection g f))‖ ≤ ‖projection g f‖ := by
    have hp := piece_bound g (weakEvolution T symmetric t (projection g f))
    exact hp.trans (weak_evolution_contraction T symmetric t (projection g f))
  have hs : ‖history T symmetric t f‖^2 ≤ ‖f‖^2 := by
    rw [history_apply, norm_sum_projection, ← norm_resolution f]
    apply Finset.sum_le_sum
    intro g _
    exact pow_le_pow_left₀ (norm_nonneg _) (hb g) 2
  nlinarith [norm_nonneg (history T symmetric t f), norm_nonneg f]

theorem history_zero (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T) :
    history T symmetric 0 = 1 := by
  simpa only [history, weak_evolution_zero, mul_one, projection_product, if_true] using projection_resolution

theorem history_left_block (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (g : Label) : projection g * history T symmetric t =
      projection g * weakEvolution T symmetric t * projection g := by
  calc
    projection g * history T symmetric t = ∑ h : Label,
        (projection g * projection h) * weakEvolution T symmetric t * projection h := by
      simp [history, Finset.mul_sum, mul_assoc]
    _ = _ := by simp [projection_product, ite_mul]

theorem history_right_block (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) (g : Label) : history T symmetric t * projection g =
      projection g * weakEvolution T symmetric t * projection g := by
  calc
    history T symmetric t * projection g = ∑ h : Label,
        projection h * weakEvolution T symmetric t * (projection h * projection g) := by
      simp [history, Finset.sum_mul, mul_assoc]
    _ = _ := by simp [projection_product, mul_ite]

theorem history_continuous (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (dense : Dense (T.domain : Set HistoryHilbert)) (f : HistoryHilbert) :
    Continuous (fun t => history T symmetric t f) := by
  simp only [history_apply]
  exact continuous_finsetSum _ (fun g _ => (projection g).continuous.comp
    (weak_evolution_continuous T symmetric dense (projection g f)))

set_option maxHeartbeats 1500000 in
theorem history_core_derivative (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert)
    (symmetric : FormalAdjointPair T T)
    (stable : ∀ (g : Label) (x : T.domain), projection g (x : HistoryHilbert) ∈ T.domain)
    (commutes : ∀ (g : Label) (x : T.domain),
      T ⟨projection g (x : HistoryHilbert), stable g x⟩ = projection g (T x))
    (x : T.domain) (hTx : T x ∈ T.domain) (t : ℝ) :
    HasDerivAt (fun u => history T symmetric u (x : HistoryHilbert))
      ((-Complex.I) • history T symmetric t (T x)) t := by
  have hd (g : Label) :
      HasDerivAt (fun u => projection g (weakEvolution T symmetric u (projection g x)))
        ((-Complex.I) • projection g (weakEvolution T symmetric t (projection g (T x)))) t := by
    let px : T.domain := ⟨projection g (x : HistoryHilbert), stable g x⟩
    have hpx : T px ∈ T.domain := by
      rw [show T px = projection g (T x) from commutes g x]
      exact stable g ⟨T x, hTx⟩
    let P := (projection g).restrictScalars ℝ
    have h := P.hasFDerivAt.comp_hasDerivAt t (weak_evolution_core_derivative T symmetric px hpx t)
    change HasDerivAt (fun u => projection g (weakEvolution T symmetric u (projection g x)))
      (projection g ((-Complex.I) • weakEvolution T symmetric t (T px))) t at h
    rw [map_smul, show T px = projection g (T x) from commutes g x] at h
    exact h
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun g _ => hd g)
  simpa only [history_apply, Finset.smul_sum] using h

set_option maxHeartbeats 1500000 in
theorem history_original_pairing (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert)
    (symmetric : FormalAdjointPair T T)
    (stable : ∀ (g : Label) (x : T.domain), projection g (x : HistoryHilbert) ∈ T.domain)
    (commutes : ∀ (g : Label) (x : T.domain),
      T ⟨projection g (x : HistoryHilbert), stable g x⟩ = projection g (T x))
    (x y : T.domain) (hTx : T x ∈ T.domain) (hTy : T y ∈ T.domain) (t : ℝ) :
    inner ℂ (history T symmetric t (x : HistoryHilbert)) (T y) =
      inner ℂ (history T symmetric t (T x)) (y : HistoryHilbert) := by
  rw [history_apply, history_apply, sum_inner, sum_inner]
  apply Finset.sum_congr rfl
  intro g _
  let px : T.domain := ⟨projection g (x : HistoryHilbert), stable g x⟩
  let py : T.domain := ⟨projection g (y : HistoryHilbert), stable g y⟩
  have hpx : T px ∈ T.domain := by
    rw [show T px = projection g (T x) from commutes g x]
    exact stable g ⟨T x, hTx⟩
  have hpy : T py ∈ T.domain := by
    rw [show T py = projection g (T y) from commutes g y]
    exact stable g ⟨T y, hTy⟩
  calc
    inner ℂ (projection g (weakEvolution T symmetric t (projection g x))) (T y) =
        inner ℂ (weakEvolution T symmetric t (projection g x)) (projection g (T y)) :=
      projection_symmetric g _ _
    _ = inner ℂ (weakEvolution T symmetric t (px : HistoryHilbert)) (T py) := by
      rw [show T py = projection g (T y) from commutes g y]
    _ = inner ℂ (weakEvolution T symmetric t (T px)) (py : HistoryHilbert) :=
      weak_evolution_original_pairing T symmetric px py hpx hpy t
    _ = inner ℂ (projection g (weakEvolution T symmetric t (projection g (T x)))) (y : HistoryHilbert) := by
      rw [show T px = projection g (T x) from commutes g x]
      exact (projection_symmetric g _ _).symm

set_option maxHeartbeats 1500000 in
theorem history_retarded_identity (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert)
    (symmetric : FormalAdjointPair T T) (dense : Dense (T.domain : Set HistoryHilbert))
    (stable : ∀ (g : Label) (x : T.domain), projection g (x : HistoryHilbert) ∈ T.domain)
    (commutes : ∀ (g : Label) (x : T.domain),
      T ⟨projection g (x : HistoryHilbert), stable g x⟩ = projection g (T x))
    (x y : T.domain) (hTx : T x ∈ T.domain) (hTy : T y ∈ T.domain)
    (eta eta' : ℝ → ℂ) (differentiable : ∀ t, HasDerivAt eta (eta' t) t)
    (derivative_continuous : Continuous eta') (b : NNReal) (end_zero : eta b = 0) :
    (∫ t in (0 : ℝ)..(b : ℝ),
      eta' t * inner ℂ (history T symmetric t (x : HistoryHilbert)) (y : HistoryHilbert) +
      eta t * (Complex.I * inner ℂ (history T symmetric t (x : HistoryHilbert)) (T y))) =
      -eta 0 * inner ℂ (x : HistoryHilbert) (y : HistoryHilbert) := by
  let c := fun t => inner ℂ (history T symmetric t (x : HistoryHilbert)) (y : HistoryHilbert)
  let k := fun t => inner ℂ (history T symmetric t (x : HistoryHilbert)) (T y)
  have hc : Continuous c := (history_continuous T symmetric dense (x : HistoryHilbert)).inner continuous_const
  have hk : Continuous k := (history_continuous T symmetric dense (x : HistoryHilbert)).inner continuous_const
  have he : Continuous eta := continuous_iff_continuousAt.mpr
    (fun t => (differentiable t).continuousAt)
  have hd (t : ℝ) : HasDerivAt (fun u => eta u * c u)
      (eta' t*c t+eta t*(Complex.I*k t)) t := by
    have hp := (history_core_derivative T symmetric stable commutes x hTx t).inner ℂ
      (hasDerivAt_const t (y : HistoryHilbert))
    have hpair : HasDerivAt c (Complex.I*k t) t := by
      simpa [c, k, inner_smul_left,
        ← history_original_pairing T symmetric stable commutes x y hTx hTy t] using hp
    exact (differentiable t).mul hpair
  have integrable := ((derivative_continuous.mul hc).add
    (he.mul ((continuous_const : Continuous (fun _ : ℝ => Complex.I)).mul hk))).intervalIntegrable
      (μ := MeasureTheory.volume) 0 (b : ℝ)
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) integrable
  simpa only [c, k, end_zero, zero_mul, history_zero, one_apply_eq_self, zero_sub,
    neg_mul] using identity

def flatHistory (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert) (symmetric : FormalAdjointPair T T)
    (t : ℝ) : GaussHalfDensity.FlatFockHilbert →L[ℂ] GaussHalfDensity.FlatFockHilbert :=
  GaussHalfDensity.fockHalfDensityEquiv.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((history T symmetric t).comp
      GaussHalfDensity.fockHalfDensityEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem flatHistory_contraction (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert)
    (symmetric : FormalAdjointPair T T) (t : ℝ) (f : GaussHalfDensity.FlatFockHilbert) :
    ‖flatHistory T symmetric t f‖ ≤ ‖f‖ := by
  change ‖GaussHalfDensity.fockHalfDensityEquiv (history T symmetric t
    (GaussHalfDensity.fockHalfDensityEquiv.symm f))‖ ≤ ‖f‖
  rw [LinearIsometryEquiv.norm_map]
  exact (history_contraction T symmetric t _).trans_eq
    (GaussHalfDensity.fockHalfDensityEquiv.symm.norm_map f)

theorem flatHistory_pairing (T : HistoryHilbert →ₗ.[ℂ] HistoryHilbert)
    (symmetric : FormalAdjointPair T T) (t : ℝ) (f g : HistoryHilbert) :
    inner ℂ (GaussHalfDensity.fockHalfDensityEquiv f)
      (flatHistory T symmetric t (GaussHalfDensity.fockHalfDensityEquiv g)) =
      inner ℂ f (history T symmetric t g) := by
  change inner ℂ (GaussHalfDensity.fockHalfDensityEquiv f)
    (GaussHalfDensity.fockHalfDensityEquiv (history T symmetric t
      (GaussHalfDensity.fockHalfDensityEquiv.symm (GaussHalfDensity.fockHalfDensityEquiv g)))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]

#print axioms projection_symmetric
#print axioms projection_product
#print axioms projection_resolution
#print axioms projection_preserves_core
#print axioms history_contraction
#print axioms history_zero
#print axioms history_left_block
#print axioms history_right_block
#print axioms history_continuous
#print axioms history_core_derivative
#print axioms history_original_pairing
#print axioms history_retarded_identity
#print axioms flatHistory_pairing
end LowEnergy.NativeHistoryGrade
