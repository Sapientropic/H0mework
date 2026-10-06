import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCutoffVolterra
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussGradedRetarded

/-! The original independent-dual gauge words descend through the G=0 left
readout of the same cutoff occurrence. No completion or preparation is changed. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace LowEnergy.CanonicalGradedCurrent
open GaussCoreHilbert SourceFamilyOperator
open GaussUnitaryHistory (HistorySpace sourceFilter reader Index)
open NativeHistoryGrade (Label projection)
open FullYSourceCutoffVolterra
open scoped Topology InnerProductSpace
local instance labelFintype : Fintype Label := Fintype.ofFinite _

def sourceLabel : Label := (1, 0)
def sourceProjection : H →L[ℂ] H := projection sourceLabel
def historyProjection : HistorySpace →L[ℂ] HistorySpace := reader sourceProjection

theorem sourceProjection_square : sourceProjection * sourceProjection = sourceProjection := by
  simp only [sourceProjection, NativeHistoryGrade.projection_product, if_true]

theorem historyProjection_square : historyProjection * historyProjection = historyProjection := by
  rw [historyProjection, ← GaussUnitaryHistory.reader_mul, sourceProjection_square]

theorem sourceProjection_grade : sourceProjection * GaussYukawaGrade.grade = 0 := by
  have hz : (sourceLabel.2.val : ℂ) = 0 := by norm_num [sourceLabel]
  have h := GaussYukawaInteraction.source_grade_left sourceLabel
  rw [hz] at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro x
  change (0 : ℂ) • projection sourceLabel x = (0 : H)
  exact zero_smul ℂ _

theorem positive_grade_left_zero (T : H →L[ℂ] H) (n : ℕ)
    (raises : GaussYukawaGrade.grade * T = T * GaussYukawaGrade.grade + (n : ℂ) • T)
    (positive : 0 < n) : sourceProjection * T = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have zero_piece (g : Label) : sourceProjection (T (projection g x)) = 0 := by
    have hg := congrArg (fun A : H →L[ℂ] H => A x)
      (GaussYukawaInteraction.source_grade_right g)
    change GaussYukawaGrade.grade (projection g x) = (g.2.val : ℂ) • projection g x at hg
    have ht := congrArg (fun A : H →L[ℂ] H => sourceProjection (A (projection g x))) raises
    have hz := congrArg (fun A : H →L[ℂ] H => A (T (projection g x))) sourceProjection_grade
    change sourceProjection (GaussYukawaGrade.grade (T (projection g x))) = 0 at hz
    change sourceProjection (GaussYukawaGrade.grade (T (projection g x))) =
      sourceProjection (T (GaussYukawaGrade.grade (projection g x)) + (n : ℂ) • T (projection g x)) at ht
    rw [hz, hg, map_add, map_smul, map_smul, map_smul, ← add_smul] at ht
    have nonzero : (g.2.val : ℂ) + (n : ℂ) ≠ 0 := by
      rw [← Nat.cast_add]
      exact_mod_cast (show g.2.val + n ≠ 0 by omega)
    exact (smul_eq_zero.mp ht.symm).resolve_left nonzero
  have resolution : (∑ g : Label, projection g x) = x := by
    simpa only [sum_apply, one_apply_eq_self] using
      congrArg (fun A : H →L[ℂ] H => A x) NativeHistoryGrade.projection_resolution
  change sourceProjection (T x) = 0
  rw [← resolution, map_sum, map_sum]
  exact Finset.sum_eq_zero (fun g _ => zero_piece g)

theorem finite_prefix_left_zero (cut n : ℕ) (t : ℝ) (F : Index) (positive : 0 < n) :
    sourceProjection * finitePrefix (GaussGradedCompression.compression F) (cutoff cut) n t = 0 :=
  positive_grade_left_zero _ n
    (finitePrefix_homogeneous _ _ _ (source_compression_grade F) (cutoff_raises cut) n t) positive

theorem finite_partial_left_return (cut n : ℕ) (t : ℝ) (F : Index) :
    sourceProjection * partialEvolution (GaussGradedCompression.compression F) (cutoff cut) n t =
      sourceProjection * SourceFiniteUnitary.time (GaussGradedCompression.compression F) t := by
  induction n with
  | zero => rw [partialEvolution]
  | succ n ih =>
    rw [partialEvolution, mul_add, ih, finite_prefix_left_zero cut (n+1) t F (by omega), add_zero]

theorem finite_left_return (cut : ℕ) (t : ℝ) (F : Index) :
    sourceProjection * (sourceEvolutionFamily cut t).component F =
      sourceProjection * (GaussGradedUnitary.finiteTime t).component F := by
  change sourceProjection * SourceFiniteUnitary.time
    (GaussGradedCompression.compression F + cutoff cut) t = _
  rw [← source_finite_evolution_return]
  exact finite_partial_left_return cut 56 t F

theorem cutoff_left_return (cut : ℕ) (t : ℝ) :
    historyProjection * sourceEvolution cut t = historyProjection * GaussGradedUnitary.time t := by
  change lift sourceFilter (constant sourceProjection) * lift sourceFilter (sourceEvolutionFamily cut t) =
    lift sourceFilter (constant sourceProjection) * lift sourceFilter (GaussGradedUnitary.finiteTime t)
  calc
    _ = lift sourceFilter (comp (constant sourceProjection) (sourceEvolutionFamily cut t)) :=
      (lift_comp sourceFilter _ _).symm
    _ = lift sourceFilter (comp (constant sourceProjection) (GaussGradedUnitary.finiteTime t)) :=
      lift_congr sourceFilter _ _ (finite_left_return cut t)
    _ = _ := lift_comp sourceFilter _ _

theorem time_projection (t : ℝ) :
    historyProjection * GaussGradedUnitary.time t = GaussGradedUnitary.time t * historyProjection :=
  GaussGradedUnitary.time_blocks t sourceLabel

theorem projection_pair (x y : HistorySpace) :
    inner ℂ (historyProjection x) y = inner ℂ x (historyProjection y) :=
  GaussGradedRetarded.projection_pair sourceLabel x y

theorem diagonal_time_pair (t : ℝ) (x y : HistorySpace) :
    inner ℂ (GaussGradedUnitary.time t x) y = inner ℂ x (GaussGradedUnitary.time (-t) y) := by
  apply lift_pair sourceFilter (GaussGradedUnitary.finiteTime t) (GaussGradedUnitary.finiteTime (-t))
  intro F a b
  change inner ℂ (SourceFiniteUnitary.time (GaussGradedCompression.compression F) t a) b =
    inner ℂ a (SourceFiniteUnitary.time (GaussGradedCompression.compression F) (-t) b)
  have ha := time_adjoint (GaussGradedCompression.compression F) t
  rw [(GaussGradedCompression.compression_selfAdjoint F).adjoint_eq] at ha
  rw [← ha]
  exact ((SourceFiniteUnitary.time (GaussGradedCompression.compression F) t).adjoint_inner_right a b).symm

theorem cutoff_sharp_on_source (cut : ℕ) (t : ℝ) (x : HistorySpace) :
    sourceSharpEvolution cut t (historyProjection x) =
      GaussGradedUnitary.time t (historyProjection x) := by
  apply ext_inner_right ℂ
  intro y
  rw [source_evolution_sharp_pair, diagonal_time_pair, projection_pair, projection_pair]
  exact congrArg (inner ℂ x)
    (congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A y) (cutoff_left_return cut (-t)))

private theorem left_fold_return {R : Type*} [Monoid R] (P : R) (U V : ℝ → R)
    (returns : ∀ t, P * U t = P * V t) (time_preserves : ∀ t, P * V t = V t * P)
    (word : List (ℝ × R)) (preserves : ∀ item ∈ word, Commute P item.2) :
    P * word.foldr (fun item tail => U item.1 * item.2 * tail) 1 =
      P * word.foldr (fun item tail => V item.1 * item.2 * tail) 1 := by
  induction word with
  | nil => rfl
  | cons item tail ih =>
    obtain ⟨t,A⟩ := item
    have ha := (preserves (t,A) (by simp)).eq
    have htail := ih (fun item hi => preserves item (by simp [hi]))
    simp only [List.foldr_cons]
    calc
      _ = (P * U t) * A * tail.foldr (fun item rest => U item.1 * item.2 * rest) 1 := by simp only [mul_assoc]
      _ = (P * V t) * A * tail.foldr (fun item rest => U item.1 * item.2 * rest) 1 := by rw [returns]
      _ = V t * A * (P * tail.foldr (fun item rest => U item.1 * item.2 * rest) 1) := by
        rw [time_preserves, mul_assoc (V t) P A, ha]
        simp only [mul_assoc]
      _ = V t * A * (P * tail.foldr (fun item rest => V item.1 * item.2 * rest) 1) := by rw [htail]
      _ = _ := by
        symm
        calc
          _ = (P * V t) * A * tail.foldr (fun item rest => V item.1 * item.2 * rest) 1 := by simp only [mul_assoc]
          _ = _ := by
            rw [time_preserves, mul_assoc (V t) P A, ha]
            simp only [mul_assoc]

def cutoffWord (cut : ℕ) (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace))) :
    HistorySpace →L[ℂ] HistorySpace :=
  word.foldr (fun item tail => sourceEvolution cut item.1 * item.2 * tail) 1

def diagonalWord (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace))) :
    HistorySpace →L[ℂ] HistorySpace :=
  word.foldr (fun item tail => GaussGradedUnitary.time item.1 * item.2 * tail) 1

theorem gauge_word_return (cut : ℕ) (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)))
    (preserves : ∀ item ∈ word, Commute historyProjection item.2) :
    historyProjection * cutoffWord cut word = historyProjection * diagonalWord word :=
  left_fold_return historyProjection (sourceEvolution cut) GaussGradedUnitary.time
    (cutoff_left_return cut) time_projection word preserves

def cutoffObservation (cut : ℕ) (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)))
    (x y : HistorySpace) : ℂ :=
  inner ℂ (historyProjection x) (cutoffWord cut word (historyProjection y))

def diagonalObservation (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)))
    (x y : HistorySpace) : ℂ :=
  inner ℂ (historyProjection x) (diagonalWord word (historyProjection y))

theorem observable_return (cut : ℕ) (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)))
    (preserves : ∀ item ∈ word, Commute historyProjection item.2) (x y : HistorySpace) :
    cutoffObservation cut word x y = diagonalObservation word x y := by
  unfold cutoffObservation diagonalObservation
  rw [projection_pair, projection_pair]
  exact congrArg (inner ℂ x) (congrArg (fun A : HistorySpace →L[ℂ] HistorySpace =>
    A (historyProjection y)) (gauge_word_return cut word preserves))

theorem observable_cutoff_limit (word : List (ℝ × (HistorySpace →L[ℂ] HistorySpace)))
    (preserves : ∀ item ∈ word, Commute historyProjection item.2) (x y : HistorySpace) :
    Filter.Tendsto (fun cut : ℕ => cutoffObservation cut word x y) Filter.atTop
      (𝓝 (diagonalObservation word x y)) := by
  simp only [observable_return _ word preserves x y]
  exact tendsto_const_nhds

#print axioms cutoff_left_return
#print axioms cutoff_sharp_on_source
#print axioms gauge_word_return
#print axioms observable_cutoff_limit
end LowEnergy.CanonicalGradedCurrent
