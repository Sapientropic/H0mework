import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedMixed
import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalGradedVariation

/-! The selected mixed words remain the original completed operators. All
finite sums and products are transported through the same source filter. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedMixedReturn
open GaussCoreHilbert CanonicalGradedCurrent CanonicalGradedMixed
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader)
open FullYSourceCutoffVolterra SourceFamilyOperator
open scoped BigOperators

private def sumFamily {ι : Type*} (S : Finset ι) (A : ι → SourceFamilyOperator.Operator Index H) :
    SourceFamilyOperator.Operator Index H where
  component F := ∑ i ∈ S, (A i).component F
  bounded := ⟨∑ i ∈ S, bound (A i), Finset.sum_nonneg (fun i _ => bound_nonneg (A i)), fun F x => by
    rw [sum_apply]
    calc
      _ ≤ ∑ i ∈ S, ‖(A i).component F x‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ S, bound (A i)*‖x‖ := Finset.sum_le_sum (fun i _ => bound_apply (A i) F x)
      _ = _ := (Finset.sum_mul _ _ _).symm⟩

private theorem lift_sum {ι : Type*} (S : Finset ι) (A : ι → SourceFamilyOperator.Operator Index H) :
    lift sourceFilter (sumFamily S A)=∑ i ∈ S, lift sourceFilter (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have h := lift_congr sourceFilter (sumFamily ∅ A) (constant 0)
      (fun _ => by simp only [sumFamily, Finset.sum_empty, constant])
    simpa only [Finset.sum_empty, lift_zero] using h
  | @insert i S hi ih =>
    have h := lift_congr sourceFilter (sumFamily (insert i S) A) (add (A i) (sumFamily S A))
      (fun _ => by simp only [sumFamily, Finset.sum_insert hi, add])
    rw [lift_add, ih] at h
    rw [Finset.sum_insert hi]
    exact h

private def wordFamily (P : SourceFamilyOperator.Operator Index H)
    (U V W : SourceFamilyOperator.Operator Index H) (A B : H →L[ℂ] H) :
    SourceFamilyOperator.Operator Index H :=
  comp (comp (comp (comp (comp (comp P U) (constant A)) V) (constant B)) W) P

private theorem lift_wordFamily (P U V W : SourceFamilyOperator.Operator Index H) (A B : H →L[ℂ] H) :
    lift sourceFilter (wordFamily P U V W A B)=
      lift sourceFilter P*lift sourceFilter U*reader A*lift sourceFilter V*reader B*
        lift sourceFilter W*lift sourceFilter P := by
  simp only [wordFamily, lift_comp]
  rfl

def fullWord (cut : ℕ) (A B : H →L[ℂ] H) (r s t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  historyProjection*sourceEvolution cut r*reader A*sourceEvolution cut s*reader B*
    sourceEvolution cut t*historyProjection

def wordTerm (cut : ℕ) (A B : H →L[ℂ] H) (r s t : ℝ) (i j k : ℕ) : HistorySpace →L[ℂ] HistorySpace :=
  historyProjection*sourcePrefix cut i r*reader A*sourcePrefix cut j s*reader B*
    sourcePrefix cut k t*historyProjection

def selectedWord (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ) (r s t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
    if (i : ℤ)+a+j+b+k=0 then wordTerm cut A B r s t i j k else 0

private def selectedFamily (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ) (r s t : ℝ) :
    SourceFamilyOperator.Operator Index H :=
  sumFamily (Finset.range 3) (fun i => sumFamily (Finset.range 3) (fun j =>
    sumFamily (Finset.range 3) (fun k => if (i : ℤ)+a+j+b+k=0 then
      wordFamily (constant sourceProjection) (sourcePrefixFamily (cutoff cut) i r)
        (sourcePrefixFamily (cutoff cut) j s) (sourcePrefixFamily (cutoff cut) k t) A B
      else constant 0)))

private theorem selectedFamily_component (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ)
    (r s t : ℝ) (F : Index) :
    (selectedFamily cut A B a b r s t).component F=CanonicalGradedMixed.selectedWord cut A B a b r s t F := by
  unfold selectedFamily CanonicalGradedMixed.selectedWord
  simp only [sumFamily]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · rfl
  · rfl

private theorem selectedFamily_lift (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ) (r s t : ℝ) :
    lift sourceFilter (selectedFamily cut A B a b r s t)=selectedWord cut A B a b r s t := by
  unfold selectedFamily selectedWord
  simp only [lift_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact lift_wordFamily _ _ _ _ A B
  · exact lift_zero sourceFilter

theorem fullWord_selected (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (lowerA : -1≤a) (lowerB : -1≤b) (r s t : ℝ) :
    fullWord cut A B r s t=selectedWord cut A B a b r s t := by
  have h := lift_congr sourceFilter
    (wordFamily (constant sourceProjection) (sourceEvolutionFamily cut r)
      (sourceEvolutionFamily cut s) (sourceEvolutionFamily cut t) A B)
    (selectedFamily cut A B a b r s t) (fun F => by
      rw [selectedFamily_component]
      exact CanonicalGradedMixed.fullWord_selected cut A B a b ha hb lowerA lowerB r s t F)
  rw [selectedFamily_lift, lift_wordFamily] at h
  exact h

private theorem projection_norm : ‖historyProjection‖≤1 := by
  apply CanonicalGradedVariation.lift_bound sourceFilter (constant sourceProjection) 1 zero_le_one
  intro F
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖NativeHistoryGrade.piece sourceLabel x‖ ≤ 1*‖x‖
  simpa only [one_mul] using NativeHistoryGrade.piece_bound sourceLabel x

private theorem reader_norm (A : H →L[ℂ] H) : ‖reader A‖≤‖A‖ :=
  CanonicalGradedVariation.lift_bound sourceFilter (constant A) ‖A‖ (norm_nonneg _) (fun _ => le_rfl)

private theorem prefix_norm (cut order : ℕ) (t : ℝ) : ‖sourcePrefix cut order t‖≤(|t| * ‖cutoff cut‖)^order :=
  CanonicalGradedVariation.lift_bound sourceFilter (sourcePrefixFamily (cutoff cut) order t) _
    (by positivity) (fun F => finitePrefix_bound _ _ (GaussGradedCompression.compression_selfAdjoint F) order t)

theorem wordTerm_bound (cut : ℕ) (A B : H →L[ℂ] H) (r s t : ℝ) (i j k : ℕ) :
    ‖wordTerm cut A B r s t i j k‖ ≤ ‖A‖*‖B‖*
      ((|r| * ‖cutoff cut‖)^i*(|s| * ‖cutoff cut‖)^j*(|t| * ‖cutoff cut‖)^k) := by
  have product := List.norm_prod_le' (l := [historyProjection, sourcePrefix cut i r, reader A,
    sourcePrefix cut j s, reader B, sourcePrefix cut k t, historyProjection]) (by simp)
  have raw : ‖wordTerm cut A B r s t i j k‖≤
      ‖historyProjection‖*‖sourcePrefix cut i r‖*‖reader A‖*‖sourcePrefix cut j s‖*
        ‖reader B‖*‖sourcePrefix cut k t‖*‖historyProjection‖ := by
    simpa only [wordTerm, List.prod_cons, List.prod_nil, List.map_cons, List.map_nil,
      mul_one, mul_assoc] using product
  calc
    _ ≤ _ := raw
    _ ≤ 1*(|r| * ‖cutoff cut‖)^i*‖A‖*(|s| * ‖cutoff cut‖)^j*
        ‖B‖*(|t| * ‖cutoff cut‖)^k*1 := by
      gcongr
      · exact projection_norm
      · exact prefix_norm cut i r
      · exact reader_norm A
      · exact prefix_norm cut j s
      · exact reader_norm B
      · exact prefix_norm cut k t
      · exact projection_norm
    _ = _ := by ring

def pathBound (cut : ℕ) (a b : ℤ) (r s t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
    if (i : ℤ)+a+j+b+k=0 then
      (|r| * ‖cutoff cut‖)^i*(|s| * ‖cutoff cut‖)^j*(|t| * ‖cutoff cut‖)^k else 0

theorem pathBound_nonnegative (cut : ℕ) (a b : ℤ) (r s t : ℝ) : 0≤pathBound cut a b r s t := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  split_ifs <;> positivity

theorem selectedWord_bound (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ) (r s t : ℝ) :
    ‖selectedWord cut A B a b r s t‖≤‖A‖*‖B‖*pathBound cut a b r s t := by
  unfold selectedWord pathBound
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k _
  split_ifs
  · exact wordTerm_bound cut A B r s t i j k
  · simp only [norm_zero, mul_zero, le_refl]

theorem fullWord_bound (cut : ℕ) (A B : H →L[ℂ] H) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (lowerA : -1≤a) (lowerB : -1≤b) (r s t : ℝ) :
    ‖fullWord cut A B r s t‖≤‖A‖*‖B‖*pathBound cut a b r s t := by
  rw [fullWord_selected cut A B a b ha hb lowerA lowerB]
  exact selectedWord_bound cut A B a b r s t


theorem pathBound_zero_grade (cut : ℕ) (r s t : ℝ) : pathBound cut 0 0 r s t=1 := by
  norm_num [pathBound, Finset.sum_range_succ]

theorem pathBound_one_lowering (cut : ℕ) (r s t : ℝ) :
    pathBound cut (-1) 0 r s t=(|r|+|s|+|t|) * ‖cutoff cut‖ := by
  norm_num [pathBound, Finset.sum_range_succ]
  ring

theorem pathBound_two_lowering (cut : ℕ) (r s t : ℝ) :
    pathBound cut (-1) (-1) r s t=
      (|r|^2+|s|^2+|t|^2+|r| * |s|+|r| * |t|+|s| * |t|) * ‖cutoff cut‖^2 := by
  norm_num [pathBound, Finset.sum_range_succ]
  simp only [mul_pow, sq_abs]
  ring

#print axioms fullWord_bound

#print axioms fullWord_selected
end LowEnergy.CanonicalGradedMixedReturn
