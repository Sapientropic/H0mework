import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalGradedCurrentSource

/-! Actual grade balance selects the surviving original Yukawa paths between
mixed current insertions. Negative-grade scalar readers remain in the word. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalGradedMixed
open GaussCoreHilbert GaussYukawaGrade CanonicalGradedCurrent
open FullYSourceCutoffVolterra
open GaussUnitaryHistory (Index)
open scoped BigOperators

abbrev Operator := H →L[ℂ] H

def Homogeneous (A : Operator) (g : ℤ) : Prop :=
  GaussYukawaGrade.grade*A=A*GaussYukawaGrade.grade+(g : ℂ) • A

theorem homogeneous_mul (A B : Operator) (a b : ℤ) (ha : Homogeneous A a) (hb : Homogeneous B b) :
    Homogeneous (A*B) (a+b) := by
  unfold Homogeneous at *
  calc
    _ = (GaussYukawaGrade.grade*A)*B := by rw [mul_assoc]
    _ = (A*GaussYukawaGrade.grade+(a : ℂ) • A)*B := by rw [ha]
    _ = A*(B*GaussYukawaGrade.grade+(b : ℂ) • B)+(a : ℂ) • (A*B) := by
      rw [add_mul, mul_assoc, hb, smul_mul_assoc]
    _ = _ := by
      simp only [mul_add, mul_smul_comm, Int.cast_add, mul_assoc]
      module

private theorem grade_sourceProjection : GaussYukawaGrade.grade*sourceProjection=0 := by
  have h := GaussYukawaInteraction.source_grade_right sourceLabel
  have hz : (sourceLabel.2.val : ℂ)=0 := by norm_num [sourceLabel]
  rw [hz] at h
  apply h.trans
  apply ContinuousLinearMap.ext
  intro x
  exact zero_smul ℂ (sourceProjection x)

theorem unbalanced_zero (A : Operator) (g : ℤ) (homogeneous : Homogeneous A g) (nonzero : g≠0) :
    sourceProjection*A*sourceProjection=0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hl := congrArg (fun T : Operator => T (A (sourceProjection x))) sourceProjection_grade
  have hr := congrArg (fun T : Operator => T x) grade_sourceProjection
  change sourceProjection (GaussYukawaGrade.grade (A (sourceProjection x)))=0 at hl
  change GaussYukawaGrade.grade (sourceProjection x)=0 at hr
  have h := congrArg (fun T : Operator => sourceProjection (T (sourceProjection x))) homogeneous
  change sourceProjection (GaussYukawaGrade.grade (A (sourceProjection x)))=
    sourceProjection (A (GaussYukawaGrade.grade (sourceProjection x))+(g : ℂ) • A (sourceProjection x)) at h
  rw [hl, hr, map_zero, zero_add, map_smul] at h
  have hn : (g : ℂ)≠0 := by exact_mod_cast nonzero
  exact (smul_eq_zero.mp h.symm).resolve_left hn

def sourceTerm (cut n : ℕ) (t : ℝ) (F : Index) : Operator :=
  finitePrefix (GaussGradedCompression.compression F) (cutoff cut) n t

theorem prefix_homogeneous (cut n : ℕ) (t : ℝ) (F : Index) :
    Homogeneous (sourceTerm cut n t F) (n : ℤ) := by
  simpa only [Homogeneous, sourceTerm, Int.cast_natCast] using
    finitePrefix_homogeneous _ _ _ (source_compression_grade F) (cutoff_raises cut) n t

theorem partial_sum (C A : Operator) (n : ℕ) (t : ℝ) :
    partialEvolution C A n t=∑ j ∈ Finset.range (n+1), finitePrefix C A j t := by
  induction n with
  | zero => simp [partialEvolution, finitePrefix, orderedIntegral]
  | succ n ih => rw [partialEvolution, Finset.sum_range_succ, ih]

theorem source_time_sum (cut : ℕ) (t : ℝ) (F : Index) :
    SourceFiniteUnitary.time (GaussGradedCompression.compression F+cutoff cut) t=
      ∑ j ∈ Finset.range 57, sourceTerm cut j t F := by
  rw [← source_finite_evolution_return, partial_sum]
  rfl

def wordTerm (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) (i j k : ℕ) : Operator :=
  sourceTerm cut i r F*A*sourceTerm cut j s F*B*sourceTerm cut k t F

theorem wordTerm_homogeneous (cut : ℕ) (A B : Operator) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (r s t : ℝ) (F : Index) (i j k : ℕ) :
    Homogeneous (wordTerm cut A B r s t F i j k) ((i : ℤ)+a+j+b+k) :=
  homogeneous_mul _ _ _ _
    (homogeneous_mul _ _ _ _
      (homogeneous_mul _ _ _ _
        (homogeneous_mul _ _ _ _ (prefix_homogeneous cut i r F) ha)
        (prefix_homogeneous cut j s F)) hb)
    (prefix_homogeneous cut k t F)

theorem wordTerm_unbalanced (cut : ℕ) (A B : Operator) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (r s t : ℝ) (F : Index) (i j k : ℕ)
    (unbalanced : (i : ℤ)+a+j+b+k≠0) :
    sourceProjection*wordTerm cut A B r s t F i j k*sourceProjection=0 :=
  unbalanced_zero _ _ (wordTerm_homogeneous cut A B a b ha hb r s t F i j k) unbalanced

def fullWord (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) : Operator :=
  let D := GaussGradedCompression.compression F+cutoff cut
  sourceProjection*SourceFiniteUnitary.time D r*A*SourceFiniteUnitary.time D s*B*
    SourceFiniteUnitary.time D t*sourceProjection

private theorem triple_sum_identity {R : Type*} [Ring R] (S : Finset ℕ)
    (P A B : R) (f g h : ℕ → R) :
    P*(∑ i ∈ S, f i)*A*(∑ j ∈ S, g j)*B*(∑ k ∈ S, h k)*P=
      ∑ i ∈ S, ∑ j ∈ S, ∑ k ∈ S, P*(f i*A*g j*B*h k)*P := by
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

theorem fullWord_sum (cut : ℕ) (A B : Operator) (r s t : ℝ) (F : Index) :
    fullWord cut A B r s t F=
      ∑ i ∈ Finset.range 57, ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57,
        sourceProjection*wordTerm cut A B r s t F i j k*sourceProjection := by
  dsimp only [fullWord]
  rw [source_time_sum, source_time_sum, source_time_sum]
  exact triple_sum_identity (Finset.range 57) sourceProjection A B
    (fun i => sourceTerm cut i r F) (fun j => sourceTerm cut j s F) (fun k => sourceTerm cut k t F)

private theorem sum57_to3 {M : Type*} [AddCommMonoid M] (f : ℕ → M)
    (vanishes : ∀ n, 3 ≤ n → n<57 → f n=0) :
    ∑ n ∈ Finset.range 57, f n=∑ n ∈ Finset.range 3, f n := by
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hout
  exact vanishes n (by simpa only [Finset.mem_range, not_lt] using hout)
    (by simpa only [Finset.mem_range] using hn)

def selectedWord (cut : ℕ) (A B : Operator) (a b : ℤ) (r s t : ℝ) (F : Index) : Operator :=
  ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3,
    if (i : ℤ)+a+j+b+k=0 then sourceProjection*wordTerm cut A B r s t F i j k*sourceProjection else 0

theorem fullWord_selected (cut : ℕ) (A B : Operator) (a b : ℤ)
    (ha : Homogeneous A a) (hb : Homogeneous B b) (lowerA : -1≤a) (lowerB : -1≤b)
    (r s t : ℝ) (F : Index) :
    fullWord cut A B r s t F=selectedWord cut A B a b r s t F := by
  let term := fun i j k => sourceProjection*wordTerm cut A B r s t F i j k*sourceProjection
  have large (i j k : ℕ) (outside : 3 ≤ i ∨ 3 ≤ j ∨ 3 ≤ k) : term i j k=0 :=
    wordTerm_unbalanced cut A B a b ha hb r s t F i j k (by omega)
  have trimK (i j : ℕ) : (∑ k ∈ Finset.range 57, term i j k)=∑ k ∈ Finset.range 3, term i j k :=
    sum57_to3 (fun k => term i j k) (fun k hk _ => large i j k (Or.inr (Or.inr hk)))
  have trimJ (i : ℕ) : (∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)=
      ∑ j ∈ Finset.range 3, ∑ k ∈ Finset.range 3, term i j k := by
    rw [sum57_to3 (fun j => ∑ k ∈ Finset.range 57, term i j k) (fun j hj _ =>
      Finset.sum_eq_zero (fun k _ => large i j k (Or.inr (Or.inl hj))))]
    exact Finset.sum_congr rfl (fun j _ => trimK i j)
  rw [fullWord_sum]
  change (∑ i ∈ Finset.range 57, ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)=_
  rw [sum57_to3 (fun i => ∑ j ∈ Finset.range 57, ∑ k ∈ Finset.range 57, term i j k)
    (fun i hi _ => Finset.sum_eq_zero (fun j _ =>
      Finset.sum_eq_zero (fun k _ => large i j k (Or.inl hi))))]
  unfold selectedWord
  apply Finset.sum_congr rfl
  intro i _
  rw [trimJ]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with balanced
  · rfl
  · exact wordTerm_unbalanced cut A B a b ha hb r s t F i j k balanced

/-- The path count is generated after grade balance, before further source cancellations. -/
def paths (a b : ℤ) : Finset (Fin 3 × Fin 3 × Fin 3) :=
  Finset.univ.filter (fun n => (n.1.val : ℤ)+a+n.2.1.val+b+n.2.2.val=0)

theorem zero_grade_path_count : (paths 0 0).card=1 := by decide
theorem single_lowering_path_count : (paths (-1) 0).card=3 := by decide
theorem double_lowering_path_count : (paths (-1) (-1)).card=6 := by decide

#print axioms fullWord_selected

#print axioms wordTerm_unbalanced
end LowEnergy.CanonicalGradedMixed
