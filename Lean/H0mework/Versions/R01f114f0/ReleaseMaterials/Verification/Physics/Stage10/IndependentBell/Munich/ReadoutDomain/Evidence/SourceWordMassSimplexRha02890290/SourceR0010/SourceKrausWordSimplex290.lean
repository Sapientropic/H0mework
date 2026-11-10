import H0mework.Versions.R3dba7b88.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceWordMassSimplexRha02890290.SourceR0007.SourceKrausWordMass289
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Actual word coordinates and the source's first-jump integral share one carrier.

Every occurrence is a finite marked word and its strict real time simplex.
The first-time split is an actual volume-preserving finite-coordinate map.
It does not assume a completed measure, a coverage certificate, or a selected
family of restricted flows. All amplitudes use the original common U(s,t).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology

namespace SourceKrausWordSimplex290

open SourceKrausSurvival285 SourceHiddenWordFlow286 SourceKrausWordMass289

universe u v

def simplex (start finish : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {times | (∀ i, start < times i ∧ times i < finish) ∧ StrictMono times}

theorem simplex_measurable (start finish : ℝ) (n : ℕ) :
    MeasurableSet (simplex start finish n) := by
  have bounds : MeasurableSet {times : Fin n → ℝ |
      ∀ i, start < times i ∧ times i < finish} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const)
  have ordered : MeasurableSet {times : Fin n → ℝ | StrictMono times} := by
    simp only [StrictMono, ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  exact bounds.inter ordered

private theorem strictMono_cons (n : ℕ) (r : ℝ) (times : Fin n → ℝ) :
    StrictMono (Fin.cons r times) ↔ (∀ i, r < times i) ∧ StrictMono times := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.succ_pos i),
      fun i j hij => by simpa using h (Fin.succ_lt_succ_iff.mpr hij)⟩
  · rintro ⟨above,ordered⟩ i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => exact (lt_irrefl _ hij).elim
        | succ j => simpa using above j
    | succ i =>
        cases j using Fin.cases with
        | zero => exact (Fin.not_lt_zero i.succ hij).elim
        | succ j => simpa using ordered (Fin.succ_lt_succ_iff.mp hij)

theorem simplex_cons (start finish r : ℝ) (n : ℕ) (times : Fin n → ℝ) :
    Fin.cons r times ∈ simplex start finish (n+1) ↔
      r ∈ Ioo start finish ∧ times ∈ simplex r finish n := by
  simp only [simplex, mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    strictMono_cons]
  constructor
  · rintro ⟨⟨atHead,tailBounds⟩,above,ordered⟩
    exact ⟨atHead,⟨fun i => ⟨above i,(tailBounds i).2⟩,ordered⟩⟩
  · rintro ⟨atHead,tailBounds,ordered⟩
    exact ⟨⟨atHead,fun i => ⟨atHead.1.trans (tailBounds i).1,(tailBounds i).2⟩⟩,
      (fun i => (tailBounds i).1),ordered⟩

theorem simplex_sub_box (start finish : ℝ) (n : ℕ) :
    simplex start finish n ⊆ Icc (fun _ => start) (fun _ => finish) := by
  intro times h
  exact ⟨fun i => (h.1 i).1.le,fun i => (h.1 i).2.le⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
theorem simplex_integrable (n : ℕ) (start finish : ℝ) (f : (Fin n → ℝ) → F)
    (continuous : Continuous f) : IntegrableOn f (simplex start finish n) volume :=
  (continuous.integrableOn_Icc (a := fun _ => start) (b := fun _ => finish)).mono_set
    (simplex_sub_box start finish n)

omit [CompleteSpace F] in
/-- The first real time and its entire remaining simplex are the original volume. -/
theorem integral_simplex_succ (n : ℕ) (start finish : ℝ)
    (f : (Fin (n+1) → ℝ) → F) (continuous : Continuous f) :
    (∫ times in simplex start finish (n+1), f times) =
      ∫ r in Ioo start finish, ∫ times in simplex r finish n, f (Fin.cons r times) := by
  classical
  let marked : (Fin (n+1) → ℝ) → F := (simplex start finish (n+1)).indicator f
  have marked_integrable : Integrable marked volume :=
    (simplex_integrable (n+1) start finish f continuous).integrable_indicator
      (simplex_measurable start finish (n+1))
  let split := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have preserving : MeasurePreserving split.symm
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
      (volume : Measure (Fin (n+1) → ℝ)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure ℝ)) 0).symm
  have transformed : Integrable (fun point : ℝ × (Fin n → ℝ) =>
      marked (Fin.cons point.1 point.2))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    simpa only [split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq, Function.comp_def] using
      (preserving.integrable_comp_emb split.symm.measurableEmbedding).mpr marked_integrable
  calc
    _ = ∫ times, marked times := (integral_indicator (simplex_measurable start finish (n+1))).symm
    _ = ∫ point : ℝ × (Fin n → ℝ), marked (Fin.cons point.1 point.2)
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
      simpa only [split, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Fin.zero_succAbove, Equiv.coe_fn_mk, cast_eq, Function.comp_def] using
          (preserving.integral_comp' marked).symm
    _ = ∫ r, ∫ times : Fin n → ℝ, marked (Fin.cons r times) := integral_prod _ transformed
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by
        by_cases inside : r ∈ Ioo start finish
        · rw [indicator_of_mem inside, ← integral_indicator (simplex_measurable r finish n)]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun times => by
            simp only [marked, indicator, simplex_cons, inside, true_and]
        · simp only [marked, indicator, simplex_cons, inside, false_and, ↓reduceIte,
            integral_zero]

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
variable {ι : Type v} [Fintype ι]
variable (source : RawKrausWindow E ι)

/-- Start is a coordinate of the same original U, not a new restricted source. -/
def amplitude : (n : ℕ) → ℝ → (Fin n → ι) → (Fin n → ℝ) → Operator (E := E)
  | 0, start, _, _ => source.chartPropagator start source.right
  | n+1, start, word, times =>
      amplitude n (times 0) (Fin.tail word) (Fin.tail times) *
        firstBranch source start (times 0) (word 0)

theorem amplitude_joint_continuous (n : ℕ) (word : Fin n → ι) :
    Continuous (fun point : ℝ × (Fin n → ℝ) => amplitude source n point.1 word point.2) := by
  induction n with
  | zero => exact source.chartPropagator_continuous.comp (continuous_fst.prodMk continuous_const)
  | succ n ih =>
      have tail : Continuous (fun times : Fin (n+1) → ℝ => Fin.tail times) :=
        continuous_pi fun i => continuous_apply i.succ
      exact ((ih (Fin.tail word)).comp
        (((continuous_apply 0).comp continuous_snd).prodMk (tail.comp continuous_snd))).mul
          ((firstBranch_continuous source (word 0)).comp
            (continuous_fst.prodMk ((continuous_apply 0).comp continuous_snd)))

theorem amplitude_continuous (n : ℕ) (start : ℝ) (word : Fin n → ι) :
    Continuous (amplitude source n start word) :=
  (amplitude_joint_continuous source n word).comp (continuous_const.prodMk continuous_id)

theorem amplitude_cons (n : ℕ) (start r : ℝ) (j : ι)
    (word : Fin n → ι) (times : Fin n → ℝ) :
    amplitude source (n+1) start (Fin.cons j word) (Fin.cons r times) =
      amplitude source n r word times * firstBranch source start r j := by
  simp only [amplitude, Fin.cons_zero, Fin.tail_cons]

def gram (n : ℕ) (start : ℝ) (word : Fin n → ι) (times : Fin n → ℝ) :
    Operator (E := E) :=
  (amplitude source n start word times).adjoint * amplitude source n start word times

theorem gram_continuous (n : ℕ) (start : ℝ) (word : Fin n → ι) :
    Continuous (gram source n start word) :=
  ((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (amplitude_continuous source n start word)).mul (amplitude_continuous source n start word)

theorem gram_cons (n : ℕ) (start r : ℝ) (j : ι)
    (word : Fin n → ι) (times : Fin n → ℝ) :
    gram source (n+1) start (Fin.cons j word) (Fin.cons r times) =
      (firstBranch source start r j).adjoint * gram source n r word times *
        firstBranch source start r j := by
  simp only [gram, amplitude_cons, ← ContinuousLinearMap.star_eq_adjoint,
    star_mul, mul_assoc]

def allWordGram (n : ℕ) (start : ℝ) : Operator (E := E) :=
  ∑ word : Fin n → ι, ∫ times in simplex start source.right n, gram source n start word times

/-- The actual simplex integral exposes exactly the original first-jump insertions. -/
theorem single_word_first_split (n : ℕ) (start : ℝ) (j : ι) (word : Fin n → ι) :
    (∫ times in simplex start source.right (n+1),
      gram source (n+1) start (Fin.cons j word) times) =
      ∫ r in Ioo start source.right, ∫ times in simplex r source.right n,
        (firstBranch source start r j).adjoint * gram source n r word times *
          firstBranch source start r j := by
  rw [integral_simplex_succ n start source.right _ (gram_continuous source (n+1) start _)]
  simp only [gram_cons]

private def singleInsertion (j : ι) (f : ℝ → Operator (E := E))
    (s r : ℝ) : Operator (E := E) :=
  (firstBranch source s r j).adjoint * f r * firstBranch source s r j

private theorem singleInsertion_continuous (j : ι) (f : ℝ → Operator (E := E))
    (continuous : Continuous f) :
    Continuous (fun pair : ℝ × ℝ => singleInsertion source j f pair.1 pair.2) :=
  (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (firstBranch_continuous source j)).mul (continuous.comp continuous_snd)).mul
      (firstBranch_continuous source j)

def fixedWordGram : (n : ℕ) → (Fin n → ι) → ℝ → Operator (E := E)
  | 0, _, s => vacuum source s
  | n+1, word, s => ∫ r in s..source.right,
      singleInsertion source (word 0) (fixedWordGram n (Fin.tail word)) s r

theorem fixedWordGram_continuous (n : ℕ) (word : Fin n → ι) :
    Continuous (fixedWordGram source n word) := by
  induction n with
  | zero => exact vacuum_continuous source
  | succ n ih =>
      have written : Continuous (fun s : ℝ =>
          ∫ r in source.right..s,
            singleInsertion source (word 0) (fixedWordGram source n (Fin.tail word)) s r) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun s r : ℝ =>
            singleInsertion source (word 0) (fixedWordGram source n (Fin.tail word)) s r)
          (a₀ := source.right)
          (singleInsertion_continuous source (word 0) _ (ih (Fin.tail word))) continuous_id
      have same : fixedWordGram source (n+1) word = (fun s : ℝ =>
          -(∫ r in source.right..s,
            singleInsertion source (word 0) (fixedWordGram source n (Fin.tail word)) s r)) := by
        funext s
        exact intervalIntegral.integral_symm _ _
      rw [same]
      exact written.neg

private theorem simplex_zero (start finish : ℝ) : simplex start finish 0 = univ := by
  ext times
  simp [simplex, StrictMono]

/-- The nested source integral is exactly its full real-coordinate Gram integral. -/
theorem fixedWordGram_eq_simplex (n : ℕ) (word : Fin n → ι) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    fixedWordGram source n word start =
      ∫ times in simplex start source.right n, gram source n start word times := by
  induction n generalizing start with
  | zero =>
      have empty_volume : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
        change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) univ = 1
        exact Measure.pi_empty_univ _
      simp [fixedWordGram, simplex_zero, gram, amplitude, vacuum, measureReal_def, empty_volume]
  | succ n ih =>
      obtain ⟨⟨j,word⟩,rfl⟩ := (Fin.consEquiv (fun _ : Fin (n+1) => ι)).surjective word
      change fixedWordGram source (n+1) (Fin.cons j word) start =
        ∫ times in simplex start source.right (n+1), gram source (n+1) start (Fin.cons j word) times
      rw [single_word_first_split source n start j word]
      simp only [fixedWordGram, Fin.cons_zero, Fin.tail_cons]
      rw [intervalIntegral.integral_of_le inside.2, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have paid := ih word r ⟨inside.1.trans hr.1.le,hr.2.le⟩
      have integrable := simplex_integrable n r source.right _ (gram_continuous source n r word)
      rw [singleInsertion, paid]
      change ((firstBranch source start r j).adjoint *
        ∫ times in simplex r source.right n, gram source n r word times) *
          firstBranch source start r j =
        ∫ times in simplex r source.right n,
          (firstBranch source start r j).adjoint * gram source n r word times *
            firstBranch source start r j
      rw [← integral_const_mul_of_integrable
        (c := (firstBranch source start r j).adjoint) integrable,
        ← integral_mul_const_of_integrable (c := firstBranch source start r j)
          (integrable.const_mul (firstBranch source start r j).adjoint)]

omit [CompleteSpace E] [Nontrivial E] in
private theorem sum_cons (n : ℕ) (f : (Fin (n+1) → ι) → Operator (E := E)) :
    (∑ word, f word) = ∑ j, ∑ word : Fin n → ι, f (Fin.cons j word) := by
  classical
  have expanded := ((Fin.consEquiv (fun _ : Fin (n+1) => ι)).sum_comp f).symm
  change (∑ word, f word) = ∑ point : ι × (Fin n → ι), f (Fin.cons point.1 point.2) at expanded
  simpa only [Fintype.sum_prod_type] using expanded

theorem sum_fixedWordGram (n : ℕ) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    (∑ word : Fin n → ι, fixedWordGram source n word start) = wordGram source n start := by
  classical
  induction n generalizing start with
  | zero => simp [fixedWordGram, wordGram, SourceKrausWordMass289.iterate]
  | succ n ih =>
      rw [sum_cons n]
      simp only [fixedWordGram, Fin.cons_zero, Fin.tail_cons]
      have integrable (j : ι) (word : Fin n → ι) :
          IntervalIntegrable (singleInsertion source j (fixedWordGram source n word) start)
            volume start source.right :=
        ((singleInsertion_continuous source j _ (fixedWordGram_continuous source n word)).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      have summed (j : ι) :
          IntervalIntegrable (fun r => ∑ word : Fin n → ι,
            singleInsertion source j (fixedWordGram source n word) start r)
            volume start source.right :=
        by simpa only [Finset.sum_fn] using
          IntervalIntegrable.sum (ε := Operator (E := E))
            (μ := (volume : Measure ℝ)) (a := start) (b := source.right)
            (f := fun word : Fin n → ι =>
              singleInsertion source j (fixedWordGram source n word) start)
            Finset.univ (fun word _ => integrable j word)
      have word_sum (j : ι) :
          (∑ word : Fin n → ι, ∫ r in start..source.right,
            singleInsertion source j (fixedWordGram source n word) start r) =
          ∫ r in start..source.right, ∑ word : Fin n → ι,
            singleInsertion source j (fixedWordGram source n word) start r :=
        (intervalIntegral.integral_finsetSum (s := Finset.univ)
          (f := fun word : Fin n → ι => singleInsertion source j (fixedWordGram source n word) start)
          (fun word _ => integrable j word)).symm
      simp_rw [word_sum]
      rw [← intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun j : ι => fun r : ℝ => ∑ word : Fin n → ι,
          singleInsertion source j (fixedWordGram source n word) start r)
        (fun j _ => summed j)]
      change (∫ r in start..source.right, ∑ j, ∑ word : Fin n → ι,
        singleInsertion source j (fixedWordGram source n word) start r) =
        ∫ r in start..source.right, insertion source (wordGram source n) start r
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le inside.2] at hr
      simp only [singleInsertion, insertion, ← Finset.mul_sum, ← Finset.sum_mul,
        ih r ⟨inside.1.trans hr.1,hr.2⟩]

theorem allWordGram_eq_source (n : ℕ) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    allWordGram source n start = wordGram source n start := by
  classical
  simp only [allWordGram, ← fixedWordGram_eq_simplex source n _ start inside]
  exact sum_fixedWordGram source n start inside

/-- The full flat word expansion inherits the source-generated identity Gram. -/
theorem allWordGram_hasSum_identity (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    HasSum (fun n => allWordGram source n start) 1 := by
  simpa only [allWordGram_eq_source source _ start inside] using
    wordGram_hasSum_identity source start inside

private def realQuadratic (x : E) : Operator (E := E) →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E x)).restrictScalars ℝ)

private theorem realQuadratic_gram (n : ℕ) (start : ℝ) (word : Fin n → ι)
    (times : Fin n → ℝ) (x : E) :
    realQuadratic x (gram source n start word times) =
      ‖amplitude source n start word times x‖^2 := by
  change (inner ℂ x (((amplitude source n start word times).adjoint *
    amplitude source n start word times) x)).re = _
  exact (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right
    (𝕜 := ℂ) (E := E) (F := E) (amplitude source n start word times) x).symm

theorem wordMass_eq_simplex (n : ℕ) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (x : E) :
    wordMass source n start x = ∑ word : Fin n → ι,
      ∫ times in simplex start source.right n, ‖amplitude source n start word times x‖^2 := by
  classical
  change realQuadratic x (wordGram source n start) = _
  rw [← allWordGram_eq_source source n start inside, allWordGram, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [← (realQuadratic x).integral_comp_comm
    (μ := (volume : Measure (Fin n → ℝ)).restrict (simplex start source.right n))
    (φ := fun times : Fin n → ℝ => gram source n start word times)
    (simplex_integrable n start source.right _ (gram_continuous source n start word))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun times => realQuadratic_gram source n start word times x

/-- All continuous times and all finite marked words conserve the original norm. -/
theorem full_word_norm (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    HasSum (fun n => ∑ word : Fin n → ι,
      ∫ times in simplex start source.right n,
        ‖amplitude source n start word times x‖^2) (‖x‖^2) := by
  simpa only [wordMass_eq_simplex source _ start inside x] using
    wordMass_hasSum_norm source start inside x

end SourceKrausWordSimplex290
