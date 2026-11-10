import H0mework.Versions.Rfa2085ee.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceKrausWordWaveRha0291.SourceR0004.SourceKrausWordWave291
import Mathlib.Analysis.Normed.Operator.Mul

/-! Endpoint observables on restrictions of the original complete word source.
The selected letters change neither K nor the original source measure.
Every finite word, every real chronological coordinate and the vacuum remain.
-/

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace SourceEndpointWords300
open SourceKrausSurvival285 SourceHiddenWordFlow286 SourceKrausWordMass289
open SourceKrausWordSimplex290 SourceKrausWordWave291

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
variable {ι : Type v} [Fintype ι]
variable (source : RawKrausWindow E ι) (hidden : Finset ι)

omit [CompleteSpace E] [Nontrivial E] in
def matrixElement (x y : E) : Operator (E := E) →L[ℂ] ℂ :=
  (innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ E y)

abbrev Letters := ↥hidden

def physicalWord {n : ℕ} (word : Fin n → Letters hidden) : Fin n → ι :=
  fun k => (word k).val

def insertion (f : ℝ → Operator (E := E)) (s r : ℝ) : Operator (E := E) :=
  ∑ j : Letters hidden,
    (firstBranch source s r j.val).adjoint * f r * firstBranch source s r j.val

theorem insertion_continuous (f : ℝ → Operator (E := E)) (hf : Continuous f) :
    Continuous (fun point : ℝ × ℝ => insertion source hidden f point.1 point.2) :=
  continuous_finsetSum Finset.univ fun j _ =>
    (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
      (firstBranch_continuous source j.val)).mul (hf.comp continuous_snd)).mul
        (firstBranch_continuous source j.val)

def advance (f : ℝ → Operator (E := E)) (s : ℝ) : Operator (E := E) :=
  ∫ r in s..source.right, insertion source hidden f s r

theorem advance_continuous (f : ℝ → Operator (E := E)) (hf : Continuous f) :
    Continuous (advance source hidden f) := by
  have moving : Continuous (fun s : ℝ =>
      ∫ r in source.right..s, insertion source hidden f s r) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun s r : ℝ => insertion source hidden f s r) (a₀ := source.right)
      (insertion_continuous source hidden f hf) continuous_id
  have written : advance source hidden f = fun s =>
      -(∫ r in source.right..s, insertion source hidden f s r) := by
    funext s
    exact intervalIntegral.integral_symm _ _
  rw [written]
  exact moving.neg

private theorem insertion_integrable (f : ℝ → Operator (E := E))
    (hf : Continuous f) (s : ℝ) :
    IntervalIntegrable (insertion source hidden f s) volume s source.right :=
  ((insertion_continuous source hidden f hf).comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

theorem advance_sub (f g : ℝ → Operator (E := E))
    (hf : Continuous f) (hg : Continuous g) (s : ℝ) :
    advance source hidden (fun r => f r-g r) s =
      advance source hidden f s - advance source hidden g s := by
  simp only [advance, insertion, mul_sub, sub_mul, Finset.sum_sub_distrib]
  exact intervalIntegral.integral_sub (insertion_integrable source hidden f hf s)
    (insertion_integrable source hidden g hg s)

theorem advance_congr (f g : ℝ → Operator (E := E))
    (same : EqOn f g (Icc source.left source.right)) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    advance source hidden f s = advance source hidden g s := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le inside.2] at hr
  simp only [insertion, same ⟨inside.1.trans hr.1,hr.2⟩]

def iterate (seed : ℝ → Operator (E := E)) : ℕ → ℝ → Operator (E := E)
  | 0 => seed
  | n+1 => advance source hidden (iterate seed n)

theorem iterate_continuous (seed : ℝ → Operator (E := E)) (continuous : Continuous seed)
    (n : ℕ) : Continuous (iterate source hidden seed n) := by
  induction n with
  | zero => exact continuous
  | succ n ih => exact advance_continuous source hidden _ ih

def activity : ℝ := ∑ j : Letters hidden, (source.jump_bounds j.val : ℝ)^2

theorem activity_nonnegative : 0 ≤ activity source hidden :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem insertion_norm (f : ℝ → Operator (E := E)) (s r : ℝ)
    (hs : s ∈ Icc source.left source.right) (hr : r ∈ Icc s source.right) :
    ‖insertion source hidden f s r‖ ≤ activity source hidden * ‖f r‖ := by
  calc
    _ ≤ ∑ j : Letters hidden,
        ‖(firstBranch source s r j.val).adjoint * f r * firstBranch source s r j.val‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Letters hidden, (source.jump_bounds j.val : ℝ)^2 * ‖f r‖ := by
      apply Finset.sum_le_sum
      intro j _
      have bound := firstBranch_norm source s r hs hr j.val
      calc
        _ ≤ (‖(firstBranch source s r j.val).adjoint‖ * ‖f r‖) *
            ‖firstBranch source s r j.val‖ :=
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))
        _ = ‖firstBranch source s r j.val‖ * ‖f r‖ *
            ‖firstBranch source s r j.val‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ (source.jump_bounds j.val : ℝ) * ‖f r‖ * (source.jump_bounds j.val : ℝ) := by
          gcongr
        _ = _ := by ring
    _ = _ := by rw [← Finset.sum_mul]; rfl

private theorem polynomial_integral (n : ℕ) (a b : ℝ) :
    (∫ r in a..b, (b-r)^n) = (b-a)^(n+1)/(n+1) := by
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^n) b, integral_pow]
  simp

/-- This bound is generated from the original U and selected original J only. -/
theorem iterate_norm (seed : ℝ → Operator (E := E)) (M : ℝ)
    (bound : ∀ s ∈ Icc source.left source.right, ‖seed s‖ ≤ M) (n : ℕ)
    (s : ℝ) (inside : s ∈ Icc source.left source.right) :
    ‖iterate source hidden seed n s‖ ≤
      M * activity source hidden ^ n * (source.right-s)^n / n.factorial := by
  induction n generalizing s with
  | zero => simpa only [iterate, pow_zero, Nat.factorial_zero, Nat.cast_one,
      mul_one, div_one] using bound s inside
  | succ n ih =>
      have continuous : Continuous (fun r : ℝ => activity source hidden *
          (M * activity source hidden ^ n * (source.right-r)^n / n.factorial)) := by fun_prop
      change ‖∫ r in s..source.right, insertion source hidden (iterate source hidden seed n) s r‖ ≤ _
      calc
        _ ≤ ∫ r in s..source.right, activity source hidden *
            (M * activity source hidden ^ n * (source.right-r)^n / n.factorial) := by
          apply intervalIntegral.norm_integral_le_of_norm_le inside.2
            (Filter.Eventually.of_forall fun r hr => ?_) (continuous.intervalIntegrable _ _)
          exact (insertion_norm source hidden _ s r inside ⟨hr.1.le,hr.2⟩).trans
            (mul_le_mul_of_nonneg_left (ih r ⟨inside.1.trans hr.1.le,hr.2⟩)
              (activity_nonnegative source hidden))
        _ = _ := by
          have written : (fun r : ℝ => activity source hidden *
              (M * activity source hidden ^ n * (source.right-r)^n / n.factorial)) =
              fun r => (activity source hidden * M * activity source hidden ^ n /
                n.factorial) * (source.right-r)^n := by funext r; ring
          rw [written, intervalIntegral.integral_const_mul, polynomial_integral]
          simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
            pow_succ, div_eq_mul_inv, mul_inv_rev]
          ring

theorem iterate_tendsto_zero (seed : ℝ → Operator (E := E)) (M : ℝ)
    (bound : ∀ s ∈ Icc source.left source.right, ‖seed s‖ ≤ M) (s : ℝ)
    (inside : s ∈ Icc source.left source.right) :
    Tendsto (fun n => iterate source hidden seed n s) atTop (𝓝 0) := by
  apply squeeze_zero_norm
  · intro n
    simpa only [mul_pow, mul_assoc, mul_div_assoc] using
      iterate_norm source hidden seed M bound n s inside
  · simpa only [mul_zero, mul_pow, mul_assoc, mul_div_assoc] using
      (FloorSemiring.tendsto_pow_div_factorial_atTop
        (activity source hidden * (source.right-s))).const_mul M

def endpointSeed (A : Operator (E := E)) (s : ℝ) : Operator (E := E) :=
  (source.chartPropagator s source.right).adjoint * A * source.chartPropagator s source.right

theorem endpointSeed_continuous (A : Operator (E := E)) : Continuous (endpointSeed source A) :=
  (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (source.chartPropagator_continuous.comp (continuous_id.prodMk continuous_const))).mul
      continuous_const).mul
        (source.chartPropagator_continuous.comp (continuous_id.prodMk continuous_const))

def endpointWord (A : Operator (E := E)) (n : ℕ) : ℝ → Operator (E := E) :=
  iterate source hidden (endpointSeed source A) n

def wordKernel (A : Operator (E := E)) (n : ℕ) (start : ℝ)
    (word : Fin n → Letters hidden) (times : Fin n → ℝ) : Operator (E := E) :=
  (amplitude source n start (physicalWord hidden word) times).adjoint * A *
    amplitude source n start (physicalWord hidden word) times

theorem wordKernel_continuous (A : Operator (E := E)) (n : ℕ) (start : ℝ)
    (word : Fin n → Letters hidden) : Continuous (wordKernel source hidden A n start word) :=
  (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (amplitude_continuous source n start (physicalWord hidden word))).mul continuous_const).mul
      (amplitude_continuous source n start (physicalWord hidden word))

omit [Fintype ι] in
private theorem physicalWord_cons (n : ℕ) (j : Letters hidden)
    (word : Fin n → Letters hidden) :
    physicalWord hidden (Fin.cons j word) = Fin.cons j.val (physicalWord hidden word) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i <;> rfl

theorem wordKernel_cons (A : Operator (E := E)) (n : ℕ) (start r : ℝ)
    (j : Letters hidden) (word : Fin n → Letters hidden) (times : Fin n → ℝ) :
    wordKernel source hidden A (n+1) start (Fin.cons j word) (Fin.cons r times) =
      (firstBranch source start r j.val).adjoint * wordKernel source hidden A n r word times *
        firstBranch source start r j.val := by
  simp only [wordKernel, physicalWord_cons, amplitude_cons,
    ← ContinuousLinearMap.star_eq_adjoint, star_mul, mul_assoc]

private def singleInsertion (j : Letters hidden) (f : ℝ → Operator (E := E))
    (s r : ℝ) : Operator (E := E) :=
  (firstBranch source s r j.val).adjoint * f r * firstBranch source s r j.val

private theorem singleInsertion_continuous (j : Letters hidden)
    (f : ℝ → Operator (E := E)) (continuous : Continuous f) :
    Continuous (fun point : ℝ × ℝ => singleInsertion source hidden j f point.1 point.2) :=
  (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    (firstBranch_continuous source j.val)).mul (continuous.comp continuous_snd)).mul
      (firstBranch_continuous source j.val)

def fixedWord (A : Operator (E := E)) :
    (n : ℕ) → (Fin n → Letters hidden) → ℝ → Operator (E := E)
  | 0, _, s => endpointSeed source A s
  | n+1, word, s => ∫ r in s..source.right,
      singleInsertion source hidden (word 0) (fixedWord A n (Fin.tail word)) s r

theorem fixedWord_continuous (A : Operator (E := E)) (n : ℕ)
    (word : Fin n → Letters hidden) : Continuous (fixedWord source hidden A n word) := by
  induction n with
  | zero => exact endpointSeed_continuous source A
  | succ n ih =>
      have moving : Continuous (fun s : ℝ => ∫ r in source.right..s,
          singleInsertion source hidden (word 0)
            (fixedWord source hidden A n (Fin.tail word)) s r) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (f := fun s r : ℝ => singleInsertion source hidden (word 0)
            (fixedWord source hidden A n (Fin.tail word)) s r) (a₀ := source.right)
          (singleInsertion_continuous source hidden (word 0) _ (ih (Fin.tail word))) continuous_id
      have written : fixedWord source hidden A (n+1) word = fun s =>
          -(∫ r in source.right..s, singleInsertion source hidden (word 0)
            (fixedWord source hidden A n (Fin.tail word)) s r) := by
        funext s
        exact intervalIntegral.integral_symm _ _
      rw [written]
      exact moving.neg

theorem fixedWord_eq_simplex (A : Operator (E := E)) (n : ℕ)
    (word : Fin n → Letters hidden) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    fixedWord source hidden A n word start =
      ∫ times in simplex start source.right n, wordKernel source hidden A n start word times := by
  induction n generalizing start with
  | zero =>
      have empty_volume : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
        change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) univ = 1
        exact Measure.pi_empty_univ _
      have empty_simplex : simplex start source.right 0 = univ := by
        ext times
        simp [simplex, StrictMono]
      simp [fixedWord, empty_simplex, wordKernel, amplitude, endpointSeed,
        measureReal_def, empty_volume]
  | succ n ih =>
      obtain ⟨⟨j,word⟩,rfl⟩ :=
        (Fin.consEquiv (fun _ : Fin (n+1) => Letters hidden)).surjective word
      change fixedWord source hidden A (n+1) (Fin.cons j word) start =
        ∫ times in simplex start source.right (n+1),
          wordKernel source hidden A (n+1) start (Fin.cons j word) times
      rw [integral_simplex_succ n start source.right _
        (wordKernel_continuous source hidden A (n+1) start _)]
      simp only [fixedWord, Fin.cons_zero, Fin.tail_cons]
      rw [intervalIntegral.integral_of_le inside.2, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      have paid := ih word r ⟨inside.1.trans hr.1.le,hr.2.le⟩
      have integrable := simplex_integrable n r source.right _
        (wordKernel_continuous source hidden A n r word)
      rw [singleInsertion, paid]
      change ((firstBranch source start r j.val).adjoint *
        ∫ times in simplex r source.right n, wordKernel source hidden A n r word times) *
          firstBranch source start r j.val =
        ∫ times in simplex r source.right n,
          wordKernel source hidden A (n+1) start (Fin.cons j word) (Fin.cons r times)
      simp_rw [wordKernel_cons]
      rw [← integral_const_mul_of_integrable
        (c := (firstBranch source start r j.val).adjoint) integrable,
        ← integral_mul_const_of_integrable (c := firstBranch source start r j.val)
          (integrable.const_mul (firstBranch source start r j.val).adjoint)]

omit [Fintype ι] in
private theorem sum_cons {F : Type*} [AddCommMonoid F] (n : ℕ)
    (f : (Fin (n+1) → Letters hidden) → F) :
    (∑ word, f word) = ∑ j, ∑ word : Fin n → Letters hidden, f (Fin.cons j word) := by
  classical
  have expanded := ((Fin.consEquiv (fun _ : Fin (n+1) => Letters hidden)).sum_comp f).symm
  change (∑ word, f word) = ∑ point : Letters hidden × (Fin n → Letters hidden),
    f (Fin.cons point.1 point.2) at expanded
  simpa only [Fintype.sum_prod_type] using expanded

theorem sum_fixedWord (A : Operator (E := E)) (n : ℕ) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    (∑ word : Fin n → Letters hidden, fixedWord source hidden A n word start) =
      endpointWord source hidden A n start := by
  classical
  induction n generalizing start with
  | zero => simp [fixedWord, endpointWord, iterate]
  | succ n ih =>
      rw [sum_cons hidden n]
      simp only [fixedWord, Fin.cons_zero, Fin.tail_cons]
      have integrable (j : Letters hidden) (word : Fin n → Letters hidden) :
          IntervalIntegrable (singleInsertion source hidden j (fixedWord source hidden A n word) start)
            volume start source.right :=
        ((singleInsertion_continuous source hidden j _ (fixedWord_continuous source hidden A n word)).comp
          (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
      have summed (j : Letters hidden) :
          IntervalIntegrable (fun r => ∑ word : Fin n → Letters hidden,
            singleInsertion source hidden j (fixedWord source hidden A n word) start r)
            volume start source.right := by
        simpa only [Finset.sum_fn] using
          IntervalIntegrable.sum (ε := Operator (E := E)) (μ := (volume : Measure ℝ))
            (a := start) (b := source.right)
            (f := fun word : Fin n → Letters hidden =>
              singleInsertion source hidden j (fixedWord source hidden A n word) start)
            Finset.univ (fun word _ => integrable j word)
      have word_sum (j : Letters hidden) :
          (∑ word : Fin n → Letters hidden, ∫ r in start..source.right,
            singleInsertion source hidden j (fixedWord source hidden A n word) start r) =
          ∫ r in start..source.right, ∑ word : Fin n → Letters hidden,
            singleInsertion source hidden j (fixedWord source hidden A n word) start r :=
        (intervalIntegral.integral_finsetSum (s := Finset.univ)
          (f := fun word : Fin n → Letters hidden =>
            singleInsertion source hidden j (fixedWord source hidden A n word) start)
          (fun word _ => integrable j word)).symm
      simp_rw [word_sum]
      rw [← intervalIntegral.integral_finsetSum (s := Finset.univ)
        (f := fun j : Letters hidden => fun r : ℝ => ∑ word : Fin n → Letters hidden,
          singleInsertion source hidden j (fixedWord source hidden A n word) start r)
        (fun j _ => summed j)]
      change (∫ r in start..source.right, ∑ j, ∑ word : Fin n → Letters hidden,
        singleInsertion source hidden j (fixedWord source hidden A n word) start r) =
        ∫ r in start..source.right, insertion source hidden
          (endpointWord source hidden A n) start r
      apply intervalIntegral.integral_congr
      intro r hr
      rw [uIcc_of_le inside.2] at hr
      simp only [singleInsertion, insertion, ← Finset.mul_sum, ← Finset.sum_mul,
        ih r ⟨inside.1.trans hr.1,hr.2⟩]

theorem endpointWord_eq_simplex (A : Operator (E := E)) (n : ℕ) (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    endpointWord source hidden A n start =
      ∑ word : Fin n → Letters hidden, ∫ times in simplex start source.right n,
        wordKernel source hidden A n start word times := by
  rw [← sum_fixedWord source hidden A n start inside]
  exact Finset.sum_congr rfl fun word _ => fixedWord_eq_simplex source hidden A n word start inside

section SourceCompression

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def selectedRegion : Set (WordHistory ι) :=
  {history | ∀ k, history.1.2 k ∈ hidden}

omit [Fintype ι] in
theorem selectedRegion_measurable : MeasurableSet (selectedRegion hidden) := by
  classical
  change MeasurableSet[⨅ chart : WordChart ι,
    MeasurableSpace.map (Sigma.mk chart) inferInstance] (selectedRegion hidden)
  rw [MeasurableSpace.measurableSet_iInf]
  intro chart
  change MeasurableSet {times : Fin chart.1 → ℝ | ∀ k, chart.2 k ∈ hidden}
  by_cases admitted : ∀ k, chart.2 k ∈ hidden
  · have all : {times : Fin chart.1 → ℝ | ∀ k, chart.2 k ∈ hidden} = univ :=
      Set.eq_univ_of_forall (fun _ => admitted)
    rw [all]
    exact MeasurableSet.univ
  · simpa only [admitted, ofPred_false] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set (Fin chart.1 → ℝ)))

def selectedWave (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    Lp E 2 (baseMeasure source start) :=
  ((Lp.memLp (wave source start inside x)).indicator (selectedRegion_measurable hidden)).toLp
    ((selectedRegion hidden).indicator (wave source start inside x))

theorem selectedWave_ae (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    selectedWave source hidden start inside x =ᵐ[baseMeasure source start]
      (selectedRegion hidden).indicator (wordFunction source start x) := by
  classical
  filter_upwards [((Lp.memLp (wave source start inside x)).indicator
    (selectedRegion_measurable hidden)).coeFn_toLp, wave_ae source start inside x]
    with history selected original
  change selectedWave source hidden start inside x history =
    (selectedRegion hidden).indicator (wave source start inside x) history at selected
  rw [selected]
  by_cases admitted : history ∈ selectedRegion hidden <;> simp [admitted, original]

theorem selectedWave_norm_le (start : ℝ) (inside : start ∈ Icc source.left source.right) (x : E) :
    ‖selectedWave source hidden start inside x‖ ≤ ‖x‖ := by
  rw [selectedWave, Lp.norm_toLp, ← wave_norm source start inside x, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_indicator_le _)

private theorem selectedWave_add (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (x y : E) :
    selectedWave source hidden start inside (x+y) =
      selectedWave source hidden start inside x + selectedWave source hidden start inside y := by
  classical
  apply Lp.ext
  filter_upwards [selectedWave_ae source hidden start inside (x+y),
    selectedWave_ae source hidden start inside x, selectedWave_ae source hidden start inside y,
    Lp.coeFn_add (selectedWave source hidden start inside x)
      (selectedWave source hidden start inside y)] with history whole hx hy added
  rw [whole, added, Pi.add_apply, hx, hy]
  by_cases admitted : history ∈ selectedRegion hidden <;>
    simp [admitted, wordFunction, map_add]

private theorem selectedWave_smul (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (c : ℂ) (x : E) :
    selectedWave source hidden start inside (c • x) = c • selectedWave source hidden start inside x := by
  classical
  apply Lp.ext
  filter_upwards [selectedWave_ae source hidden start inside (c • x),
    selectedWave_ae source hidden start inside x,
    Lp.coeFn_smul c (selectedWave source hidden start inside x)] with history whole hx scaled
  rw [whole, scaled, Pi.smul_apply, hx]
  by_cases admitted : history ∈ selectedRegion hidden <;>
    simp [admitted, wordFunction, map_smul]

/-- A measurable source restriction of291; its norm is at most one, not assumed isometric. -/
def selectedSourceMap (start : ℝ) (inside : start ∈ Icc source.left source.right) :
    E →L[ℂ] Lp E 2 (baseMeasure source start) :=
  ({toFun := selectedWave source hidden start inside
    map_add' := selectedWave_add source hidden start inside
    map_smul' := selectedWave_smul source hidden start inside} :
      E →ₗ[ℂ] Lp E 2 (baseMeasure source start)).mkContinuous 1
        (fun x => by
          change ‖selectedWave source hidden start inside x‖ ≤ 1 * ‖x‖
          simpa only [one_mul] using selectedWave_norm_le source hidden start inside x)

theorem selectedSourceMap_norm_le (start : ℝ) (inside : start ∈ Icc source.left source.right) :
    ‖selectedSourceMap source hidden start inside‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (fun x => by
      change ‖selectedWave source hidden start inside x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using selectedWave_norm_le source hidden start inside x)

def endpointEffect (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (A : Operator (E := E)) : Operator (E := E) :=
  (selectedSourceMap source hidden start inside).adjoint.comp
    ((A.compLpL 2 (baseMeasure source start)).comp (selectedSourceMap source hidden start inside))

theorem endpointEffect_norm_le (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (A : Operator (E := E)) : ‖endpointEffect source hidden start inside A‖ ≤ ‖A‖ := by
  let S := selectedSourceMap source hidden start inside
  have bounded : ‖S‖ ≤ 1 := selectedSourceMap_norm_le source hidden start inside
  calc
    _ ≤ ‖S.adjoint‖ * (‖A.compLpL 2 (baseMeasure source start)‖ * ‖S‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = ‖S‖ * (‖A.compLpL 2 (baseMeasure source start)‖ * ‖S‖) := by
      rw [LinearIsometryEquiv.norm_map]
    _ ≤ 1 * (‖A‖ * 1) := by
      gcongr
      exact A.norm_compLpL_le
    _ = _ := by ring

theorem selectedSourceMap_univ (start : ℝ) (inside : start ∈ Icc source.left source.right) :
    selectedSourceMap source Finset.univ start inside =
      (sourceIsometry source start inside).toContinuousLinearMap := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  apply Lp.ext
  filter_upwards [selectedWave_ae source Finset.univ start inside x,
    wave_ae source start inside x] with history selected original
  change selectedWave source Finset.univ start inside x history = wave source start inside x history
  rw [selected,original]
  have admitted : history ∈ selectedRegion (Finset.univ : Finset ι) := by
    intro k
    exact Finset.mem_univ _
  exact Set.indicator_of_mem admitted _

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem pointwise_identity (start : ℝ) :
    (1 : Operator (E := E)).compLpL 2 (baseMeasure source start) = 1 := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  exact (1 : Operator (E := E)).coeFn_compLpL field

theorem endpointEffect_univ_identity (start : ℝ)
    (inside : start ∈ Icc source.left source.right) :
    endpointEffect source Finset.univ start inside 1 = 1 := by
  rw [endpointEffect, selectedSourceMap_univ, pointwise_identity]
  change (sourceIsometry source start inside).toContinuousLinearMap.adjoint.comp
    (sourceIsometry source start inside).toContinuousLinearMap = 1
  exact (sourceIsometry source start inside).adjoint_comp_self

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem pointwise_positive (start : ℝ) (A : Operator (E := E))
    (positive : A.IsPositive) : (A.compLpL 2 (baseMeasure source start)).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro field
  let q : WordHistory ι → ℂ := fun history => inner ℂ (A (field history)) (field history)
  have actual : inner ℂ (A.compLpL 2 (baseMeasure source start) field) field =
      ((∫ history, (q history).re ∂baseMeasure source start : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ history, q history ∂baseMeasure source start := by
        apply integral_congr_ae
        filter_upwards [A.coeFn_compLpL field] with history acted
        rw [acted]
      _ = ∫ history, ((q history).re : ℂ) ∂baseMeasure source start := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun history =>
          (((ContinuousLinearMap.isPositive_iff_complex A).mp positive) (field history)).1.symm
      _ = _ := integral_ofReal
  let value : ℝ := ∫ history, (q history).re ∂baseMeasure source start
  constructor
  · rw [actual]
    change (Complex.re (Complex.ofReal value) : ℂ) = Complex.ofReal value
    exact congrArg Complex.ofReal (Complex.ofReal_re value)
  · rw [actual]
    change (0 : ℝ) ≤ Complex.re (Complex.ofReal value)
    rw [Complex.ofReal_re]
    apply integral_nonneg
    intro history
    have point := (((ContinuousLinearMap.isPositive_iff_complex A).mp positive) (field history)).2
    change (0 : ℝ) ≤ (q history).re at point
    exact point

theorem endpointEffect_positive (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (A : Operator (E := E)) (positive : A.IsPositive) :
    (endpointEffect source hidden start inside A).IsPositive :=
  (pointwise_positive source start A positive).adjoint_conj
    (selectedSourceMap source hidden start inside)

theorem endpointEffect_identity_quadratic (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (x : E) :
    (inner ℂ x (endpointEffect source hidden start inside 1 x)).re =
      ‖selectedSourceMap source hidden start inside x‖^2 := by
  rw [endpointEffect, pointwise_identity, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

theorem endpointEffect_subunital (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (x : E) : (inner ℂ x (endpointEffect source hidden start inside 1 x)).re ≤ ‖x‖^2 := by
  rw [endpointEffect_identity_quadratic]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr
    (selectedWave_norm_le source hidden start inside x)

def endpointPairing (start : ℝ) (A : Operator (E := E)) (x y : E)
    (history : WordHistory ι) : ℂ :=
  (selectedRegion hidden).indicator (fun point =>
    inner ℂ (wordFunction source start x point) (A (wordFunction source start y point))) history

private theorem source_pairing_ae (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (A : Operator (E := E)) (x y : E) :
    (fun history => inner ℂ (selectedSourceMap source hidden start inside x history)
      ((A.compLpL 2 (baseMeasure source start))
        (selectedSourceMap source hidden start inside y) history)) =ᵐ[baseMeasure source start]
      endpointPairing source hidden start A x y := by
  classical
  filter_upwards [selectedWave_ae source hidden start inside x,
    selectedWave_ae source hidden start inside y,
    A.coeFn_compLpL (selectedSourceMap source hidden start inside y)] with history hx hy acted
  change (A.compLpL 2 (baseMeasure source start))
    (selectedWave source hidden start inside y) history =
      A (selectedWave source hidden start inside y history) at acted
  change inner ℂ (selectedWave source hidden start inside x history)
    ((A.compLpL 2 (baseMeasure source start))
      (selectedWave source hidden start inside y) history) = _
  rw [acted, hx, hy]
  by_cases admitted : history ∈ selectedRegion hidden <;> simp [endpointPairing, admitted]

theorem endpointPairing_integrable (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (A : Operator (E := E)) (x y : E) :
    Integrable (endpointPairing source hidden start A x y) (baseMeasure source start) :=
  (L2.integrable_inner (selectedSourceMap source hidden start inside x)
    ((A.compLpL 2 (baseMeasure source start)) (selectedSourceMap source hidden start inside y))).congr
      (source_pairing_ae source hidden start inside A x y)

theorem endpointEffect_pairing (start : ℝ) (inside : start ∈ Icc source.left source.right)
    (A : Operator (E := E)) (x y : E) :
    inner ℂ x (endpointEffect source hidden start inside A y) =
      ∫ history, endpointPairing source hidden start A x y history ∂baseMeasure source start := by
  rw [endpointEffect, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    L2.inner_def]
  exact integral_congr_ae (source_pairing_ae source hidden start inside A x y)

private def includedChart (start : ℝ) (n : ℕ) (word : Fin n → ι) : Measure (WordHistory ι) :=
  (volume.restrict (simplex start source.right n)).map
    (fun times : Fin n → ℝ => (⟨⟨n,word⟩,times⟩ : WordHistory ι))

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
private theorem sourceMeasure_by_number (start : ℝ) :
    baseMeasure source start = Measure.sum fun n : ℕ =>
      Measure.sum fun word : Fin n → ι => includedChart source start n word := by
  ext measurableSet measurable
  simp only [baseMeasure, Measure.sum_apply _ measurable]
  exact ENNReal.tsum_sigma' (β := fun n : ℕ => Fin n → ι)
    (fun chart => includedChart source start chart.1 chart.2 measurableSet)

private def admittedWordsEquiv (n : ℕ) :
    {word : Fin n → ι // ∀ k, word k ∈ hidden} ≃ (Fin n → Letters hidden) where
  toFun word k := ⟨word.val k, word.property k⟩
  invFun word := ⟨physicalWord hidden word, fun k => (word k).property⟩
  left_inv word := rfl
  right_inv word := by funext k; rfl

open scoped Classical in
private theorem sum_admitted {F : Type*} [AddCommMonoid F] (n : ℕ)
    (f : (Fin n → ι) → F) :
    (∑ word : Fin n → ι, if ∀ k, word k ∈ hidden then f word else 0) =
      ∑ word : Fin n → Letters hidden, f (physicalWord hidden word) := by
  classical
  calc
    _ = ∑ word ∈ Finset.univ.filter (fun word : Fin n → ι => ∀ k, word k ∈ hidden), f word := by
      rw [Finset.sum_filter]
    _ = ∑ word : {word : Fin n → ι // ∀ k, word k ∈ hidden}, f word.val :=
      Finset.sum_subtype _ (fun word => by simp) f
    _ = _ := by
      exact (Equiv.sum_comp (admittedWordsEquiv hidden n).symm
        (fun word : {word : Fin n → ι // ∀ k, word k ∈ hidden} => f word.val)).symm

theorem complete_word_pairing_hasSum (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (A : Operator (E := E)) (x y : E) :
    HasSum (fun n => ∑ word : Fin n → Letters hidden,
      ∫ times in simplex start source.right n,
        inner ℂ (amplitude source n start (physicalWord hidden word) times x)
          (A (amplitude source n start (physicalWord hidden word) times y)))
      (inner ℂ x (endpointEffect source hidden start inside A y)) := by
  classical
  let f := endpointPairing source hidden start A x y
  have hf : Integrable f (baseMeasure source start) :=
    endpointPairing_integrable source hidden start inside A x y
  have regrouped : Integrable f (Measure.sum fun n : ℕ =>
      Measure.sum fun word : Fin n → ι => includedChart source start n word) := by
    rw [← sourceMeasure_by_number source start]
    exact hf
  have paid := hasSum_integral_measure regrouped
  have each (n : ℕ) :
      (∫ history, f history ∂Measure.sum fun word : Fin n → ι => includedChart source start n word) =
        ∑ word : Fin n → Letters hidden,
          ∫ times in simplex start source.right n,
            inner ℂ (amplitude source n start (physicalWord hidden word) times x)
              (A (amplitude source n start (physicalWord hidden word) times y)) := by
    have oneNumber : Integrable f
        (Measure.sum fun word : Fin n → ι => includedChart source start n word) :=
      regrouped.mono_measure (Measure.le_sum _ n)
    rw [integral_sum_measure oneNumber, tsum_fintype]
    have chart (word : Fin n → ι) :
        (∫ history, f history ∂includedChart source start n word) =
          if ∀ k, word k ∈ hidden then
            ∫ times in simplex start source.right n,
              inner ℂ (amplitude source n start word times x) (A (amplitude source n start word times y))
          else 0 := by
      have measurable : Measurable (fun times : Fin n → ℝ =>
          (⟨⟨n,word⟩,times⟩ : WordHistory ι)) := by
        apply Measurable.of_le_map
        change (⨅ chart : WordChart ι, MeasurableSpace.map
          (fun times : Fin chart.1 → ℝ => (⟨chart,times⟩ : WordHistory ι))
          (inferInstance : MeasurableSpace (Fin chart.1 → ℝ))) ≤
            MeasurableSpace.map
              (fun times : Fin n → ℝ => (⟨⟨n,word⟩,times⟩ : WordHistory ι))
              (inferInstance : MeasurableSpace (Fin n → ℝ))
        exact iInf_le _ (⟨n,word⟩ : WordChart ι)
      have hchart := oneNumber.mono_measure (Measure.le_sum _ word)
      rw [includedChart, integral_map measurable.aemeasurable hchart.aestronglyMeasurable]
      by_cases admitted : ∀ k, word k ∈ hidden <;>
        simp [f, endpointPairing, selectedRegion, admitted, wordFunction]
    simp_rw [chart]
    exact sum_admitted hidden n _
  have total : (∫ history, f history ∂Measure.sum fun n : ℕ =>
      Measure.sum fun word : Fin n → ι => includedChart source start n word) =
        inner ℂ x (endpointEffect source hidden start inside A y) := by
    rw [← sourceMeasure_by_number source start]
    exact (endpointEffect_pairing source hidden start inside A x y).symm
  simpa only [each,total] using paid

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem endpointWord_matrixElement (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (A : Operator (E := E))
    (n : ℕ) (x y : E) :
    matrixElement x y (endpointWord source hidden A n start) =
      ∑ word : Fin n → Letters hidden, ∫ times in simplex start source.right n,
        inner ℂ (amplitude source n start (physicalWord hidden word) times x)
          (A (amplitude source n start (physicalWord hidden word) times y)) := by
  rw [endpointWord_eq_simplex source hidden A n start inside, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [← (matrixElement x y).integral_comp_comm
    (simplex_integrable n start source.right _ (wordKernel_continuous source hidden A n start word))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun times =>
    ContinuousLinearMap.adjoint_inner_right
      (amplitude source n start (physicalWord hidden word) times) x
      (A (amplitude source n start (physicalWord hidden word) times y))

theorem endpointWord_pairing_hasSum (start : ℝ)
    (inside : start ∈ Icc source.left source.right) (A : Operator (E := E)) (x y : E) :
    HasSum (fun n => matrixElement x y (endpointWord source hidden A n start))
      (inner ℂ x (endpointEffect source hidden start inside A y)) := by
  simpa only [endpointWord_matrixElement source hidden start inside A] using
    complete_word_pairing_hasSum source hidden start inside A x y

end SourceCompression

end SourceEndpointWords300
