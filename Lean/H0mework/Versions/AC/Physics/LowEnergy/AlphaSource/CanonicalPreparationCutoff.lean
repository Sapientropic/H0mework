import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.CanonicalPreparationCutoff
open MeasureTheory Set
open scoped Topology BigOperators ENNReal ContDiff

-- Exact generated denominator in source_symbol_compact_majorants.json.
def sourceRadius : ℝ :=
  1 / 261482289693277665651522839245015177665807101875032689157102281549211979139375767950683670540993639204670461821233693610992022788982061006528049864060729908277173566168890387875317626124106230000

theorem radius_small : 0 < sourceRadius ∧ sourceRadius < 1/800 := by
  norm_num [sourceRadius]

def sourceChi (t : ℝ) : ℝ :=
  if t ≤ 1 then 0 else if 2 ≤ t then 1 else
    Real.exp (-1/(t-1)) / (Real.exp (-1/(t-1)) + Real.exp (-1/(2-t)))

abbrev FlatConfiguration := Fin 100 → ℝ

-- The complete sparse center_z100 in the actual source compact-majorant output.
def flatSource (i : Fin 100) : ℝ :=
  if i=0 ∨ i=2 ∨ i=5 then 1 else
  if i=67 ∨ i=77 ∨ i=94 then 3*Real.sqrt 2/10 else
  if i=95 then -(3*Real.sqrt 2/10) else 0

def sourceCutFactor (distance : ℝ) : ℝ :=
  if 2*sourceRadius ≤ |distance| then 0 else
    if sourceRadius < |distance| then
      sourceChi (1+(2*sourceRadius-|distance|)/sourceRadius) else 1

theorem chi_nonnegative (t : ℝ) : 0 ≤ sourceChi t := by
  unfold sourceChi
  split_ifs <;> positivity

theorem chi_le_one (t : ℝ) : sourceChi t ≤ 1 := by
  unfold sourceChi
  split_ifs
  · norm_num
  · rfl
  · apply (div_le_one (by positivity)).mpr
    linarith [Real.exp_pos (-1/(2-t))]

theorem chi_positive {t : ℝ} (ht : 1 < t) : 0 < sourceChi t := by
  rw [sourceChi, if_neg (not_le.mpr ht)]
  split_ifs <;> positivity

theorem factor_nonnegative (d : ℝ) : 0 ≤ sourceCutFactor d := by
  unfold sourceCutFactor
  split_ifs
  · norm_num
  · exact chi_nonnegative _
  · norm_num

theorem factor_le_one (d : ℝ) : sourceCutFactor d ≤ 1 := by
  unfold sourceCutFactor
  split_ifs
  · norm_num
  · exact chi_le_one _
  · rfl

theorem factor_positive_iff (d : ℝ) : 0 < sourceCutFactor d ↔ |d| < 2*sourceRadius := by
  unfold sourceCutFactor
  by_cases hd : 2*sourceRadius ≤ |d|
  · rw [if_pos hd]
    simp only [lt_self_iff_false, false_iff]
    exact not_lt.mpr hd
  · rw [if_neg hd]
    have inside := lt_of_not_ge hd
    refine ⟨fun _ => inside, fun _ => ?_⟩
    split_ifs
    · apply chi_positive
      have quotient : 0 < (2*sourceRadius-|d|)/sourceRadius :=
        div_pos (sub_pos.mpr inside) radius_small.1
      linarith
    · norm_num

def sourcePsi (z : FlatConfiguration) : ℝ :=
  ∏ i : Fin 100, sourceCutFactor (z i-flatSource i)

def sourceOpenBox : Set FlatConfiguration := {z | ∀ i, |z i-flatSource i| < 2*sourceRadius}
def sourceClosedBox : Set FlatConfiguration := {z | ∀ i, |z i-flatSource i| ≤ 2*sourceRadius}
def sourceFaces : Set FlatConfiguration := {z | ∃ i, |z i-flatSource i| = 2*sourceRadius}

theorem sourcePsi_nonnegative (z : FlatConfiguration) : 0 ≤ sourcePsi z :=
  Finset.prod_nonneg (fun _ _ => factor_nonnegative _)

theorem sourcePsi_le_one (z : FlatConfiguration) : sourcePsi z ≤ 1 :=
  Finset.prod_le_one (fun _ _ => factor_nonnegative _) (fun _ _ => factor_le_one _)

theorem sourcePsi_positive (z : FlatConfiguration) : 0 < sourcePsi z ↔ z ∈ sourceOpenBox := by
  constructor
  · intro positive i
    by_contra outside
    have factorZero : sourceCutFactor (z i-flatSource i)=0 := by
      simp only [sourceCutFactor, if_pos (le_of_not_gt outside)]
    have wholeZero : sourcePsi z=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) factorZero
    linarith
  · intro inside
    exact Finset.prod_pos (fun i _ => (factor_positive_iff _).mpr (inside i))

theorem sourcePsi_support : Function.support sourcePsi = sourceOpenBox := by
  ext z
  change sourcePsi z ≠ 0 ↔ z ∈ sourceOpenBox
  exact ne_comm.trans ((ne_iff_lt_iff_le.mpr (sourcePsi_nonnegative z)).trans (sourcePsi_positive z))

theorem sourcePsi_at_source : sourcePsi flatSource = 1 := by
  have nonnegative : ¬ 2*sourceRadius ≤ 0 := by linarith [radius_small.1]
  have nonpositive : ¬ sourceRadius < 0 := by linarith [radius_small.1]
  simp [sourcePsi, sourceCutFactor, nonnegative, nonpositive]

theorem sourceOpenBox_open : IsOpen sourceOpenBox := by
  have expression : sourceOpenBox =
      ⋂ i : Fin 100, {z : FlatConfiguration | |z i-flatSource i| < 2*sourceRadius} := by
    ext z
    simp [sourceOpenBox]
  rw [expression]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt
    ((continuous_apply i).sub continuous_const).abs continuous_const)

theorem sourceClosedBox_closed : IsClosed sourceClosedBox := by
  have expression : sourceClosedBox =
      ⋂ i : Fin 100, {z : FlatConfiguration | |z i-flatSource i| ≤ 2*sourceRadius} := by
    ext z
    simp [sourceClosedBox]
  rw [expression]
  exact isClosed_iInter (fun i => isClosed_le
    ((continuous_apply i).sub continuous_const).abs continuous_const)

theorem sourceClosedBox_compact : IsCompact sourceClosedBox := by
  have expression : sourceClosedBox = Set.pi Set.univ (fun i : Fin 100 =>
      Icc (flatSource i-2*sourceRadius) (flatSource i+2*sourceRadius)) := by
    ext z
    simp only [sourceClosedBox, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_Icc]
    apply forall_congr'
    intro i
    rw [abs_le]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [expression]
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem sourcePsi_compact : HasCompactSupport sourcePsi := by
  have inside : tsupport sourcePsi ⊆ sourceClosedBox := by
    rw [tsupport, sourcePsi_support]
    exact closure_minimal (fun _ h i => (h i).le) sourceClosedBox_closed
  exact sourceClosedBox_compact.of_isClosed_subset isClosed_closure inside

theorem source_frontier_faces : frontier sourceOpenBox ⊆ sourceFaces := by
  have inside : closure sourceOpenBox ⊆ sourceClosedBox :=
    closure_minimal (fun _ h i => (h i).le) sourceClosedBox_closed
  intro z hz
  rw [frontier, sourceOpenBox_open.interior_eq] at hz
  have closed := inside hz.1
  have notInside : ¬ ∀ i, |z i-flatSource i| < 2*sourceRadius := hz.2
  push Not at notInside
  obtain ⟨i, hi⟩ := notInside
  exact ⟨i, le_antisymm (closed i) hi⟩

def flatMeasure : Measure FlatConfiguration := Measure.pi (fun _ : Fin 100 => volume)

theorem coordinate_hyperplane_null (i : Fin 100) (c : ℝ) :
    flatMeasure {z | z i=c}=0 := by
  change (Measure.pi (fun _ : Fin 100 => (volume : Measure ℝ)))
    (Function.eval i ⁻¹' {c})=0
  exact Measure.pi_eval_preimage_null (fun _ : Fin 100 => (volume : Measure ℝ))
    (i := i) (s := {c}) (measure_singleton c)

theorem source_faces_null : flatMeasure sourceFaces=0 := by
  have inclusion : sourceFaces ⊆ ⋃ i : Fin 100,
      ({z | z i=flatSource i+2*sourceRadius} ∪ {z | z i=flatSource i-2*sourceRadius}) := by
    rintro z ⟨i, hi⟩
    apply mem_iUnion.mpr
    refine ⟨i, ?_⟩
    by_cases positive : 0 ≤ z i-flatSource i
    · rw [abs_of_nonneg positive] at hi
      exact Or.inl (by dsimp; linarith)
    · rw [abs_of_neg (lt_of_not_ge positive)] at hi
      exact Or.inr (by dsimp; linarith)
  apply measure_mono_null inclusion
  exact measure_iUnion_null (fun i =>
    measure_union_null (coordinate_hyperplane_null i _) (coordinate_hyperplane_null i _))

theorem source_frontier_null : flatMeasure (frontier sourceOpenBox)=0 :=
  measure_mono_null source_frontier_faces source_faces_null

theorem source_frontier_density_null (w : FlatConfiguration → ℝ≥0∞) :
    (flatMeasure.withDensity w) (frontier sourceOpenBox)=0 :=
  withDensity_absolutelyContinuous flatMeasure w source_frontier_null

theorem sourceChi_transition (t : ℝ) :
    sourceChi t = Real.smoothTransition (t-1) := by
  unfold sourceChi
  split_ifs with low high
  · exact (Real.smoothTransition.zero_of_nonpos (by linarith)).symm
  · exact (Real.smoothTransition.one_of_one_le (by linarith)).symm
  · have first : ¬ t-1 ≤ 0 := by linarith
    have second : ¬ 1-(t-1) ≤ 0 := by linarith
    simp only [Real.smoothTransition, expNegInvGlue, if_neg first, if_neg second]
    rw [show 1-(t-1)=2-t from by ring]
    simp [div_eq_mul_inv]

theorem sourceChi_smooth : ContDiff ℝ ∞ sourceChi := by
  have identity : sourceChi = fun t : ℝ => Real.smoothTransition (t-1) :=
    funext sourceChi_transition
  rw [identity]
  exact Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem sourceCutFactor_transition (d : ℝ) :
    sourceCutFactor d = Real.smoothTransition (2-|d|/sourceRadius) := by
  have positive := radius_small.1
  unfold sourceCutFactor
  split_ifs with outside annulus
  · apply (Real.smoothTransition.zero_of_nonpos _).symm
    have bound : 2 ≤ |d|/sourceRadius := (le_div_iff₀ positive).mpr outside
    linarith
  · rw [sourceChi_transition]
    congr 1
    field_simp
    ring
  · apply (Real.smoothTransition.one_of_one_le _).symm
    have bound : |d|/sourceRadius ≤ 1 := (div_le_one positive).mpr (le_of_not_gt annulus)
    linarith

-- The product removes the apparent cusp of |d| at the flat plateau center.
theorem sourceCutFactor_product (d : ℝ) :
    sourceCutFactor d =
      Real.smoothTransition (2-d/sourceRadius)*Real.smoothTransition (2+d/sourceRadius) := by
  rw [sourceCutFactor_transition]
  by_cases nonnegative : 0 ≤ d
  · rw [abs_of_nonneg nonnegative]
    have bound : 1 ≤ 2+d/sourceRadius := by
      have := div_nonneg nonnegative radius_small.1.le
      linarith
    rw [Real.smoothTransition.one_of_one_le bound, mul_one]
  · have nonpositive : d ≤ 0 := le_of_not_ge nonnegative
    rw [abs_of_nonpos nonpositive]
    have bound : 1 ≤ 2-d/sourceRadius := by
      have := div_nonpos_of_nonpos_of_nonneg nonpositive radius_small.1.le
      linarith
    rw [Real.smoothTransition.one_of_one_le bound, one_mul]
    congr 1
    ring

theorem sourceCutFactor_smooth : ContDiff ℝ ∞ sourceCutFactor := by
  have identity : sourceCutFactor = fun d : ℝ =>
      Real.smoothTransition (2-d/sourceRadius)*Real.smoothTransition (2+d/sourceRadius) :=
    funext sourceCutFactor_product
  rw [identity]
  apply ContDiff.mul
  · exact Real.smoothTransition.contDiff.comp
      (contDiff_const.sub (contDiff_id.div_const sourceRadius))
  · exact Real.smoothTransition.contDiff.comp
      (contDiff_const.add (contDiff_id.div_const sourceRadius))

theorem sourcePsi_smooth : ContDiff ℝ ∞ sourcePsi := by
  unfold sourcePsi
  apply contDiff_prod
  intro i _
  exact sourceCutFactor_smooth.comp ((contDiff_apply ℝ ℝ i).sub contDiff_const)

theorem sourcePsi_measurable : Measurable sourcePsi :=
  sourcePsi_smooth.continuous.measurable

theorem actual_source_cutoff :
    ContDiff ℝ ∞ sourcePsi ∧ HasCompactSupport sourcePsi ∧ sourcePsi flatSource=1 ∧
      Function.support sourcePsi=sourceOpenBox :=
  ⟨sourcePsi_smooth, sourcePsi_compact, sourcePsi_at_source, sourcePsi_support⟩

end LowEnergy.CanonicalPreparationCutoff
#print axioms LowEnergy.CanonicalPreparationCutoff.actual_source_cutoff
