import H0mework.Versions.R7c8399ec.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceKrausSurvivalRha0285.SourceR0006.SourceKrausSurvival285
import H0mework.Physics.DiracEvolution.GalerkinEvolution
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! A common source flow generates continuous hidden-word amplitudes.

The two clock arguments are evaluations of two fixed fundamental solutions.
They are not independent selections of interval solutions.  Complex-linear
operators remain complex-linear while the existing real-time IVP producer acts
on their Banach space.  Every finite hidden word has its own real ordered time
simplex, including the zero-letter chart.  The countable chart measure below is
generated from these amplitudes; no density or measure enters its input.

The finite-window law constructed here keeps the full Kraus inventory in K and
selects only the designated traced letters for hidden words.  The instrument's
retained Fock amplitudes, public/CEM seam and full physical-law identification
consume this cell constructor separately; radiative coherent arms are not
summed as independent positive hidden histories.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxErrors 80

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ENNReal

namespace SourceHiddenWordFlow286

open SourceKrausSurvival285
open SaturationMonoid.PhysicsCore.StageNineDiracMatterGalerkinEvolution

universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {ι : Type v} [Fintype ι]

private def leftAction (A : Operator (E := E)) :
    Operator (E := E) →L[ℝ] Operator (E := E) :=
  (ContinuousLinearMap.compL ℂ E E E A).restrictScalars ℝ

omit [CompleteSpace E] in
private theorem leftAction_continuous (A : ℝ → Operator (E := E))
    (hA : Continuous A) : Continuous (fun t => leftAction (A t)) :=
  (ContinuousLinearMap.restrictScalarsIsometry ℂ
    (Operator (E := E)) (Operator (E := E)) ℝ ℝ).continuous.comp
    ((ContinuousLinearMap.compL ℂ E E E).continuous.comp hA)

/-- The original Banach IVP acts directly on complex operators from identity. -/
def operatorFlow (A : ℝ → Operator (E := E)) (hA : Continuous A)
    (a b : ℝ) (hab : a ≤ b) (t : ℝ) : Operator (E := E) :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun s => leftAction (A s)) (leftAction_continuous A hA)
    (1 : Operator (E := E)) a b hab).choose t

theorem operatorFlow_initial (A : ℝ → Operator (E := E)) (hA : Continuous A)
    (a b : ℝ) (hab : a ≤ b) : operatorFlow A hA a b hab a = 1 :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun s => leftAction (A s)) (leftAction_continuous A hA)
    (1 : Operator (E := E)) a b hab).choose_spec.1

theorem operatorFlow_derivative (A : ℝ → Operator (E := E)) (hA : Continuous A)
    (a b : ℝ) (hab : a ≤ b) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (operatorFlow A hA a b hab)
      ((A t).comp (operatorFlow A hA a b hab t)) (Icc a b) t :=
  (exists_galerkinLinearCoefficientCurve_on_Icc
    (fun s => leftAction (A s)) (leftAction_continuous A hA)
    (1 : Operator (E := E)) a b hab).choose_spec.2 t ht

theorem operatorFlow_continuous (A : ℝ → Operator (E := E)) (hA : Continuous A)
    (a b : ℝ) (hab : a ≤ b) : ContinuousOn (operatorFlow A hA a b hab) (Icc a b) :=
  fun t ht => (operatorFlow_derivative A hA a b hab t ht).continuousWithinAt

private theorem applied_flow_derivative (A : ℝ → Operator (E := E)) (hA : Continuous A)
    (a b : ℝ) (hab : a ≤ b) (x : E) (t : ℝ) (ht : t ∈ Icc a b) :
    HasDerivWithinAt (fun s => operatorFlow A hA a b hab s x)
      (A t (operatorFlow A hA a b hab t x)) (Icc a b) t := by
  have written := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
    t (operatorFlow_derivative A hA a b hab t ht)
  change HasDerivWithinAt (fun s => operatorFlow A hA a b hab s x)
    ((A t).comp (operatorFlow A hA a b hab t) x) (Icc a b) t at written
  simpa only [ContinuousLinearMap.comp_apply] using written

/-- An arbitrary finite source window contains only its original continuous
raw coefficients. Bounds and flows are generated after this input. -/
structure RawKrausWindow (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (ι : Type v) [Fintype ι] where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  halfHamiltonian : ℝ → E →L[ℂ] E
  jumps : ℝ → ι → E →L[ℂ] E
  halfHamiltonian_continuous : ContinuousOn halfHamiltonian (Icc left right)
  jumps_continuous : ∀ j, ContinuousOn (fun t => jumps t j) (Icc left right)

namespace RawKrausWindow

variable [Nontrivial E]
variable (source : RawKrausWindow E ι)

private theorem jump_peak_exists (j : ι) :
    ∃ t ∈ Icc source.left source.right,
      ∀ s ∈ Icc source.left source.right, ‖source.jumps s j‖ ≤ ‖source.jumps t j‖ :=
  isCompact_Icc.exists_isMaxOn ⟨source.left,left_mem_Icc.mpr source.ordered⟩
    (source.jumps_continuous j).norm

/-- The entire original jump inventory supplies its own finite activity bounds. -/
def jump_bounds (j : ι) : ℝ≥0 :=
  ‖source.jumps (source.jump_peak_exists j).choose j‖₊

theorem jumps_norm (t : ℝ) (ht : t ∈ Icc source.left source.right) (j : ι) :
    ‖source.jumps t j‖ ≤ source.jump_bounds j := by
  change ‖source.jumps t j‖ ≤ ‖source.jumps (source.jump_peak_exists j).choose j‖
  exact (source.jump_peak_exists j).choose_spec.2 t ht

def coefficient (t : ℝ) : Operator (E := E) :=
  generator (source.halfHamiltonian t) (source.jumps t)

theorem coefficient_continuous : ContinuousOn source.coefficient (Icc source.left source.right) := by
  have adjoint_continuous :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous
  have coherent : ContinuousOn (fun t => hamiltonian (source.halfHamiltonian t)) (Icc source.left source.right) :=
    source.halfHamiltonian_continuous.add (adjoint_continuous.comp_continuousOn source.halfHamiltonian_continuous)
  have gram : ContinuousOn (fun t => krausGram (source.jumps t)) (Icc source.left source.right) := by
    exact continuousOn_finsetSum Finset.univ fun j _ =>
      (adjoint_continuous.comp_continuousOn (source.jumps_continuous j)).mul (source.jumps_continuous j)
  exact (coherent.const_smul (-Complex.I)).sub (gram.const_smul (1 / 2 : ℂ))


def timeProjection (t : ℝ) : Icc source.left source.right :=
  projIcc source.left source.right source.ordered t

def clampedCoefficient (t : ℝ) : Operator (E := E) :=
  source.coefficient (source.timeProjection t)

theorem clampedCoefficient_continuous : Continuous source.clampedCoefficient :=
  source.coefficient_continuous.comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc (h := source.ordered))) fun t => (source.timeProjection t).2

theorem clampedCoefficient_original (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    source.clampedCoefficient t = source.coefficient t := by
  simp only [clampedCoefficient, timeProjection, projIcc_of_mem source.ordered ht]

def dualCoefficient (t : ℝ) : Operator (E := E) :=
  ContinuousLinearMap.adjoint (source.clampedCoefficient t)

theorem dualCoefficient_continuous : Continuous source.dualCoefficient :=
  (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp
    source.clampedCoefficient_continuous

theorem coefficient_dual (t : ℝ) (x y : E) :
    inner ℂ (source.clampedCoefficient t x) y = inner ℂ x (source.dualCoefficient t y) := by
  exact (ContinuousLinearMap.adjoint_inner_right (source.clampedCoefficient t) x y).symm

def forward : ℝ → Operator (E := E) :=
  operatorFlow source.clampedCoefficient source.clampedCoefficient_continuous
    source.left source.right source.ordered

def backward : ℝ → Operator (E := E) :=
  operatorFlow (fun t => -source.dualCoefficient t) source.dualCoefficient_continuous.neg
    source.left source.right source.ordered

theorem forward_derivative (x : E) (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    HasDerivWithinAt (fun s => source.forward s x)
      (source.clampedCoefficient t (source.forward t x)) (Icc source.left source.right) t :=
  applied_flow_derivative _ _ _ _ _ x t ht

theorem backward_derivative (x : E) (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    HasDerivWithinAt (fun s => source.backward s x)
      (-source.dualCoefficient t (source.backward t x)) (Icc source.left source.right) t :=
  applied_flow_derivative _ _ _ _ _ x t ht

private theorem pairing_constant (x y : ℝ → E) (b : ℝ)
    (hb : source.left ≤ b)
    (dx : ∀ t ∈ Icc source.left b, HasDerivWithinAt x
      (source.clampedCoefficient t (x t)) (Icc source.left b) t)
    (dy : ∀ t ∈ Icc source.left b, HasDerivWithinAt y
      (-source.dualCoefficient t (y t)) (Icc source.left b) t) :
    inner ℂ (x b) (y b) = inner ℂ (x source.left) (y source.left) := by
  have first : ContinuousOn x (Icc source.left b) := fun t ht => (dx t ht).continuousWithinAt
  have last : ContinuousOn y (Icc source.left b) := fun t ht => (dy t ht).continuousWithinAt
  have derivative (t : ℝ) (ht : t ∈ Ioo source.left b) :
      HasDerivAt (fun s => inner ℂ (x s) (y s)) 0 t := by
    have before := (dx t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have after := (dy t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    convert! before.inner ℂ after using 1
    rw [inner_neg_right, source.coefficient_dual]
    ring
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
    (first.inner (𝕜 := ℂ) last) derivative (intervalIntegrable_const (c := (0 : ℂ)))
  rw [intervalIntegral.integral_zero] at written
  exact sub_eq_zero.mp written.symm

private theorem exists_terminal_backward (b : ℝ) (hb : source.left ≤ b) (x : E) :
    ∃ path : ℝ → E, path b = x ∧ ∀ t ∈ Icc source.left b,
      HasDerivWithinAt path (-source.dualCoefficient t (path t)) (Icc source.left b) t := by
  have continuous : Continuous (fun t => (source.dualCoefficient (-t)).restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ).continuous.comp
      (source.dualCoefficient_continuous.comp continuous_neg)
  obtain ⟨path, initial, evolution⟩ := exists_galerkinLinearCoefficientCurve_on_Icc
    (fun t => (source.dualCoefficient (-t)).restrictScalars ℝ) continuous
    x (-b) (-source.left) (neg_le_neg hb)
  refine ⟨fun t => path (-t), initial, ?_⟩
  intro t ht
  have into : MapsTo (fun s : ℝ => -s) (Icc source.left b) (Icc (-b) (-source.left)) := by
    intro s hs
    constructor <;> linarith [hs.1,hs.2]
  have actual := (evolution (-t) (into ht)).scomp t (hasDerivAt_neg t).hasDerivWithinAt into
  simp only [neg_neg, neg_smul, one_smul, galerkinLinearVelocity] at actual
  change HasDerivWithinAt (fun s => path (-s))
    (-source.dualCoefficient t (path (-t))) (Icc source.left b) t at actual
  exact actual

private theorem terminal_endpoint (b : ℝ) (hb : b ∈ Icc source.left source.right)
    (x : E) (path : ℝ → E) (atEnd : path b = x)
    (evolution : ∀ t ∈ Icc source.left b, HasDerivWithinAt path
      (-source.dualCoefficient t (path t)) (Icc source.left b) t) :
    (source.forward b).adjoint x = path source.left := by
  apply ext_inner_left ℂ
  intro initial
  have subset : Icc source.left b ⊆ Icc source.left source.right :=
    Icc_subset_Icc le_rfl hb.2
  have atStart : source.forward source.left initial = initial := by
    rw [forward, operatorFlow_initial]
    rfl
  have same := source.pairing_constant (fun t => source.forward t initial) path b hb.1
    (fun t ht => (source.forward_derivative initial t (subset ht)).mono subset) evolution
  rw [atStart, atEnd] at same
  exact (ContinuousLinearMap.adjoint_inner_right (source.forward b) initial x).trans same

def backwardKernel (s t : ℝ) : Operator (E := E) :=
  (source.backward s).comp (source.forward t).adjoint

theorem backwardKernel_terminal (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    source.backwardKernel t t = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨path,atEnd,evolution⟩ := source.exists_terminal_backward t ht.1 x
  have endpoint := source.terminal_endpoint t ht x path atEnd evolution
  have subset : Icc source.left t ⊆ Icc source.left source.right :=
    Icc_subset_Icc le_rfl ht.2
  have continuity : Continuous (fun r => (-source.dualCoefficient r).restrictScalars ℝ) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ).continuous.comp
      source.dualCoefficient_continuous.neg
  have same := galerkinLinearCoefficientCurve_eqOn_Icc
    (fun r => (-source.dualCoefficient r).restrictScalars ℝ) continuity
    (fun r => source.backwardKernel r t x) path (path source.left)
    source.left t ht.1
    (by
      change source.backward source.left ((source.forward t).adjoint x) = path source.left
      rw [backward, operatorFlow_initial]
      exact endpoint)
    rfl
    (fun r hr => by
      change HasDerivWithinAt (fun s => source.backward s ((source.forward t).adjoint x))
        (-source.dualCoefficient r (source.backward r ((source.forward t).adjoint x)))
        (Icc source.left t) r
      exact (source.backward_derivative ((source.forward t).adjoint x) r (subset hr)).mono subset)
    (fun r hr => by
      change HasDerivWithinAt path (-source.dualCoefficient r (path r)) (Icc source.left t) r
      exact evolution r hr)
  exact (same (right_mem_Icc.mpr ht.1)).trans atEnd

/-- Both clocks evaluate the same two generated fundamental solutions. -/
def propagate (s t : ℝ) : Operator (E := E) :=
  (source.forward t).comp (source.backward s).adjoint

theorem propagate_initial (s : ℝ) (hs : s ∈ Icc source.left source.right) :
    source.propagate s s = 1 := by
  have reflected := congrArg (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E))
    (source.backwardKernel_terminal s hs)
  simpa only [backwardKernel, propagate, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_one] using reflected

theorem propagate_derivative (s : ℝ) (x : E) (t : ℝ)
    (ht : t ∈ Icc source.left source.right) :
    HasDerivWithinAt (fun r => source.propagate s r x)
      (source.clampedCoefficient t (source.propagate s t x))
      (Icc source.left source.right) t :=
  source.forward_derivative ((source.backward s).adjoint x) t ht

theorem propagate_continuous : ContinuousOn
    (fun pair : ℝ × ℝ => source.propagate pair.1 pair.2)
    ((Icc source.left source.right) ×ˢ (Icc source.left source.right)) := by
  have forward_cont : ContinuousOn source.forward (Icc source.left source.right) :=
    operatorFlow_continuous _ _ _ _ _
  have backward_cont : ContinuousOn source.backward (Icc source.left source.right) :=
    operatorFlow_continuous _ _ _ _ _
  exact ContinuousOn.clm_comp (𝕜 := ℂ) (E := E) (F := E) (G := E)
    (forward_cont.comp continuous_snd.continuousOn fun _ h => h.2)
    (((ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).continuous.comp_continuousOn
      backward_cont).comp continuous_fst.continuousOn fun _ h => h.1)

theorem propagate_contracts (s t : ℝ) (hs : source.left ≤ s) (hst : s ≤ t)
    (ht : t ≤ source.right) (x : E) : ‖source.propagate s t x‖ ≤ ‖x‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have subset : Icc s t ⊆ Icc source.left source.right := Icc_subset_Icc hs ht
  have energy (r : ℝ) (hr : r ∈ Icc s t) :=
    ((source.propagate_derivative s x r (subset hr)).mono subset).norm_sq
  have decreasing : AntitoneOn (fun r => ‖source.propagate s r x‖ ^ 2) (Icc s t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
      (fun r hr => (energy r hr).continuousWithinAt)
    · intro r hr
      exact (energy r (interior_subset hr)).mono interior_subset
    · intro r _
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      change (inner ℂ (source.propagate s r x)
        (source.clampedCoefficient r (source.propagate s r x))).re ≤ 0
      exact generator_dissipative _ _ _
  have paid := decreasing (left_mem_Icc.mpr hst) (right_mem_Icc.mpr hst) hst
  change ‖source.propagate s t x‖ ^ 2 ≤ ‖source.propagate s s x‖ ^ 2 at paid
  have atStart : source.propagate s s x = x := by
    exact congrArg (fun U : Operator (E := E) => U x)
      (source.propagate_initial s ⟨hs,hst.trans ht⟩)
  rw [atStart] at paid
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp paid

theorem propagate_jump_energy (s : ℝ) (x : E) (t : ℝ)
    (ht : t ∈ Icc source.left source.right) :
    HasDerivWithinAt (fun r => ‖source.propagate s r x‖ ^ 2)
      (-(∑ j, ‖source.jumps t j (source.propagate s t x)‖ ^ 2))
      (Icc source.left source.right) t := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply (source.propagate_derivative s x t ht).norm_sq.congr_deriv
  change 2 * (inner ℂ (source.propagate s t x)
    (source.clampedCoefficient t (source.propagate s t x))).re = _
  rw [source.clampedCoefficient_original t ht]
  exact generator_energy _ _ _

/-- The source produces the complete first-jump/no-jump mass identity.
There is no supplied probability kernel or normalizer in this mouth. -/
theorem survival_plus_first_jump (s t : ℝ) (hs : source.left ≤ s) (hst : s ≤ t)
    (ht : t ≤ source.right) (x : E) :
    ‖source.propagate s t x‖ ^ 2 +
      (∫ r in s..t, ∑ j, ‖source.jumps r j (source.propagate s r x)‖ ^ 2) = ‖x‖ ^ 2 := by
  have subset : Icc s t ⊆ Icc source.left source.right := Icc_subset_Icc hs ht
  have path_cont : ContinuousOn (fun r => source.propagate s r x) (Icc s t) :=
    fun r hr => ((source.propagate_derivative s x r (subset hr)).mono subset).continuousWithinAt
  have activity_cont : ContinuousOn
      (fun r => ∑ j, ‖source.jumps r j (source.propagate s r x)‖ ^ 2) (Icc s t) :=
    continuousOn_finsetSum Finset.univ fun j _ =>
      (((source.jumps_continuous j).mono subset).clm_apply path_cont).norm.pow 2
  have energy (r : ℝ) (hr : r ∈ Icc s t) :=
    (source.propagate_jump_energy s x r (subset hr)).mono subset
  have written := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hst
    (path_cont.norm.pow 2)
    (fun r hr => (energy r (Ioo_subset_Icc_self hr)).hasDerivAt (Icc_mem_nhds hr.1 hr.2))
    (activity_cont.neg.intervalIntegrable_of_Icc hst)
  have initial : source.propagate s s x = x :=
    congrArg (fun U : Operator (E := E) => U x) (source.propagate_initial s ⟨hs,hst.trans ht⟩)
  simp only [Pi.pow_apply] at written
  rw [intervalIntegral.integral_neg, initial] at written
  linarith

def activityBound : ℝ≥0 := ∑ j, source.jump_bounds j ^ 2

/-- A raw source bound controls every first-jump branch uniformly in its
incoming vector; it is independent of a completed or normalized path law. -/
theorem first_jump_density_bound (s t : ℝ) (hs : source.left ≤ s) (hst : s ≤ t)
    (ht : t ≤ source.right) (x : E) :
    (∑ j, ‖source.jumps t j (source.propagate s t x)‖ ^ 2) ≤
      (source.activityBound : ℝ) * ‖x‖ ^ 2 := by
  have member : t ∈ Icc source.left source.right := ⟨hs.trans hst,ht⟩
  have survival := source.propagate_contracts s t hs hst ht x
  calc
    (∑ j, ‖source.jumps t j (source.propagate s t x)‖ ^ 2) ≤
        ∑ j, ((source.jump_bounds j : ℝ) * ‖x‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (source.jump_bounds j).coe_nonneg (norm_nonneg x))).mpr
      exact ((source.jumps t j).le_opNorm (source.propagate s t x)).trans
        (mul_le_mul (source.jumps_norm t member j) survival (norm_nonneg _)
          (source.jump_bounds j).coe_nonneg)
    _ = (source.activityBound : ℝ) * ‖x‖ ^ 2 := by
      simp only [mul_pow, ← Finset.sum_mul, activityBound, NNReal.coe_sum, NNReal.coe_pow]

/-- Clamping is solely a continuous extension for chart measurability. -/
def chartPropagator (s t : ℝ) : Operator (E := E) :=
  source.propagate (source.timeProjection s) (source.timeProjection t)

theorem chartPropagator_continuous :
    Continuous (fun pair : ℝ × ℝ => source.chartPropagator pair.1 pair.2) :=
  source.propagate_continuous.comp_continuous
    ((continuous_subtype_val.comp ((continuous_projIcc (h := source.ordered)).comp continuous_fst)).prodMk
      (continuous_subtype_val.comp ((continuous_projIcc (h := source.ordered)).comp continuous_snd)))
    fun pair => ⟨(source.timeProjection pair.1).2,(source.timeProjection pair.2).2⟩

def chartJump (j : ι) (t : ℝ) : Operator (E := E) :=
  source.jumps (source.timeProjection t) j

theorem chartJump_continuous (j : ι) : Continuous (source.chartJump j) :=
  (source.jumps_continuous j).comp_continuous
    (continuous_subtype_val.comp (continuous_projIcc (h := source.ordered))) fun t => (source.timeProjection t).2

def lastTime : (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => source.left
  | n+1, times => times (Fin.last n)

theorem lastTime_continuous (n : ℕ) : Continuous (source.lastTime n) := by
  cases n with
  | zero => exact continuous_const
  | succ n => exact continuous_apply (Fin.last n)

def prefixAmplitude (source : RawKrausWindow E ι) : (n : ℕ) → (Fin n → ι) → (Fin n → ℝ) → Operator (E := E)
  | 0, _, _ => 1
  | n+1, word, times =>
      source.chartJump (word (Fin.last n)) (times (Fin.last n)) *
        source.chartPropagator (source.lastTime n (fun i => times i.castSucc)) (times (Fin.last n)) *
        prefixAmplitude source n (fun i => word i.castSucc) (fun i => times i.castSucc)

theorem prefixAmplitude_continuous (n : ℕ) (word : Fin n → ι) :
    Continuous (source.prefixAmplitude n word) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have restriction : Continuous (fun times : Fin (n+1) → ℝ => fun i : Fin n => times i.castSucc) :=
        continuous_pi fun i => continuous_apply i.castSucc
      exact (((source.chartJump_continuous (word (Fin.last n))).comp (continuous_apply (Fin.last n))).mul
        (source.chartPropagator_continuous.comp
          (((source.lastTime_continuous n).comp restriction).prodMk (continuous_apply (Fin.last n))))).mul
        ((ih (fun i => word i.castSucc)).comp restriction)

def amplitude (n : ℕ) (word : Fin n → ι) (times : Fin n → ℝ) : Operator (E := E) :=
  source.chartPropagator (source.lastTime n times) source.right * source.prefixAmplitude n word times

theorem amplitude_continuous (n : ℕ) (word : Fin n → ι) : Continuous (source.amplitude n word) :=
  (source.chartPropagator_continuous.comp
    ((source.lastTime_continuous n).prodMk continuous_const)).mul
    (source.prefixAmplitude_continuous n word)

def orderedSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {times | (∀ i, source.left < times i ∧ times i < source.right) ∧ StrictMono times}

theorem orderedSimplex_measurable (n : ℕ) : MeasurableSet (source.orderedSimplex n) := by
  have bounds : MeasurableSet {times : Fin n → ℝ |
      ∀ i, source.left < times i ∧ times i < source.right} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
        (measurableSet_lt (measurable_pi_apply i) measurable_const)
  have order : MeasurableSet {times : Fin n → ℝ | StrictMono times} := by
    simp only [StrictMono, ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)
  exact bounds.inter order

def bornDensity (x : E) (n : ℕ) (word : Fin n → ι) (times : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖source.amplitude n word times x‖ ^ 2)

theorem bornDensity_measurable (x : E) (n : ℕ) (word : Fin n → ι) :
    Measurable (source.bornDensity x n word) := by
  have amplitude_cont : Continuous (fun times : Fin n → ℝ =>
      source.amplitude n word times x) :=
    (source.amplitude_continuous n word).clm_apply continuous_const
  exact (ENNReal.continuous_ofReal.comp (amplitude_cont.norm.pow 2)).measurable

def chartMeasure (x : E) (n : ℕ) (word : Fin n → ι) : Measure (Fin n → ℝ) :=
  (volume.restrict (source.orderedSimplex n)).withDensity (source.bornDensity x n word)

abbrev HiddenChart (hidden : Finset ι) := Σ n : ℕ, Fin n → ↥hidden
abbrev HiddenHistory (hidden : Finset ι) := Σ chart : HiddenChart hidden, Fin chart.1 → ℝ

omit [Fintype ι] in
private theorem chart_inclusion_measurable (hidden : Finset ι) (chart : HiddenChart hidden) :
    Measurable (fun times : Fin chart.1 → ℝ => (⟨chart, times⟩ : HiddenHistory hidden)) :=
  Measurable.of_le_map (iInf_le _ chart)

/-- All finite traced words are assembled without a supplied density or law. -/
def hiddenHistoryMeasure (hidden : Finset ι) (x : E) : Measure (HiddenHistory hidden) :=
  Measure.sum fun chart : HiddenChart hidden =>
    (source.chartMeasure x chart.1 (fun i => (chart.2 i).val)).map (fun times : Fin chart.1 → ℝ => (⟨chart, times⟩ : HiddenHistory hidden))

theorem hiddenHistoryMeasure_apply (hidden : Finset ι) (x : E)
    (event : Set (HiddenHistory hidden)) (measurable : MeasurableSet event) :
    source.hiddenHistoryMeasure hidden x event =
      ∑' chart : HiddenChart hidden,
        ∫⁻ times in (fun times : Fin chart.1 → ℝ =>
          (⟨chart, times⟩ : HiddenHistory hidden)) ⁻¹' event,
          source.bornDensity x chart.1 (fun i => (chart.2 i).val) times
          ∂(volume.restrict (source.orderedSimplex chart.1)) := by
  rw [hiddenHistoryMeasure, Measure.sum_apply _ measurable]
  apply tsum_congr
  intro chart
  rw [Measure.map_apply (chart_inclusion_measurable hidden chart) measurable,
    chartMeasure, MeasureTheory.withDensity_apply _ ((chart_inclusion_measurable hidden chart) measurable)]

end RawKrausWindow

end SourceHiddenWordFlow286
