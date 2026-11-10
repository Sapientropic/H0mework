import H0mework.Versions.Rb42a6779.ReleaseMaterials.Verification.Physics.Stage10.IndependentBell.Munich.ReadoutDomain.Evidence.SourceKrausSurvivalRha0285.SourceR0004.RetardedSourceSurvival284
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Raw Kraus coefficients generate dissipativity and a contracting survival.

`halfHamiltonian` is an unconstrained coefficient source.  Its adjoint generates
its Hermitian partner; every jump contributes its own Gram operator.  No
completed propagator, positivity certificate or contraction bound is input.
The physical284 consumer must identify these source expressions with its exact
raw H/R inventory.  This file uses the Hilbert operator norm on CLM, not the
matrix row-sum norm used by the separate generic284 matrix instance.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Set
open scoped BigOperators NNReal Topology

namespace SourceKrausSurvival285

universe u v

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
variable {ι : Type v} [Fintype ι]

abbrev Operator := E →L[ℂ] E

def hamiltonian (A : Operator (E := E)) : Operator (E := E) :=
  A + ContinuousLinearMap.adjoint A

def krausGram (J : ι → Operator (E := E)) : Operator (E := E) :=
  ∑ j, ContinuousLinearMap.adjoint (J j) * J j

def generator (A : Operator (E := E)) (J : ι → Operator (E := E)) : Operator (E := E) :=
  (-Complex.I) • hamiltonian A - (1 / 2 : ℂ) • krausGram J

/-- The entire coherent Hamiltonian, including all raw phases, cancels from
its real energy pairing. -/
theorem hamiltonian_inner_im (A : Operator (E := E)) (x : E) :
    (inner ℂ x (hamiltonian A x)).im = 0 := by
  simp only [hamiltonian, add_apply, inner_add_right,
    ContinuousLinearMap.adjoint_inner_right, Complex.add_im]
  have paired := inner_im_symm (𝕜 := ℂ) x (A x)
  change (inner ℂ x (A x)).im = -(inner ℂ (A x) x).im at paired
  linarith

theorem krausGram_inner_re (J : ι → Operator (E := E)) (x : E) :
    (inner ℂ x (krausGram J x)).re = ∑ j, ‖J j x‖ ^ 2 := by
  simp only [krausGram, sum_apply, inner_sum, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  change RCLike.re (inner ℂ (J j x) (J j x)) = ‖J j x‖ ^ 2
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (J j x)

/-- The source-generated full Kraus inventory pays the exact energy square. -/
theorem generator_energy (A : Operator (E := E)) (J : ι → Operator (E := E)) (x : E) :
    2 * (inner ℂ x (generator A J x)).re = -(∑ j, ‖J j x‖ ^ 2) := by
  have coherent : (inner ℂ x ((-Complex.I) • hamiltonian A x)).re = 0 := by
    simp only [inner_smul_right, Complex.mul_re, Complex.neg_re, Complex.I_re,
      neg_zero, zero_mul, Complex.neg_im, Complex.I_im, neg_one_mul,
      zero_sub, hamiltonian_inner_im]
  have half : ((1 / 2 : ℂ) * inner ℂ x (krausGram J x)).re =
      (1 / 2 : ℝ) * (inner ℂ x (krausGram J x)).re := by
    norm_num [Complex.mul_re]
  simp only [generator, sub_apply, smul_apply,
    inner_sub_right, inner_smul_right, Complex.sub_re]
  rw [show ((-Complex.I) * inner ℂ x (hamiltonian A x)).re = 0 by
    simpa only [inner_smul_right] using coherent, half, krausGram_inner_re]
  ring

theorem generator_dissipative (A : Operator (E := E)) (J : ι → Operator (E := E)) (x : E) :
    (inner ℂ x (generator A J x)).re ≤ 0 := by
  have energy := generator_energy A J x
  have positive : 0 ≤ ∑ j, ‖J j x‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

theorem hamiltonian_norm_bound (A : Operator (E := E)) :
    ‖hamiltonian A‖ ≤ 2 * ‖A‖ := by
  calc
    ‖hamiltonian A‖ ≤ ‖A‖ + ‖ContinuousLinearMap.adjoint A‖ := norm_add_le _ _
    _ = 2 * ‖A‖ := by
      rw [(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).norm_map]
      ring

theorem krausGram_norm_bound (J : ι → Operator (E := E)) :
    ‖krausGram J‖ ≤ ∑ j, ‖J j‖ ^ 2 := by
  unfold krausGram
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  calc
    ‖ContinuousLinearMap.adjoint (J j) * J j‖ ≤
        ‖ContinuousLinearMap.adjoint (J j)‖ * ‖J j‖ := norm_mul_le _ _
    _ = ‖J j‖ ^ 2 := by
      rw [(ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := E) (F := E)).norm_map]
      ring

theorem generator_norm_bound (A : Operator (E := E)) (J : ι → Operator (E := E)) :
    ‖generator A J‖ ≤ 2 * ‖A‖ + (1 / 2 : ℝ) * ∑ j, ‖J j‖ ^ 2 := by
  calc
    ‖generator A J‖ ≤ ‖(-Complex.I) • hamiltonian A‖ +
        ‖(1 / 2 : ℂ) • krausGram J‖ := norm_sub_le _ _
    _ = ‖hamiltonian A‖ + (1 / 2 : ℝ) * ‖krausGram J‖ := by
      norm_num [norm_smul]
    _ ≤ 2 * ‖A‖ + (1 / 2 : ℝ) * ∑ j, ‖J j‖ ^ 2 :=
      add_le_add (hamiltonian_norm_bound A)
        (mul_le_mul_of_nonneg_left (krausGram_norm_bound J) (by norm_num))

/-- Only raw finite coefficient sources and their local analytic bounds enter.
The bound and subdivision condition are coefficient facts, not flow data. -/
structure RawKrausCell (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [Nontrivial E] (ι : Type v) [Fintype ι] where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  halfHamiltonian : ℝ → E →L[ℂ] E
  jumps : ℝ → ι → E →L[ℂ] E
  halfHamiltonian_continuous : ContinuousOn halfHamiltonian (Icc left right)
  jumps_continuous : ∀ j, ContinuousOn (fun t => jumps t j) (Icc left right)
  halfHamiltonian_bound : ℝ≥0
  jump_bounds : ι → ℝ≥0
  halfHamiltonian_norm : ∀ t ∈ Icc left right, ‖halfHamiltonian t‖ ≤ halfHamiltonian_bound
  jumps_norm : ∀ t ∈ Icc left right, ∀ j, ‖jumps t j‖ ≤ jump_bounds j
  short : 2 * (2 * (halfHamiltonian_bound : ℝ) +
    (1 / 2 : ℝ) * ∑ j, (jump_bounds j : ℝ) ^ 2) * (right - left) ≤ 1

namespace RawKrausCell

variable [Nontrivial E]
variable (source : RawKrausCell E ι)

def bound : ℝ≥0 := 2 * source.halfHamiltonian_bound + (1 / 2 : ℝ≥0) * ∑ j, source.jump_bounds j ^ 2

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

theorem coefficient_norm (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    ‖source.coefficient t‖ ≤ source.bound := by
  have jumps : (∑ j, ‖source.jumps t j‖ ^ 2) ≤ ∑ j, (source.jump_bounds j : ℝ) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    exact (sq_le_sq₀ (norm_nonneg _) (source.jump_bounds j).coe_nonneg).mpr (source.jumps_norm t ht j)
  calc
    ‖source.coefficient t‖ ≤ 2 * ‖source.halfHamiltonian t‖ +
        (1 / 2 : ℝ) * ∑ j, ‖source.jumps t j‖ ^ 2 := generator_norm_bound _ _
    _ ≤ 2 * (source.halfHamiltonian_bound : ℝ) +
        (1 / 2 : ℝ) * ∑ j, (source.jump_bounds j : ℝ) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left (source.halfHamiltonian_norm t ht) (by norm_num))
        (mul_le_mul_of_nonneg_left jumps (by norm_num))
    _ = (source.bound : ℝ) := by simp [bound]

def survivalSource : RetardedSourceSurvival284.LocalSurvivalSource (Operator (E := E)) where
  left := source.left
  right := source.right
  ordered := source.ordered
  generator := source.coefficient
  continuous := source.coefficient_continuous
  bound := source.bound
  norm_bound := source.coefficient_norm
  short := by simpa [bound] using source.short

private theorem applied_derivative (U : ℝ → Operator (E := E))
    (equation : ∀ t ∈ Icc source.left source.right,
      HasDerivWithinAt U (source.coefficient t * U t) (Icc source.left source.right) t)
    (x : E) (t : ℝ) (ht : t ∈ Icc source.left source.right) :
    HasDerivWithinAt (fun r => U r x) (source.coefficient t (U t x)) (Icc source.left source.right) t := by
  have written := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt t (equation t ht)
  change HasDerivWithinAt (fun r => U r x) ((source.coefficient t * U t) x)
    (Icc source.left source.right) t at written
  simpa only [mul_apply_eq_comp] using written

private theorem contracts_on_window (U : ℝ → Operator (E := E))
    (initial : U source.left = 1)
    (equation : ∀ t ∈ Icc source.left source.right,
      HasDerivWithinAt U (source.coefficient t * U t) (Icc source.left source.right) t)
    (x : E) (t : ℝ) (ht : t ∈ Icc source.left source.right) : ‖U t x‖ ≤ ‖x‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  have energy (s : ℝ) (hs : s ∈ Icc source.left source.right) :=
    (source.applied_derivative U equation x s hs).norm_sq
  have decreasing : AntitoneOn (fun s => ‖U s x‖ ^ 2) (Icc source.left source.right) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc source.left source.right)
      (fun s hs => (energy s hs).continuousWithinAt)
    · intro s hs
      exact (energy s (interior_subset hs)).mono interior_subset
    · intro s _
      apply mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      change (inner ℂ (U s x) (source.coefficient s (U s x))).re ≤ 0
      exact generator_dissipative _ _ _
  have paid := decreasing (left_mem_Icc.mpr source.ordered) ht ht.1
  have atStart : U source.left x = x := by
    simpa using congrArg (fun op : Operator (E := E) => op x) initial
  change ‖U t x‖ ^ 2 ≤ ‖U source.left x‖ ^ 2 at paid
  rw [atStart] at paid
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp paid

/-- The actual coefficient source produces its survival and contraction.
Neither U nor an operator-norm/contraction certificate enters this mouth. -/
theorem generate_contracting_survival :
    ∃ U : ℝ → Operator (E := E), U source.left = 1 ∧
      (∀ t ∈ Icc source.left source.right,
        HasDerivWithinAt U (source.coefficient t * U t) (Icc source.left source.right) t) ∧
      (∀ t ∈ Icc source.left source.right, ‖U t‖ ≤ 1) := by
  obtain ⟨U,initial,equation⟩ := source.survivalSource.generate_survival
  refine ⟨U,initial,equation,?_⟩
  intro t ht
  exact (U t).opNorm_le_bound (by norm_num) fun x => by
    simpa only [one_mul] using source.contracts_on_window U initial equation x t ht

/-- The same generated trajectory also pays the full jump energy identity. -/
theorem generate_survival_with_jump_energy :
    ∃ U : ℝ → Operator (E := E), U source.left = 1 ∧
      (∀ t ∈ Icc source.left source.right,
        HasDerivWithinAt U (source.coefficient t * U t) (Icc source.left source.right) t) ∧
      (∀ t ∈ Icc source.left source.right, ‖U t‖ ≤ 1) ∧
      ∀ (x : E) (t : ℝ), t ∈ Icc source.left source.right →
        HasDerivWithinAt (fun r => ‖U r x‖ ^ 2)
          (-(∑ j, ‖source.jumps t j (U t x)‖ ^ 2)) (Icc source.left source.right) t := by
  obtain ⟨U,initial,equation,contraction⟩ := source.generate_contracting_survival
  refine ⟨U,initial,equation,contraction,?_⟩
  intro x t ht
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  apply (source.applied_derivative U equation x t ht).norm_sq.congr_deriv
  change 2 * (inner ℂ (U t x) (source.coefficient t (U t x))).re = _
  exact generator_energy _ _ _

end RawKrausCell

end SourceKrausSurvival285
