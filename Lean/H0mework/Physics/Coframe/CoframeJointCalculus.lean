import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# S9-C3e2b: joint calculus for the coframe variation corridor

This module isolates the reusable calculus which turns joint `C¹` regularity
of a family `F : X → Y → Z` into continuity of its derivative in the `Y`
slot, both along a background section and along an affine parameter corridor.
It also pulls a locally admitted family back to an open corridor for the
background-subtracted integrand used in differentiation under the integral.

The final negative regression proves that smoothness of every individual
`Y`-fiber does not imply continuity of the partial derivative in `X`.
Consequently the physics-specific finite-coordinate module must produce true
joint regularity; it cannot reuse C3e1 fiberwise smoothness as a certificate.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeJointCalculus

open Filter
open scoped ContDiff

noncomputable section

set_option maxHeartbeats 600000

section AbstractJointCalculus

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A joint `C¹` family has a continuously varying derivative in its second
slot after restriction to a `C¹` section. -/
theorem partialFDeriv_continuousAt_of_jointC1
    (family : X → Y → Z) (selectedSection : X → Y) (point : X)
    (familyJointC1 : ContDiffAt ℝ 1 (Function.uncurry family)
      (point, selectedSection point))
    (sectionC1 : ContDiffAt ℝ 0 selectedSection point) :
    ContinuousAt
      (fun candidate : X =>
        fderiv ℝ (family candidate) (selectedSection candidate)) point := by
  exact (ContDiffAt.fderiv (m := 0) familyJointC1 sectionC1
    (by simp)).continuousAt

/-- Evaluating the continuously varying partial derivative on a continuous
direction preserves continuity. -/
theorem partialFDeriv_apply_continuousAt_of_jointC1
    (family : X → Y → Z) (selectedSection direction : X → Y) (point : X)
    (familyJointC1 : ContDiffAt ℝ 1 (Function.uncurry family)
      (point, selectedSection point))
    (sectionC1 : ContDiffAt ℝ 0 selectedSection point)
    (directionContinuous : ContinuousAt direction point) :
    ContinuousAt
      (fun candidate : X =>
        fderiv ℝ (family candidate) (selectedSection candidate)
          (direction candidate)) point := by
  exact (partialFDeriv_continuousAt_of_jointC1 family selectedSection point
    familyJointC1 sectionC1).clm_apply directionContinuous

/-- The coframe-like affine corridor as a section over parameter-point
pairs. -/
def affineCorridorSection
    (background variation : X → Y) (pair : ℝ × X) : Y :=
  background pair.2 + pair.1 • variation pair.2

/-- Pull a joint family back to the affine parameter corridor. -/
def affineCorridorDensity
    (family : X → Y → Z) (background variation : X → Y)
    (parameter : ℝ) (point : X) : Z :=
  family point (background point + parameter • variation point)

/-- Background subtraction is the compact-support preserving integrand used
for differentiation under the integral. -/
def affineCorridorDensityIncrement
    (family : X → Y → Z) (background variation : X → Y)
    (parameter : ℝ) (point : X) : Z :=
  affineCorridorDensity family background variation parameter point -
    affineCorridorDensity family background variation 0 point

theorem affineCorridorSection_contDiffAt
    (background variation : X → Y) (parameter : ℝ) (point : X)
    (backgroundC1 : ContDiffAt ℝ 1 background point)
    (variationC1 : ContDiffAt ℝ 1 variation point) :
    ContDiffAt ℝ 1 (affineCorridorSection background variation)
      (parameter, point) := by
  exact (backgroundC1.comp (parameter, point) contDiffAt_snd).add
    (contDiffAt_fst.smul
      (variationC1.comp (parameter, point) contDiffAt_snd))

/-- A pointwise producer for joint `C¹` on every nondegenerate family input
pulls back to joint `C¹` on the entire admitted parameter corridor. -/
theorem affineCorridorDensity_contDiffOn
    (family : X → Y → Z) (background variation : X → Y)
    (parameterSet : Set ℝ)
    (familyJointC1 : ∀ parameter ∈ parameterSet, ∀ point,
      ContDiffAt ℝ 1 (Function.uncurry family)
        (point, background point + parameter • variation point))
    (backgroundC1 : ContDiff ℝ 1 background)
    (variationC1 : ContDiff ℝ 1 variation) :
    ContDiffOn ℝ 1
      (Function.uncurry
        (affineCorridorDensity family background variation))
      (parameterSet ×ˢ (Set.univ : Set X)) := by
  rintro ⟨parameter, point⟩ ⟨parameterMem, _⟩
  have corridorC1 := affineCorridorSection_contDiffAt background variation
    parameter point backgroundC1.contDiffAt variationC1.contDiffAt
  have inputC1 : ContDiffAt ℝ 1
      (fun pair : ℝ × X =>
        (pair.2, affineCorridorSection background variation pair))
      (parameter, point) := contDiffAt_snd.prodMk corridorC1
  have pulledBack :=
    (familyJointC1 parameter parameterMem point).comp (parameter, point) inputC1
  have pullbackFunctionEq :
      (Function.uncurry family ∘ fun pair : ℝ × X =>
        (pair.2, affineCorridorSection background variation pair)) =
      fun pair : ℝ × X =>
        family pair.2
          (background pair.2 + pair.1 • variation pair.2) := by
    funext pair
    rfl
  rw [pullbackFunctionEq] at pulledBack
  change ContDiffWithinAt ℝ 1
    (fun pair : ℝ × X =>
      family pair.2
        (background pair.2 + pair.1 • variation pair.2))
    (parameterSet ×ˢ (Set.univ : Set X)) (parameter, point)
  exact pulledBack.contDiffWithinAt

/-- The same pullback theorem directly produces joint `C¹` for the
background-subtracted family; no regularity or derivative of the increment is
accepted independently. -/
theorem affineCorridorDensityIncrement_contDiffOn
    (family : X → Y → Z) (background variation : X → Y)
    (parameterSet : Set ℝ) (zeroMem : 0 ∈ parameterSet)
    (familyJointC1 : ∀ parameter ∈ parameterSet, ∀ point,
      ContDiffAt ℝ 1 (Function.uncurry family)
        (point, background point + parameter • variation point))
    (backgroundC1 : ContDiff ℝ 1 background)
    (variationC1 : ContDiff ℝ 1 variation) :
    ContDiffOn ℝ 1
      (Function.uncurry
        (affineCorridorDensityIncrement family background variation))
      (parameterSet ×ˢ (Set.univ : Set X)) := by
  have variedC1 := affineCorridorDensity_contDiffOn family background variation
    parameterSet familyJointC1 backgroundC1 variationC1
  intro pair pairMem
  have backgroundInputC1 : ContDiffAt ℝ 1
      (fun candidate : ℝ × X =>
        (candidate.2, background candidate.2)) pair :=
    contDiffAt_snd.prodMk
      (backgroundC1.contDiffAt.comp pair contDiffAt_snd)
  have backgroundC1AtPair : ContDiffAt ℝ 1
      (fun candidate : ℝ × X => family candidate.2 (background candidate.2))
      pair := by
    have familyAtBackground : ContDiffAt ℝ 1 (Function.uncurry family)
        (pair.2, background pair.2) := by
      simpa using familyJointC1 0 zeroMem pair.2
    have pulledBack := familyAtBackground.comp pair backgroundInputC1
    have pullbackFunctionEq :
        (Function.uncurry family ∘ fun candidate : ℝ × X =>
          (candidate.2, background candidate.2)) =
        fun candidate : ℝ × X =>
          family candidate.2 (background candidate.2) := by
      funext candidate
      rfl
    rw [pullbackFunctionEq] at pulledBack
    exact pulledBack
  exact (variedC1 pair pairMem).sub (by
    simpa [affineCorridorDensity] using backgroundC1AtPair.contDiffWithinAt)

/-- An eventually admitted corridor and an actual local joint-regularity
producer generate the open `C¹` corridor used by differentiation under the
integral. The only predicate passed here is the structural domain condition
(for coframes, nonzero determinant), not a regularity certificate. -/
theorem exists_open_affineCorridorDensityIncrement_contDiffOn
    (family : X → Y → Z) (background variation : X → Y)
    (admissible : Y → Prop)
    (eventuallyAdmitted : ∀ᶠ parameter in nhds (0 : ℝ), ∀ point,
      admissible (background point + parameter • variation point))
    (familyJointC1 : ∀ point candidate, admissible candidate →
      ContDiffAt ℝ 1 (Function.uncurry family) (point, candidate))
    (backgroundC1 : ContDiff ℝ 1 background)
    (variationC1 : ContDiff ℝ 1 variation) :
    ∃ parameterSet : Set ℝ,
      IsOpen parameterSet ∧
        0 ∈ parameterSet ∧
        ContDiffOn ℝ 1
          (Function.uncurry
            (affineCorridorDensityIncrement family background variation))
          (parameterSet ×ˢ (Set.univ : Set X)) := by
  obtain ⟨parameterSet, parameterSubset, parameterOpen, zeroMem⟩ :=
    mem_nhds_iff.mp eventuallyAdmitted
  refine ⟨parameterSet, parameterOpen, zeroMem, ?_⟩
  apply affineCorridorDensityIncrement_contDiffOn family background variation
    parameterSet zeroMem
  · intro parameter parameterMem point
    exact familyJointC1 point
      (background point + parameter • variation point)
      (parameterSubset parameterMem point)
  · exact backgroundC1
  · exact variationC1

/-- Reindex a joint family by parameter-point pairs while retaining the
coframe-like variable as its differentiable second slot. -/
def parameterReindexedFamily
    (family : X → Y → Z) (pair : ℝ × X) (value : Y) : Z :=
  family pair.2 value

theorem parameterReindexedFamily_contDiffAt
    (family : X → Y → Z) (selectedSection : ℝ × X → Y)
    (parameter : ℝ) (point : X)
    (familyJointC1 : ContDiffAt ℝ 1 (Function.uncurry family)
      (point, selectedSection (parameter, point))) :
    ContDiffAt ℝ 1
      (Function.uncurry (parameterReindexedFamily family))
      ((parameter, point), selectedSection (parameter, point)) := by
  have firstProjectionC1 : ContDiffAt ℝ 1
      (fun pair : (ℝ × X) × Y => pair.1.2)
      ((parameter, point), selectedSection (parameter, point)) :=
    contDiffAt_snd.comp
      ((parameter, point), selectedSection (parameter, point)) contDiffAt_fst
  have inputC1 : ContDiffAt ℝ 1
      (fun pair : (ℝ × X) × Y => (pair.1.2, pair.2))
      ((parameter, point), selectedSection (parameter, point)) :=
    firstProjectionC1.prodMk contDiffAt_snd
  have pulledBack := familyJointC1.comp
    ((parameter, point), selectedSection (parameter, point)) inputC1
  have pullbackFunctionEq :
      (Function.uncurry family ∘ fun pair : (ℝ × X) × Y =>
        (pair.1.2, pair.2)) =
      Function.uncurry (parameterReindexedFamily family) := by
    funext pair
    rfl
  rw [pullbackFunctionEq] at pulledBack
  exact pulledBack

/-- At every corridor point covered by joint `C¹`, the displayed partial
derivative is the genuine parameter derivative, not merely a continuous
candidate. -/
theorem affineCorridor_hasFDerivAt_of_jointC1
    (family : X → Y → Z) (background variation : X → Y)
    (parameter : ℝ) (point : X)
    (familyJointC1 : ContDiffAt ℝ 1 (Function.uncurry family)
      (point, affineCorridorSection background variation (parameter, point))) :
    HasFDerivAt
      (fun candidate : ℝ =>
        family point (background point + candidate • variation point))
      ((fderiv ℝ (family point)
          (background point + parameter • variation point)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ (variation point)))
      parameter := by
  have fiberC1 : ContDiffAt ℝ 1 (family point)
      (background point + parameter • variation point) := by
    have pulledBack := familyJointC1.comp
      (background point + parameter • variation point)
      (contDiffAt_const.prodMk contDiffAt_id)
    have pullbackFunctionEq :
        (Function.uncurry family ∘ Prod.mk point) = family point := by
      funext candidate
      rfl
    rw [pullbackFunctionEq] at pulledBack
    exact pulledBack
  have outerDerivative : HasFDerivAt (family point)
      (fderiv ℝ (family point)
        (background point + parameter • variation point))
      (background point + parameter • variation point) :=
    (fiberC1.differentiableAt (by simp)).hasFDerivAt
  have pathDerivative : HasFDerivAt
      (fun candidate : ℝ =>
        background point + candidate • variation point)
      (ContinuousLinearMap.toSpanSingleton ℝ (variation point)) parameter := by
    exact (hasFDerivAt_const_add_iff
      (f := fun candidate : ℝ =>
        (ContinuousLinearMap.toSpanSingleton ℝ (variation point)) candidate)
      (background point)).2
        (ContinuousLinearMap.toSpanSingleton ℝ
          (variation point)).hasFDerivAt
  exact outerDerivative.comp parameter pathDerivative

/-- Joint `C¹` of the original family produces continuity of the actual
parameter-axis partial derivative on the affine corridor. This is the exact
abstract bridge needed by compact-uniform domination. -/
theorem affineCorridorParameterFDeriv_continuousAt_of_jointC1
    (family : X → Y → Z) (background variation : X → Y)
    (parameter : ℝ) (point : X)
    (familyJointC1 : ContDiffAt ℝ 1 (Function.uncurry family)
      (point, affineCorridorSection background variation (parameter, point)))
    (backgroundC1 : ContDiffAt ℝ 1 background point)
    (variationC1 : ContDiffAt ℝ 1 variation point) :
    ContinuousAt
      (fun pair : ℝ × X =>
        (fderiv ℝ (family pair.2)
          (affineCorridorSection background variation pair)).comp
            (ContinuousLinearMap.toSpanSingleton ℝ (variation pair.2)))
      (parameter, point) := by
  have reindexedC1 := parameterReindexedFamily_contDiffAt family
    (affineCorridorSection background variation) parameter point familyJointC1
  have corridorC1 := affineCorridorSection_contDiffAt background variation
    parameter point backgroundC1 variationC1
  have partialDerivativeContinuous : ContinuousAt
      (fun pair : ℝ × X =>
        fderiv ℝ (parameterReindexedFamily family pair)
          (affineCorridorSection background variation pair))
      (parameter, point) :=
    (ContDiffAt.fderiv (m := 0) reindexedC1
      (corridorC1.of_le (by simp)) (by simp)).continuousAt
  have directionContinuous : ContinuousAt
      (fun pair : ℝ × X =>
        ContinuousLinearMap.toSpanSingleton ℝ (variation pair.2))
      (parameter, point) := by
    exact (ContinuousLinearMap.toSpanSingletonCLE
      (𝕜 := ℝ) (E := Y)).continuous.continuousAt.comp
        (variationC1.continuousAt.comp continuousAt_snd)
  exact partialDerivativeContinuous.clm_comp directionContinuous

end AbstractJointCalculus

/-! ## Negative regression: fiberwise smoothness is not joint regularity -/

/-- Every second-slot fiber is linear or constant, while the coefficient
jumps in the first variable. -/
def fiberwiseSmoothDiscontinuousFamily (point value : ℝ) : ℝ :=
  if point = 0 then value else 0

theorem fiberwiseSmoothDiscontinuousFamily_contDiff_fiber (point : ℝ) :
    ContDiff ℝ ∞ (fiberwiseSmoothDiscontinuousFamily point) := by
  by_cases pointZero : point = 0
  · unfold fiberwiseSmoothDiscontinuousFamily
    simp only [if_pos pointZero]
    fun_prop
  · unfold fiberwiseSmoothDiscontinuousFamily
    simpa only [if_neg pointZero] using
      (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (0 : ℝ)))

@[simp] theorem fiberwiseSmoothDiscontinuousFamily_partial_apply_one
    (point : ℝ) :
    fderiv ℝ (fiberwiseSmoothDiscontinuousFamily point) 0 1 =
      if point = 0 then 1 else 0 := by
  by_cases pointZero : point = 0
  · have familyEq : fiberwiseSmoothDiscontinuousFamily point = id := by
      funext value
      simp [fiberwiseSmoothDiscontinuousFamily, pointZero]
    rw [if_pos pointZero, familyEq, fderiv_id]
    simp
  · have familyEq : fiberwiseSmoothDiscontinuousFamily point =
        fun _ : ℝ => 0 := by
      funext value
      simp [fiberwiseSmoothDiscontinuousFamily, pointZero]
    rw [if_neg pointZero, familyEq, fderiv_const_apply]
    simp

/-- Thus no abstract theorem can promote the existing C3e1 statement
`∀ point, ContDiffAt ... (family point)` to continuity of the coframe partial
derivative. Smooth dependence of the actual finite coefficients on the base
point must be proved. -/
theorem fiberwiseSmooth_does_not_force_partialFDeriv_continuous :
    ¬ ContinuousAt
      (fun point : ℝ =>
        fderiv ℝ (fiberwiseSmoothDiscontinuousFamily point) 0) 0 := by
  intro partialContinuous
  have evaluatedContinuous : ContinuousAt
      (fun point : ℝ =>
        fderiv ℝ (fiberwiseSmoothDiscontinuousFamily point) 0 1) 0 :=
    partialContinuous.clm_apply continuousAt_const
  have sequenceToZero : Tendsto
      (fun index : ℕ => (1 : ℝ) / ((index : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have impossibleLimit : Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 1) := by
    have mappedLimit := evaluatedContinuous.tendsto.comp sequenceToZero
    have mappedFunctionEq :
        ((fun point : ℝ =>
          fderiv ℝ (fiberwiseSmoothDiscontinuousFamily point) 0 1) ∘
          fun index : ℕ => (1 : ℝ) / ((index : ℝ) + 1)) =
        fun index : ℕ =>
          fderiv ℝ
            (fiberwiseSmoothDiscontinuousFamily
              ((1 : ℝ) / ((index : ℝ) + 1))) 0 1 := by
      funext index
      rfl
    rw [mappedFunctionEq] at mappedLimit
    have sequenceDerivativeZero :
        (fun index : ℕ =>
          fderiv ℝ
            (fiberwiseSmoothDiscontinuousFamily
              ((1 : ℝ) / ((index : ℝ) + 1))) 0 1) =
        fun _ : ℕ => (0 : ℝ) := by
      funext index
      rw [fiberwiseSmoothDiscontinuousFamily_partial_apply_one]
      have denominatorNonzero : (index : ℝ) + 1 ≠ 0 := by positivity
      have sequenceNonzero : (1 : ℝ) / ((index : ℝ) + 1) ≠ 0 :=
        div_ne_zero one_ne_zero denominatorNonzero
      exact if_neg sequenceNonzero
    have originDerivativeOne :
        fderiv ℝ (fiberwiseSmoothDiscontinuousFamily 0) 0 1 = 1 := by
      simpa using
        fiberwiseSmoothDiscontinuousFamily_partial_apply_one 0
    rw [sequenceDerivativeZero, originDerivativeOne] at mappedLimit
    exact mappedLimit
  have zeroLimit : Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_nhds
  have : (1 : ℝ) = 0 := tendsto_nhds_unique impossibleLimit zeroLimit
  norm_num at this

end

end SaturationMonoid.PhysicsCore.StageNineCoframeJointCalculus
