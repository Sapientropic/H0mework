import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Burnol constant-gap Hilbert face

This is the source-independent physical carrier underlying an augmented
Sonine realization.  A vector belongs to the local face when its restriction
to a finite symmetric interval lies in the one-dimensional constant line.
The Burnol face imposes the same condition after the actual `L²` Fourier
transform.  Both conditions are closed; no zero, evaluator, eigenvalue, or
critical-line premise enters the construction.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open FourierTransform MeasureTheory Set
open scoped ENNReal

noncomputable section

abbrev BurnolL2 : Type := Lp ℂ 2 (volume : Measure ℝ)

def symmetricInterval (radius : ℝ) : Set ℝ := Icc (-radius) radius

@[measurability]
theorem measurableSet_symmetricInterval (radius : ℝ) :
    MeasurableSet (symmetricInterval radius) :=
  measurableSet_Icc

def restrictToInterval (radius : ℝ) :
    BurnolL2 →L[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius)) :=
  LpToLpRestrictCLM ℝ ℂ ℂ volume 2 (symmetricInterval radius)

theorem restrictedInterval_univ_ne_top (radius : ℝ) :
    ((volume : Measure ℝ).restrict (symmetricInterval radius)) Set.univ ≠ ∞ := by
  rw [Measure.restrict_apply_univ]
  exact measure_Icc_lt_top.ne

def intervalConstant (radius : ℝ) :
    Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius)) :=
  indicatorConstLp 2 MeasurableSet.univ
    (restrictedInterval_univ_ne_top radius) 1

def intervalConstantLine (radius : ℝ) :
    Submodule ℂ
      (Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius))) :=
  ℂ ∙ intervalConstant radius

/-- Functions whose restriction to the symmetric interval is almost
everywhere constant. -/
def locallyConstantFace (radius : ℝ) : Submodule ℂ BurnolL2 :=
  (intervalConstantLine radius).comap (restrictToInterval radius).toLinearMap

theorem mem_locallyConstantFace_iff_exists {radius : ℝ} {value : BurnolL2} :
    value ∈ locallyConstantFace radius ↔
      ∃ coefficient : ℂ,
        coefficient • intervalConstant radius = restrictToInterval radius value := by
  change restrictToInterval radius value ∈ intervalConstantLine radius ↔ _
  exact Submodule.mem_span_singleton

theorem intervalConstantLine_isClosed (radius : ℝ) :
    IsClosed (intervalConstantLine radius : Set
      (Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius)))) := by
  let _ : FiniteDimensional ℂ (intervalConstantLine radius) :=
    FiniteDimensional.span_of_finite ℂ
      (Set.finite_singleton (intervalConstant radius))
  exact (intervalConstantLine radius).closed_of_finiteDimensional

theorem locallyConstantFace_isClosed (radius : ℝ) :
    IsClosed (locallyConstantFace radius : Set BurnolL2) :=
  (intervalConstantLine_isClosed radius).preimage
    (restrictToInterval radius).continuous

def fourierL2 : BurnolL2 ≃ₗᵢ[ℂ] BurnolL2 := Lp.fourierTransformₗᵢ ℝ ℂ

/-- The local constant condition simultaneously in position and Fourier
coordinates. -/
def burnolFace (radius : ℝ) : Submodule ℂ BurnolL2 :=
  locallyConstantFace radius ⊓
    (locallyConstantFace radius).comap fourierL2.toLinearMap

theorem mem_burnolFace_iff {radius : ℝ} {value : BurnolL2} :
    value ∈ burnolFace radius ↔
      value ∈ locallyConstantFace radius ∧
        fourierL2 value ∈ locallyConstantFace radius :=
  Iff.rfl

theorem burnolFace_isClosed (radius : ℝ) :
    IsClosed (burnolFace radius : Set BurnolL2) :=
  (locallyConstantFace_isClosed radius).inter
    ((locallyConstantFace_isClosed radius).preimage fourierL2.continuous)

def burnolClosedFace (radius : ℝ) : ClosedSubmodule ℂ BurnolL2 where
  toSubmodule := burnolFace radius
  isClosed' := burnolFace_isClosed radius

theorem negMeasurePreserving :
    MeasurePreserving (fun x : ℝ ↦ -x) (volume : Measure ℝ) volume :=
  Measure.measurePreserving_neg volume

def reflectL2 : BurnolL2 →ₗᵢ[ℂ] BurnolL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x) negMeasurePreserving

theorem reflectL2_reflectL2 (value : BurnolL2) :
    reflectL2 (reflectL2 value) = value := by
  apply Lp.ext
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (reflectL2 value) negMeasurePreserving,
    negMeasurePreserving.quasiMeasurePreserving.ae
      (Lp.coeFn_compMeasurePreserving value negMeasurePreserving)]
    with x first second
  simpa [reflectL2] using first.trans second

theorem neg_preimage_symmetricInterval (radius : ℝ) :
    (fun x : ℝ ↦ -x) ⁻¹' symmetricInterval radius =
      symmetricInterval radius := by
  ext x
  simp only [symmetricInterval, mem_preimage, mem_Icc]
  constructor <;> rintro ⟨left, right⟩ <;> constructor <;> linarith

theorem negMeasurePreserving_restrict (radius : ℝ) :
    MeasurePreserving (fun x : ℝ ↦ -x)
      ((volume : Measure ℝ).restrict (symmetricInterval radius))
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) := by
  simpa only [neg_preimage_symmetricInterval] using
    negMeasurePreserving.restrict_preimage (measurableSet_symmetricInterval radius)

def reflectRestricted (radius : ℝ) :
    Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius)) →ₗᵢ[ℂ]
      Lp ℂ 2 ((volume : Measure ℝ).restrict (symmetricInterval radius)) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℝ ↦ -x)
    (negMeasurePreserving_restrict radius)

theorem intervalConstant_coeFn (radius : ℝ) :
    intervalConstant radius =ᵐ[
      (volume : Measure ℝ).restrict (symmetricInterval radius)]
      (fun _ : ℝ ↦ (1 : ℂ)) := by
  simpa only [intervalConstant, Set.indicator_univ] using
    (@indicatorConstLp_coeFn ℝ ℂ _ 2
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) _ Set.univ
      MeasurableSet.univ (restrictedInterval_univ_ne_top radius) (1 : ℂ))

theorem intervalConstant_ne_zero {radius : ℝ} (positive : 0 < radius) :
    intervalConstant radius ≠ 0 := by
  intro zero
  have equality :
      indicatorConstLp 2 MeasurableSet.univ
          (restrictedInterval_univ_ne_top radius) (1 : ℂ) =
        indicatorConstLp 2 MeasurableSet.empty (by simp) (1 : ℂ) := by
    rw [indicatorConstLp_empty]
    exact zero
  have setsEqual : (Set.univ : Set ℝ) =ᵐ[
      (volume : Measure ℝ).restrict (symmetricInterval radius)]
      (∅ : Set ℝ) :=
    (indicatorConstLp_inj MeasurableSet.univ
      (restrictedInterval_univ_ne_top radius) MeasurableSet.empty
      (by simp) (by norm_num : (1 : ℂ) ≠ 0)).mp equality
  have measureZero :
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) Set.univ = 0 := by
    calc
      _ = ((volume : Measure ℝ).restrict
          (symmetricInterval radius)) (∅ : Set ℝ) := measure_congr setsEqual
      _ = 0 := measure_empty
  have measureNe :
      ((volume : Measure ℝ).restrict (symmetricInterval radius)) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, symmetricInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  exact measureNe measureZero

theorem intervalConstantLine_finrank {radius : ℝ} (positive : 0 < radius) :
    Module.finrank ℂ (intervalConstantLine radius) = 1 :=
  finrank_span_singleton (intervalConstant_ne_zero positive)

theorem restrictToInterval_reflectL2 (radius : ℝ) (value : BurnolL2) :
    restrictToInterval radius (reflectL2 value) =
      reflectRestricted radius (restrictToInterval radius value) := by
  apply Lp.ext
  have restrictedNeg :=
    (negMeasurePreserving_restrict radius).quasiMeasurePreserving.ae
      (LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value)
  filter_upwards [
    LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) (reflectL2 value),
    ae_restrict_of_ae (Lp.coeFn_compMeasurePreserving value negMeasurePreserving),
    Lp.coeFn_compMeasurePreserving (restrictToInterval radius value)
      (negMeasurePreserving_restrict radius), restrictedNeg]
    with x left reflection right restriction
  calc
    restrictToInterval radius (reflectL2 value) x = reflectL2 value x := left
    _ = value (-x) := reflection
    _ = restrictToInterval radius value (-x) := restriction.symm
    _ = reflectRestricted radius (restrictToInterval radius value) x := right.symm

theorem reflectRestricted_intervalConstant (radius : ℝ) :
    reflectRestricted radius (intervalConstant radius) =
      intervalConstant radius := by
  apply Lp.ext
  have constantNeg :=
    (negMeasurePreserving_restrict radius).quasiMeasurePreserving.ae
      (intervalConstant_coeFn radius)
  filter_upwards [
    Lp.coeFn_compMeasurePreserving (intervalConstant radius)
      (negMeasurePreserving_restrict radius),
    constantNeg, intervalConstant_coeFn radius]
    with x reflection negConstant constant
  calc
    reflectRestricted radius (intervalConstant radius) x =
        intervalConstant radius (-x) := reflection
    _ = 1 := negConstant
    _ = intervalConstant radius x := constant.symm

theorem locallyConstantFace_reflectL2 {radius : ℝ} {value : BurnolL2}
    (membership : value ∈ locallyConstantFace radius) :
    reflectL2 value ∈ locallyConstantFace radius := by
  change restrictToInterval radius value ∈ intervalConstantLine radius at membership
  change restrictToInterval radius (reflectL2 value) ∈ intervalConstantLine radius
  rw [restrictToInterval_reflectL2]
  obtain ⟨coefficient, equality⟩ := Submodule.mem_span_singleton.mp membership
  rw [← equality, (reflectRestricted radius).map_smul,
    reflectRestricted_intervalConstant]
  exact Submodule.smul_mem _ coefficient
    (Submodule.mem_span_singleton_self (R := ℂ) (intervalConstant radius))

end

end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.intervalConstantLine_finrank
#print axioms SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.burnolFace_isClosed
