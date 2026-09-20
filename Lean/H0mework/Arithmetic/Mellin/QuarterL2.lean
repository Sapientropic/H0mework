import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import H0mework.Arithmetic.Mellin.QuarterTransform

/-!
# The canonical quarter-weight L² domain

The log-quarter transform selects the actual functions whose transformed
representatives lie in `L²(ℝ)`.  Tate reflection and normalized positive
dilation preserve this domain and become norm-preserving maps after passage
to Mathlib's `Lp ℂ 2 volume` carrier.  No continuity of the Mellin functional
on this Hilbert carrier is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann

open Complex MeasureTheory
open scoped ENNReal

noncomputable section

def positiveMellinQuarterL2Submodule :
    Submodule ℂ ClozelPositiveMellinFunction where
  carrier := { f | MemLp (positiveMellinLogQuarterTransform f)
    (2 : ℝ≥0∞) (volume : Measure ℝ) }
  zero_mem' := by
    change MemLp (positiveMellinLogQuarterTransform 0)
      (2 : ℝ≥0∞) (volume : Measure ℝ)
    rw [map_zero]
    exact MemLp.zero
  add_mem' {f g} hf hg := by
    change MemLp (positiveMellinLogQuarterTransform (f + g))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
    rw [map_add]
    exact hf.add hg
  smul_mem' c f hf := by
    change MemLp (positiveMellinLogQuarterTransform (c • f))
      (2 : ℝ≥0∞) (volume : Measure ℝ)
    rw [map_smul]
    exact hf.const_smul c

abbrev PositiveMellinQuarterL2 := positiveMellinQuarterL2Submodule

theorem positiveTateInvolution_mem_quarterL2
    (f : ClozelPositiveMellinFunction)
    (mem : f ∈ positiveMellinQuarterL2Submodule) :
    positiveTateInvolution f ∈ positiveMellinQuarterL2Submodule := by
  have reflected := mem.comp_measurePreserving
    (Measure.measurePreserving_neg (volume : Measure ℝ))
  change MemLp (fun x : ℝ =>
    positiveMellinLogQuarterTransform f (-x))
      (2 : ℝ≥0∞) (volume : Measure ℝ) at reflected
  apply (memLp_congr_ae (ae_of_all _ fun x =>
    positiveMellinLogQuarterTransform_tate f x)).mpr
  exact reflected

theorem positiveQuarterNormalizedDilation_mem_quarterL2
    (a : ℝ) (positive : 0 < a)
    (f : ClozelPositiveMellinFunction)
    (mem : f ∈ positiveMellinQuarterL2Submodule) :
    positiveMellinQuarterNormalizedDilation a positive f ∈
      positiveMellinQuarterL2Submodule := by
  have translated := mem.comp_measurePreserving
    (measurePreserving_add_left (volume : Measure ℝ) (Real.log a))
  change MemLp (fun x : ℝ =>
    positiveMellinLogQuarterTransform f (Real.log a + x))
      (2 : ℝ≥0∞) (volume : Measure ℝ) at translated
  have almostEverywhere :
      positiveMellinLogQuarterTransform
          (positiveMellinQuarterNormalizedDilation a positive f) =ᵐ[volume]
        (fun x : ℝ => positiveMellinLogQuarterTransform f
          (Real.log a + x)) :=
    ae_of_all _ fun x => by
      rw [positiveMellinLogQuarterTransform_normalizedDilation]
      ring
  exact (memLp_congr_ae almostEverywhere).mpr translated

def positiveMellinQuarterL2Tate :
    PositiveMellinQuarterL2 →ₗ[ℂ] PositiveMellinQuarterL2 where
  toFun f :=
    ⟨positiveTateInvolution f.1,
      positiveTateInvolution_mem_quarterL2 f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact positiveTateInvolution.map_add f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact positiveTateInvolution.map_smul c f.1

theorem positiveMellinQuarterL2Tate_involutive
    (f : PositiveMellinQuarterL2) :
    positiveMellinQuarterL2Tate (positiveMellinQuarterL2Tate f) = f := by
  apply Subtype.ext
  exact positiveTateInvolution_involutive f.1

def positiveMellinQuarterL2NormalizedDilation
    (a : ℝ) (positive : 0 < a) :
    PositiveMellinQuarterL2 →ₗ[ℂ] PositiveMellinQuarterL2 where
  toFun f :=
    ⟨positiveMellinQuarterNormalizedDilation a positive f.1,
      positiveQuarterNormalizedDilation_mem_quarterL2
        a positive f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact (positiveMellinQuarterNormalizedDilation a positive).map_add
      f.1 g.1
  map_smul' c f := by
    apply Subtype.ext
    exact (positiveMellinQuarterNormalizedDilation a positive).map_smul
      c f.1

theorem positiveMellinQuarterL2_memLp
    (f : PositiveMellinQuarterL2) :
    MemLp (positiveMellinLogQuarterTransform f.1)
      (2 : ℝ≥0∞) (volume : Measure ℝ) :=
  f.2

def positiveMellinQuarterLpValue
    (f : PositiveMellinQuarterL2) :
    Lp ℂ (2 : ℝ≥0∞) (volume : Measure ℝ) :=
  (positiveMellinQuarterL2_memLp f).toLp
    (positiveMellinLogQuarterTransform f.1)

theorem positiveMellinQuarterLpValue_tate
    (f : PositiveMellinQuarterL2) :
    positiveMellinQuarterLpValue (positiveMellinQuarterL2Tate f) =
      Lp.compMeasurePreserving (fun x : ℝ => -x)
        (Measure.measurePreserving_neg (volume : Measure ℝ))
        (positiveMellinQuarterLpValue f) := by
  rw [positiveMellinQuarterLpValue, positiveMellinQuarterLpValue,
    Lp.toLp_compMeasurePreserving
      (positiveMellinQuarterL2_memLp f)
      (Measure.measurePreserving_neg (volume : Measure ℝ))]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => positiveMellinLogQuarterTransform_tate f.1 x

theorem positiveMellinQuarterLpValue_normalizedDilation
    (a : ℝ) (positive : 0 < a)
    (f : PositiveMellinQuarterL2) :
    positiveMellinQuarterLpValue
        (positiveMellinQuarterL2NormalizedDilation a positive f) =
      Lp.compMeasurePreserving (fun x : ℝ => Real.log a + x)
        (measurePreserving_add_left (volume : Measure ℝ) (Real.log a))
        (positiveMellinQuarterLpValue f) := by
  rw [positiveMellinQuarterLpValue, positiveMellinQuarterLpValue,
    Lp.toLp_compMeasurePreserving
      (positiveMellinQuarterL2_memLp f)
      (measurePreserving_add_left
        (volume : Measure ℝ) (Real.log a))]
  apply MemLp.toLp_congr
  exact ae_of_all _ fun x => by
    change positiveMellinLogQuarterTransform
        (positiveMellinQuarterNormalizedDilation a positive f.1) x =
      positiveMellinLogQuarterTransform f.1 (Real.log a + x)
    rw [positiveMellinLogQuarterTransform_normalizedDilation]
    ring

theorem positiveMellinQuarterLpValue_tate_norm
    (f : PositiveMellinQuarterL2) :
    ‖positiveMellinQuarterLpValue (positiveMellinQuarterL2Tate f)‖ =
      ‖positiveMellinQuarterLpValue f‖ := by
  rw [positiveMellinQuarterLpValue_tate,
    Lp.norm_compMeasurePreserving]

theorem positiveMellinQuarterLpValue_normalizedDilation_norm
    (a : ℝ) (positive : 0 < a)
    (f : PositiveMellinQuarterL2) :
    ‖positiveMellinQuarterLpValue
        (positiveMellinQuarterL2NormalizedDilation a positive f)‖ =
      ‖positiveMellinQuarterLpValue f‖ := by
  rw [positiveMellinQuarterLpValue_normalizedDilation,
    Lp.norm_compMeasurePreserving]

end

end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
