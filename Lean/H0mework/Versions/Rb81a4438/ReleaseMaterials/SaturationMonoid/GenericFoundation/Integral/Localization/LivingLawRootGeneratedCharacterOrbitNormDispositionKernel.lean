import Mathlib.Analysis.SpecificLimits.Normed
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Integral.Localization.LivingLawRootGeneratedCharacterOrbitIntegralFaceKernel

/-!
# Character-orbit norm disposition

For a nonzero source vector, a two-sided complex character orbit has exactly
one of two outcomes.  The character has unit norm, or an actual sequence of
nonzero orbit points converges to zero: forward powers when the norm is below
one, inverse powers when it is above one.  This is an explicit non-discrete
compression residual, not a claim that the source carrier is imperfect.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedCharacterOrbitIntegralFace

open Filter

noncomputable section

universe h

variable {H : Type h} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A generated null sequence of nonzero points in the integral orbit. -/
structure OrbitCompressionResidual (scalar : ℂˣ) (vector : H) where
  exponent : ℕ → ℤ
  point_nonzero : ∀ stage,
    orbitPoint scalar vector (exponent stage) ≠ 0
  tends_to_zero : Tendsto
    (fun stage => orbitPoint scalar vector (exponent stage))
    atTop (nhds 0)

theorem OrbitCompressionResidual.point_mem
    {scalar : ℂˣ} {vector : H}
    (residual : OrbitCompressionResidual scalar vector) (stage : ℕ) :
    orbitPoint scalar vector (residual.exponent stage) ∈
      characterOrbit scalar vector :=
  orbitPoint_mem scalar vector _

inductive OrbitNormDisposition (scalar : ℂˣ) (vector : H) : Type h where
  | unitNorm (norm_eq_one : ‖(scalar : ℂ)‖ = 1)
  | compressionResidual (residual : OrbitCompressionResidual scalar vector)

def forwardCompressionResidual
    (scalar : ℂˣ) (vector : H) (vector_ne_zero : vector ≠ 0)
    (contracting : ‖(scalar : ℂ)‖ < 1) :
    OrbitCompressionResidual scalar vector where
  exponent stage := (stage : ℤ)
  point_nonzero stage := by
    simp [orbitPoint, vector_ne_zero, scalar.ne_zero]
  tends_to_zero := by
    simpa [orbitPoint] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one contracting).smul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => vector) atTop (nhds vector))

def inverseCompressionResidual
    (scalar : ℂˣ) (vector : H) (vector_ne_zero : vector ≠ 0)
    (expanding : 1 < ‖(scalar : ℂ)‖) :
    OrbitCompressionResidual scalar vector where
  exponent stage := -(stage : ℤ)
  point_nonzero stage := by
    simp [orbitPoint, vector_ne_zero, scalar.ne_zero]
  tends_to_zero := by
    have inverseContracting : ‖((scalar : ℂ)⁻¹)‖ < 1 := by
      rw [norm_inv]
      exact inv_lt_one_of_one_lt₀ expanding
    simpa [orbitPoint] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one inverseContracting).smul
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => vector) atTop (nhds vector))

/-- The norm-one or explicit compression-residual total disposition. -/
noncomputable def settleOrbitNorm
    (scalar : ℂˣ) (vector : H) (vector_ne_zero : vector ≠ 0) :
    OrbitNormDisposition scalar vector := by
  classical
  by_cases contracting : ‖(scalar : ℂ)‖ < 1
  · exact .compressionResidual
      (forwardCompressionResidual scalar vector vector_ne_zero contracting)
  · by_cases unitNorm : ‖(scalar : ℂ)‖ = 1
    · exact .unitNorm unitNorm
    · have expanding : 1 < ‖(scalar : ℂ)‖ :=
        lt_of_le_of_ne (le_of_not_gt contracting) (Ne.symm unitNorm)
      exact .compressionResidual
        (inverseCompressionResidual scalar vector vector_ne_zero expanding)

theorem orbitNormDisposition_total
    (scalar : ℂˣ) (vector : H) (vector_ne_zero : vector ≠ 0) :
    Nonempty (OrbitNormDisposition scalar vector) :=
  ⟨settleOrbitNorm scalar vector vector_ne_zero⟩

/-- Any downstream observation language that excludes the generated nonzero
null-sequence residual forces the character action to have unit norm. -/
theorem norm_eq_one_of_noCompressionResidual
    (scalar : ℂˣ) (vector : H) (vector_ne_zero : vector ≠ 0)
    (noResidual : ¬ Nonempty (OrbitCompressionResidual scalar vector)) :
    ‖(scalar : ℂ)‖ = 1 := by
  by_contra normNe
  by_cases contracting : ‖(scalar : ℂ)‖ < 1
  · exact noResidual
      ⟨forwardCompressionResidual scalar vector vector_ne_zero contracting⟩
  · have expanding : 1 < ‖(scalar : ℂ)‖ :=
      lt_of_le_of_ne (le_of_not_gt contracting) (Ne.symm normNe)
    exact noResidual
      ⟨inverseCompressionResidual scalar vector vector_ne_zero expanding⟩

end
end SourceGeneratedCharacterOrbitIntegralFace
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
