import Mathlib.Analysis.Fourier.LpSpace

/-!
# Balanced Sonine source gap

The radius-indexed source and Fourier gaps are actual closed kernels in
Schwartz space.  At radius one Fourier and inverse Fourier preserve the same
face and generate its canonical involutive source action.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual

open Complex FourierTransform MeasureTheory
open scoped SchwartzMap RealInnerProductSpace

noncomputable section

abbrev SonineSchwartz := SchwartzMap ℝ ℂ

/-- Point evaluation, factored through the existing continuous inclusion of
Schwartz space into continuous functions vanishing at infinity. -/
def soninePointEval (x : ℝ) : SonineSchwartz →L[ℂ] ℂ :=
  (BoundedContinuousFunction.evalCLM ℂ x).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)

@[simp] theorem soninePointEval_apply (x : ℝ) (test : SonineSchwartz) :
    soninePointEval x test = test x :=
  rfl

/-- Closed kernel of one actual source evaluation. -/
def soninePointKernel (x : ℝ) : ClosedSubmodule ℂ SonineSchwartz where
  toSubmodule := (soninePointEval x : SonineSchwartz →ₗ[ℂ] ℂ).ker
  isClosed' := by simpa using (soninePointEval x).isClosed_ker

/-- Closed source face whose functions vanish throughout the open symmetric
gap of the given radius. -/
def sonineSourceGapFace (radius : ℝ) : ClosedSubmodule ℂ SonineSchwartz :=
  ⨅ x : {x : ℝ // |x| < radius}, soninePointKernel x

theorem mem_sonineSourceGapFace_iff
    (radius : ℝ) (test : SonineSchwartz) :
    test ∈ sonineSourceGapFace radius ↔
      ∀ x : ℝ, |x| < radius → test x = 0 := by
  constructor
  · intro membership x hx
    have atPoint := (ClosedSubmodule.mem_iInf.mp membership) ⟨x, hx⟩
    simpa [soninePointKernel] using atPoint
  · intro vanishes
    apply ClosedSubmodule.mem_iInf.mpr
    intro x
    simpa [soninePointKernel] using vanishes x.1 x.2

/-- Simultaneous source/Fourier gap face.  Both constraints are genuine
closed kernels; no completion or projection premise is stored. -/
def sonineTwoGapFace (sourceRadius fourierRadius : ℝ) :
    ClosedSubmodule ℂ SonineSchwartz :=
  sonineSourceGapFace sourceRadius ⊓
    (sonineSourceGapFace fourierRadius).comap
      (FourierTransform.fourierCLM ℂ SonineSchwartz)

theorem mem_sonineTwoGapFace_iff
    (sourceRadius fourierRadius : ℝ) (test : SonineSchwartz) :
    test ∈ sonineTwoGapFace sourceRadius fourierRadius ↔
      (∀ x : ℝ, |x| < sourceRadius → test x = 0) ∧
      (∀ x : ℝ, |x| < fourierRadius → (𝓕 test) x = 0) := by
  simp only [sonineTwoGapFace, ClosedSubmodule.mem_inf,
    ClosedSubmodule.mem_comap, mem_sonineSourceGapFace_iff,
    FourierTransform.fourierCLM_apply]

/-- Under Mathlib's self-dual normalization, two Fourier transforms are
reflection. -/
theorem sonine_fourier_fourier_apply (test : SonineSchwartz) (x : ℝ) :
    (𝓕 (𝓕 test)) x = test (-x) := by
  have inversion : 𝓕⁻ (𝓕 test) = test :=
    FourierTransform.fourierInv_fourier_eq test
  rw [SchwartzMap.fourierInv_apply_eq] at inversion
  have atNeg := congrArg (fun value : SonineSchwartz ↦ value (-x)) inversion
  simpa using atNeg

/-- The balanced two-gap face is genuinely Fourier/J invariant. -/
theorem fourier_mem_sonineTwoGapFace_one
    (test : SonineSchwartz)
    (membership : test ∈ sonineTwoGapFace 1 1) :
    𝓕 test ∈ sonineTwoGapFace 1 1 := by
  rw [mem_sonineTwoGapFace_iff] at membership ⊢
  constructor
  · exact membership.2
  · intro x hx
    rw [sonine_fourier_fourier_apply]
    apply membership.1
    simpa using hx

theorem fourierInv_mem_sonineTwoGapFace_one
    (test : SonineSchwartz)
    (membership : test ∈ sonineTwoGapFace 1 1) :
    𝓕⁻ test ∈ sonineTwoGapFace 1 1 := by
  rw [mem_sonineTwoGapFace_iff] at membership ⊢
  constructor
  · intro x hx
    rw [SchwartzMap.fourierInv_apply_eq]
    apply membership.2
    simpa using hx
  · intro x hx
    rw [FourierTransform.fourier_fourierInv_eq]
    exact membership.1 x hx

/-- The fixed balanced Sonine source type.  The linear-source carrier is the
underlying submodule of the closed face, so it retains the full additive-group
and complex-module instances required by generated Hilbert closure. -/
abbrev StageZeroBalancedSonineSource :=
  (sonineTwoGapFace 1 1).toSubmodule

/-- Fourier/J is an actual endomorphism of the fixed source face. -/
def stageZeroBalancedSonineFourier :
    StageZeroBalancedSonineSource →ₗ[ℂ] StageZeroBalancedSonineSource where
  toFun source :=
    ⟨𝓕 (source : SonineSchwartz),
      fourier_mem_sonineTwoGapFace_one source source.property⟩
  map_add' left right := by
    apply Subtype.ext
    exact (FourierTransform.fourierCLM ℂ SonineSchwartz).map_add left right
  map_smul' coefficient source := by
    apply Subtype.ext
    exact (FourierTransform.fourierCLM ℂ SonineSchwartz).map_smul
      coefficient source

/-- Fourier/J is an actual equivalence of the fixed balanced source face. -/
def stageZeroBalancedSonineFourierEquiv :
    StageZeroBalancedSonineSource ≃ₗ[ℂ] StageZeroBalancedSonineSource where
  toFun := stageZeroBalancedSonineFourier
  invFun source :=
    ⟨𝓕⁻ (source : SonineSchwartz),
      fourierInv_mem_sonineTwoGapFace_one source source.property⟩
  left_inv source := by
    apply Subtype.ext
    exact FourierTransform.fourierInv_fourier_eq
      (source : SonineSchwartz)
  right_inv source := by
    apply Subtype.ext
    exact FourierTransform.fourier_fourierInv_eq
      (source : SonineSchwartz)
  map_add' := stageZeroBalancedSonineFourier.map_add
  map_smul' := stageZeroBalancedSonineFourier.map_smul

@[simp] theorem stageZeroBalancedSonineFourier_coe
    (source : StageZeroBalancedSonineSource) :
    (stageZeroBalancedSonineFourier source : SonineSchwartz) =
      𝓕 (source : SonineSchwartz) :=
  rfl

end

end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid

