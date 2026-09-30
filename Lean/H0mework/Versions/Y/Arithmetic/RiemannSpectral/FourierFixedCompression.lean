import H0mework.Versions.Y.Arithmetic.RiemannSpectral.MultiplicativeDilation
import H0mework.Arithmetic.BurnolMellin.PairedMellinCharacter

/-!
# Fourier-fixed Burnol multiplicative compression

The even constant-gap face is Fourier invariant, but Fourier is not the
identity on that whole face.  Its fixed closed submodule is the actual
`J = 1` physical sector.  Normalized multiplicative dilation is first
compressed to the even Burnol face and then to this fixed sector.

The source law `J D_h = D_h⁻¹ J` makes the resulting bounded operator
self-adjoint and contractive.  Its matrix coefficients are exactly those of
the paired forward/inverse dilation, while the scalar sibling is the existing
paired Mellin character.  Parity reflection is not used as a Tate action.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open SourceGeneratedCompressedUnitaryDefectPort
open scoped InnerProductSpace

noncomputable section

local instance evenBurnolCarrierComplete (radius : ℝ) :
    CompleteSpace (EvenBurnolPhysicalCarrier radius) := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace radius).isClosed.isComplete

def evenBurnolMultiplicativeCompression (radius shift : ℝ) :
    EvenBurnolPhysicalCarrier radius →L[ℂ]
      EvenBurnolPhysicalCarrier radius :=
  compression (evenBurnolClosedFace radius)
    (burnolMultiplicativeDilation shift).toLinearIsometry

theorem evenFaceFourier_multiplicativeCompression_adjoint
    (radius shift : ℝ) (state : EvenBurnolPhysicalCarrier radius) :
    evenFaceFourierEquiv radius
        (evenBurnolMultiplicativeCompression radius shift state) =
      ContinuousLinearMap.adjoint
        (evenBurnolMultiplicativeCompression radius shift)
        (evenFaceFourierEquiv radius state) := by
  exact compression_J_adjoint_sibling
    (evenBurnolClosedFace radius)
    (burnolMultiplicativeDilation shift)
    fourierL2
    (evenBurnolFourierBalanced radius)
    (fourierL2_burnolMultiplicativeDilation_inverse shift)
    state

def evenBurnolFourierFixedFace (radius : ℝ) :
    ClosedSubmodule ℂ (EvenBurnolPhysicalCarrier radius) where
  toSubmodule :=
    ((evenFaceFourierEquiv radius).toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℂ (EvenBurnolPhysicalCarrier radius)).ker
  isClosed' :=
    ((evenFaceFourierEquiv radius).toContinuousLinearEquiv.toContinuousLinearMap -
      ContinuousLinearMap.id ℂ (EvenBurnolPhysicalCarrier radius)).isClosed_ker

theorem mem_evenBurnolFourierFixedFace_iff
    {radius : ℝ} {state : EvenBurnolPhysicalCarrier radius} :
    state ∈ evenBurnolFourierFixedFace radius ↔
      evenFaceFourierEquiv radius state = state := by
  change ((evenFaceFourierEquiv radius).toContinuousLinearEquiv.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ (EvenBurnolPhysicalCarrier radius)) state = 0 ↔ _
  change evenFaceFourierEquiv radius state - state = 0 ↔ _
  exact sub_eq_zero

abbrev EvenBurnolFourierFixedCarrier (radius : ℝ) :=
  (evenBurnolFourierFixedFace radius).toSubmodule

local instance evenBurnolFourierFixedCarrierInnerProductSpace (radius : ℝ) :
    InnerProductSpace ℂ (EvenBurnolFourierFixedCarrier radius) :=
  inferInstance

local instance evenBurnolFourierFixedCarrierComplete (radius : ℝ) :
    CompleteSpace (EvenBurnolFourierFixedCarrier radius) := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolFourierFixedFace radius).isClosed.isComplete

def evenBurnolFourierFixedCompression (radius shift : ℝ) :
    EvenBurnolFourierFixedCarrier radius →L[ℂ]
      EvenBurnolFourierFixedCarrier radius :=
  (evenBurnolFourierFixedFace radius).toSubmodule.orthogonalProjectionOnto.comp
    ((evenBurnolMultiplicativeCompression radius shift).comp
      (evenBurnolFourierFixedFace radius).toSubmodule.subtypeL)

theorem evenBurnolFourierFixedCompression_inner_left
    (radius shift : ℝ) (left right : EvenBurnolFourierFixedCarrier radius) :
    inner ℂ (evenBurnolFourierFixedCompression radius shift left) right =
      inner ℂ
        (evenBurnolMultiplicativeCompression radius shift (left :
          EvenBurnolPhysicalCarrier radius))
        (right : EvenBurnolPhysicalCarrier radius) := by
  simp [evenBurnolFourierFixedCompression]

theorem evenBurnolFourierFixedCompression_inner_right
    (radius shift : ℝ) (left right : EvenBurnolFourierFixedCarrier radius) :
    inner ℂ left (evenBurnolFourierFixedCompression radius shift right) =
      inner ℂ (left : EvenBurnolPhysicalCarrier radius)
        (evenBurnolMultiplicativeCompression radius shift
          (right : EvenBurnolPhysicalCarrier radius)) := by
  simp [evenBurnolFourierFixedCompression]

theorem evenBurnolFourierFixedCompression_symmetric
    (radius shift : ℝ)
    (left right : EvenBurnolFourierFixedCarrier radius) :
    inner ℂ (evenBurnolFourierFixedCompression radius shift left) right =
      inner ℂ left
        (evenBurnolFourierFixedCompression radius shift right) := by
  rw [evenBurnolFourierFixedCompression_inner_left,
    evenBurnolFourierFixedCompression_inner_right]
  let J := evenFaceFourierEquiv radius
  let C := evenBurnolMultiplicativeCompression radius shift
  have leftFixed : J (left : EvenBurnolPhysicalCarrier radius) = left :=
    mem_evenBurnolFourierFixedFace_iff.mp left.property
  have rightFixed : J (right : EvenBurnolPhysicalCarrier radius) = right :=
    mem_evenBurnolFourierFixedFace_iff.mp right.property
  have sibling := evenFaceFourier_multiplicativeCompression_adjoint
    radius shift (left : EvenBurnolPhysicalCarrier radius)
  change J (C (left : EvenBurnolPhysicalCarrier radius)) =
    ContinuousLinearMap.adjoint C
      (J (left : EvenBurnolPhysicalCarrier radius)) at sibling
  rw [leftFixed] at sibling
  calc
    inner ℂ (C (left : EvenBurnolPhysicalCarrier radius))
        (right : EvenBurnolPhysicalCarrier radius) =
      inner ℂ (J (C (left : EvenBurnolPhysicalCarrier radius)))
        (J (right : EvenBurnolPhysicalCarrier radius)) :=
      (J.inner_map_map _ _).symm
    _ = inner ℂ (ContinuousLinearMap.adjoint C
          (left : EvenBurnolPhysicalCarrier radius))
        (right : EvenBurnolPhysicalCarrier radius) := by
      rw [sibling, rightFixed]
    _ = inner ℂ (left : EvenBurnolPhysicalCarrier radius)
        (C (right : EvenBurnolPhysicalCarrier radius)) := by
      rw [ContinuousLinearMap.adjoint_inner_left]

theorem evenBurnolFourierFixedCompression_isSymmetric
    (radius shift : ℝ) :
    @LinearMap.IsSymmetric ℂ
      (EvenBurnolFourierFixedCarrier radius)
      _ _ _
      (evenBurnolFourierFixedCompression radius shift).toLinearMap :=
  evenBurnolFourierFixedCompression_symmetric radius shift

theorem evenBurnolFourierFixedCompression_contractive
    (radius shift : ℝ) (state : EvenBurnolFourierFixedCarrier radius) :
    ‖evenBurnolFourierFixedCompression radius shift state‖ ≤ ‖state‖ := by
  calc
    ‖evenBurnolFourierFixedCompression radius shift state‖ ≤
        ‖evenBurnolMultiplicativeCompression radius shift
          (state : EvenBurnolPhysicalCarrier radius)‖ := by
      exact (evenBurnolFourierFixedFace radius).toSubmodule.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ ‖(state : EvenBurnolPhysicalCarrier radius)‖ :=
      norm_compression_le (evenBurnolClosedFace radius)
        (burnolMultiplicativeDilation shift).toLinearIsometry _
    _ = ‖state‖ := rfl

def pairedBurnolMultiplicativeDilation (shift : ℝ) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  (1 / 2 : ℂ) •
    ((burnolMultiplicativeDilation shift).toContinuousLinearEquiv.toContinuousLinearMap +
      (burnolMultiplicativeDilation (-shift)).toContinuousLinearEquiv.toContinuousLinearMap)

theorem evenBurnolFourierFixedCompression_inner_eq_pairedDilation
    (radius shift : ℝ) (left right : EvenBurnolFourierFixedCarrier radius) :
    inner ℂ left (evenBurnolFourierFixedCompression radius shift right) =
      inner ℂ (left : BurnolL2)
        (pairedBurnolMultiplicativeDilation shift (right : BurnolL2)) := by
  rw [evenBurnolFourierFixedCompression_inner_right]
  unfold evenBurnolMultiplicativeCompression
  rw [compression_inner_right_readback]
  have leftFixed :=
    mem_evenBurnolFourierFixedFace_iff.mp left.property
  have rightFixed :=
    mem_evenBurnolFourierFixedFace_iff.mp right.property
  have leftFourier : fourierL2 (left : BurnolL2) = left := by
    exact congrArg Subtype.val leftFixed
  have rightFourier : fourierL2 (right : BurnolL2) = right := by
    exact congrArg Subtype.val rightFixed
  have inverseInner :
      inner ℂ (left : BurnolL2)
          (burnolMultiplicativeDilation shift (right : BurnolL2)) =
        inner ℂ (left : BurnolL2)
          (burnolMultiplicativeDilation (-shift) (right : BurnolL2)) := by
    calc
      _ = inner ℂ (fourierL2 (left : BurnolL2))
          (fourierL2
            (burnolMultiplicativeDilation shift (right : BurnolL2))) :=
        (fourierL2.inner_map_map _ _).symm
      _ = inner ℂ (left : BurnolL2)
          (burnolMultiplicativeDilation (-shift)
            (fourierL2 (right : BurnolL2))) := by
        rw [fourierL2_burnolMultiplicativeDilation, leftFourier]
      _ = _ := by rw [rightFourier]
  change inner ℂ (left : BurnolL2)
      (burnolMultiplicativeDilation shift (right : BurnolL2)) =
    inner ℂ (left : BurnolL2)
      ((1 / 2 : ℂ) •
        (burnolMultiplicativeDilation shift (right : BurnolL2) +
          burnolMultiplicativeDilation (-shift) (right : BurnolL2)))
  rw [inner_smul_right, inner_add_right, ← inverseInner]
  ring

theorem pairedMellinTranslationCharacter_smul_eq_paired
    (coordinate : ℂ) (shift : ℝ) (state : BurnolL2) :
    pairedMellinTranslationCharacter coordinate shift • state =
      (1 / 2 : ℂ) •
        (fullMellinTranslationCharacter coordinate shift • state +
          reciprocalMellinTranslationCharacter coordinate shift • state) := by
  unfold pairedMellinTranslationCharacter
  module

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
