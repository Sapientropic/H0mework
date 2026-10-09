import H0mework.Versions.V2.Arithmetic.BurnolMellin.FourierSiblingOrthogonalityConsumer
import H0mework.Versions.R2.Arithmetic.RiemannSpectral.FourierFixedCompression

/-!
# Direct paired compression on the Burnol `P_a` orthogonal face

The zero-owned completed-Mellin Riesz vector already lies in the orthogonal
complement of the actual compact co-Poisson range.  This file equips that
same face with the paired forward/inverse multiplicative compression.  It
introduces no claim gate, pending state, auxiliary root, or branch classifier.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open SourceGeneratedCompressedUnitaryDefectPort
open scoped InnerProductSpace

noncomputable section

abbrev BurnolPaAmbientCarrier :=
  EvenBurnolPhysicalCarrier burnolUnscaledCommonGapRadius

local instance burnolPaAmbientCarrierComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolPaOrthogonalClosedFace : ClosedSubmodule ℂ BurnolPaAmbientCarrier where
  toSubmodule :=
    Submodule.orthogonal burnolCompactCoPoissonClosedRange.toSubmodule
  isClosed' := burnolCompactCoPoissonClosedRange.toSubmodule.isClosed_orthogonal

abbrev BurnolPaOrthogonalCarrier := burnolPaOrthogonalClosedFace.toSubmodule

local instance burnolPaOrthogonalCarrierComplete :
    CompleteSpace BurnolPaOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- The actual paired forward/inverse action before the `P_a`-orthogonal
projection. -/
def burnolPairedAmbientCompression (shift : ℝ) :
    BurnolPaAmbientCarrier →L[ℂ] BurnolPaAmbientCarrier :=
  (1 / 2 : ℂ) •
    (evenBurnolMultiplicativeCompression
        burnolUnscaledCommonGapRadius shift +
      evenBurnolMultiplicativeCompression
        burnolUnscaledCommonGapRadius (-shift))

/-- Orthogonal compression of the paired action to the actual `P_a⊥`
physical face. -/
def burnolPaPairedDilationCompression (shift : ℝ) :
    BurnolPaOrthogonalCarrier →L[ℂ] BurnolPaOrthogonalCarrier :=
  burnolPaOrthogonalClosedFace.toSubmodule.orthogonalProjectionOnto.comp
    ((burnolPairedAmbientCompression shift).comp
      burnolPaOrthogonalClosedFace.toSubmodule.subtypeL)

theorem burnolPairedAmbientCompression_symmetric
    (shift : ℝ) (left right : BurnolPaAmbientCarrier) :
    inner ℂ (burnolPairedAmbientCompression shift left) right =
      inner ℂ left (burnolPairedAmbientCompression shift right) := by
  let forward := evenBurnolMultiplicativeCompression
    burnolUnscaledCommonGapRadius shift
  let inverse := evenBurnolMultiplicativeCompression
    burnolUnscaledCommonGapRadius (-shift)
  have forwardAdjoint (x y : BurnolPaAmbientCarrier) :
      inner ℂ (forward x) y = inner ℂ x (inverse y) := by
    calc
      _ = inner ℂ
          (burnolMultiplicativeDilation shift (x : BurnolL2))
          (y : BurnolL2) :=
        compression_inner_left_readback
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation shift).toLinearIsometry x y
      _ = inner ℂ (x : BurnolL2)
          (burnolMultiplicativeDilation (-shift) (y : BurnolL2)) := by
        rw [burnolMultiplicativeDilation_neg_eq_symm]
        exact (burnolMultiplicativeDilation shift).inner_map_eq_flip _ _
      _ = inner ℂ x (inverse y) :=
        (compression_inner_right_readback
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation (-shift)).toLinearIsometry x y).symm
  have inverseAdjoint (x y : BurnolPaAmbientCarrier) :
      inner ℂ (inverse x) y = inner ℂ x (forward y) := by
    calc
      _ = inner ℂ
          (burnolMultiplicativeDilation (-shift) (x : BurnolL2))
          (y : BurnolL2) :=
        compression_inner_left_readback
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation (-shift)).toLinearIsometry x y
      _ = inner ℂ (x : BurnolL2)
          (burnolMultiplicativeDilation shift (y : BurnolL2)) := by
        calc
          _ = inner ℂ (x : BurnolL2)
              ((burnolMultiplicativeDilation (-shift)).symm
                (y : BurnolL2)) :=
            (burnolMultiplicativeDilation (-shift)).inner_map_eq_flip _ _
          _ = _ := by
            rw [← burnolMultiplicativeDilation_neg_eq_symm (-shift), neg_neg]
      _ = inner ℂ x (forward y) :=
        (compression_inner_right_readback
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation shift).toLinearIsometry x y).symm
  have sumSymmetric : (forward + inverse).toLinearMap.IsSymmetric := by
    intro x y
    change inner ℂ (forward x + inverse x) y =
      inner ℂ x (forward y + inverse y)
    rw [inner_add_left, inner_add_right, forwardAdjoint, inverseAdjoint]
    abel
  have halfReal : star (1 / 2 : ℂ) = (1 / 2 : ℂ) := by norm_num
  exact (sumSymmetric.smul halfReal) left right

theorem burnolPaPairedDilationCompression_symmetric
    (shift : ℝ) (left right : BurnolPaOrthogonalCarrier) :
    inner ℂ (burnolPaPairedDilationCompression shift left) right =
      inner ℂ left (burnolPaPairedDilationCompression shift right) := by
  rw [burnolPaPairedDilationCompression]
  simp only [ContinuousLinearMap.comp_apply]
  rw [burnolPaOrthogonalClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [burnolPaOrthogonalClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact burnolPairedAmbientCompression_symmetric shift left right

theorem burnolPaPairedDilationCompression_contractive
    (shift : ℝ) (state : BurnolPaOrthogonalCarrier) :
    ‖burnolPaPairedDilationCompression shift state‖ ≤ ‖state‖ := by
  calc
    ‖burnolPaPairedDilationCompression shift state‖ ≤
        ‖burnolPairedAmbientCompression shift
          (state : BurnolPaAmbientCarrier)‖ :=
      burnolPaOrthogonalClosedFace.toSubmodule.norm_orthogonalProjectionOnto_apply_le _
    _ ≤ (1 / 2 : ℝ) *
          (‖evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius shift
              (state : BurnolPaAmbientCarrier)‖ +
            ‖evenBurnolMultiplicativeCompression burnolUnscaledCommonGapRadius (-shift)
              (state : BurnolPaAmbientCarrier)‖) := by
      unfold burnolPairedAmbientCompression
      rw [smul_apply, add_apply, norm_smul]
      have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [halfNorm]
      exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ ≤ (1 / 2 : ℝ) * (‖state‖ + ‖state‖) := by
      gcongr
      · exact norm_compression_le
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation shift).toLinearIsometry _
      · exact norm_compression_le
          (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
          (burnolMultiplicativeDilation (-shift)).toLinearIsometry _
    _ = ‖state‖ := by ring

/-- The zero-owned completed-Mellin Riesz state in the actual physical
orthogonal face. -/
def burnolZeroPaRieszState
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) : BurnolPaOrthogonalCarrier :=
  ⟨burnolCompletedMellinRieszVector coordinate,
    riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
      coordinate zero⟩

theorem burnolZeroPaRieszState_readback
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0)
    (value : BurnolPaAmbientCarrier) :
    inner ℂ (burnolZeroPaRieszState coordinate zero : BurnolL2)
        (value : BurnolL2) =
      burnolCompletedMellinEvaluator coordinate value :=
  burnolCompletedMellinRieszVector_readback coordinate value

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
