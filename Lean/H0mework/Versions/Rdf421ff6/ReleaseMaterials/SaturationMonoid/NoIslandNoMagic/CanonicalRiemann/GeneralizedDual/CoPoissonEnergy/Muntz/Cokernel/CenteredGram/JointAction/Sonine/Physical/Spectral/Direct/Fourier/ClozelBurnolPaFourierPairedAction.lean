import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaOrthogonalCompression

/-!
# Fourier naturality of the paired action on `P_a⊥`

The paired forward/inverse multiplicative compression commutes with ordinary
Fourier.  Consequently its coefficient matrix on a state and its Fourier
sibling has equal diagonal and equal off-diagonal entries.  These identities
remove both orthogonal projections; they do not assume an eigenvalue.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open SourceGeneratedCompressedUnitaryDefectPort
open scoped InnerProductSpace

noncomputable section

local instance burnolFourierPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance burnolFourierPaOrthogonalComplete :
    CompleteSpace BurnolPaOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

/-- The existing Fourier action with the concrete `P_a⊥` carrier spelling
used by the paired compression. -/
def burnolPaFourierAction :
    BurnolPaOrthogonalCarrier ≃ₗᵢ[ℂ] BurnolPaOrthogonalCarrier :=
  burnolCompactCoPoissonActionSquare.orthogonalAction

@[simp] theorem burnolPaFourierAction_coe
    (state : BurnolPaOrthogonalCarrier) :
    (burnolPaFourierAction state : BurnolPaAmbientCarrier) =
      evenFaceFourierEquiv burnolUnscaledCommonGapRadius
        (state : BurnolPaAmbientCarrier) :=
  rfl

/-- Matrix coefficients of the quotient compression are the literal ambient
paired-dilation coefficients. -/
theorem burnolPaPairedDilationCompression_inner_eq_ambient
    (shift : ℝ) (left right : BurnolPaOrthogonalCarrier) :
    inner ℂ left (burnolPaPairedDilationCompression shift right) =
      inner ℂ (left : BurnolL2)
        (pairedBurnolMultiplicativeDilation shift (right : BurnolL2)) := by
  let leftAmbient : BurnolPaAmbientCarrier := left
  let rightAmbient : BurnolPaAmbientCarrier :=
    burnolPaOrthogonalClosedFace.toSubmodule.subtypeL right
  have projectionRead :
      inner ℂ left
          (burnolPaOrthogonalClosedFace.toSubmodule.orthogonalProjectionOnto
            (burnolPairedAmbientCompression shift rightAmbient)) =
        inner ℂ leftAmbient
          (burnolPairedAmbientCompression shift rightAmbient) :=
    burnolPaOrthogonalClosedFace.toSubmodule
      |>.inner_orthogonalProjectionOnto_eq_of_mem_left left _
  have forwardRead :
      inner ℂ (leftAmbient : BurnolL2)
          ((evenBurnolMultiplicativeCompression
            burnolUnscaledCommonGapRadius shift rightAmbient :
              BurnolPaAmbientCarrier) : BurnolL2) =
        inner ℂ (leftAmbient : BurnolL2)
          (burnolMultiplicativeDilation shift (rightAmbient : BurnolL2)) :=
    compression_inner_right_readback
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
      (burnolMultiplicativeDilation shift).toLinearIsometry
      leftAmbient rightAmbient
  have inverseRead :
      inner ℂ (leftAmbient : BurnolL2)
          ((evenBurnolMultiplicativeCompression
            burnolUnscaledCommonGapRadius (-shift) rightAmbient :
              BurnolPaAmbientCarrier) : BurnolL2) =
        inner ℂ (leftAmbient : BurnolL2)
          (burnolMultiplicativeDilation (-shift) (rightAmbient : BurnolL2)) :=
    compression_inner_right_readback
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius)
      (burnolMultiplicativeDilation (-shift)).toLinearIsometry
      leftAmbient rightAmbient
  calc
    _ = inner ℂ leftAmbient
        (burnolPairedAmbientCompression shift rightAmbient) := by
      simpa only [burnolPaPairedDilationCompression,
        ContinuousLinearMap.comp_apply, leftAmbient, rightAmbient] using
          projectionRead
    _ = (1 / 2 : ℂ) *
        (inner ℂ (leftAmbient : BurnolL2)
            (burnolMultiplicativeDilation shift (rightAmbient : BurnolL2)) +
          inner ℂ (leftAmbient : BurnolL2)
            (burnolMultiplicativeDilation (-shift)
              (rightAmbient : BurnolL2))) := by
      unfold burnolPairedAmbientCompression
      simp only [smul_apply, add_apply]
      change inner ℂ (leftAmbient : BurnolL2)
          ((1 / 2 : ℂ) •
            (((evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius shift rightAmbient :
                  BurnolPaAmbientCarrier) : BurnolL2) +
              ((evenBurnolMultiplicativeCompression
                burnolUnscaledCommonGapRadius (-shift) rightAmbient :
                  BurnolPaAmbientCarrier) : BurnolL2))) = _
      rw [inner_smul_right, inner_add_right, forwardRead, inverseRead]
    _ = _ := by
      unfold pairedBurnolMultiplicativeDilation
      change (1 / 2 : ℂ) *
          (inner ℂ (leftAmbient : BurnolL2)
              (burnolMultiplicativeDilation shift (rightAmbient : BurnolL2)) +
            inner ℂ (leftAmbient : BurnolL2)
              (burnolMultiplicativeDilation (-shift)
                (rightAmbient : BurnolL2))) =
        inner ℂ (leftAmbient : BurnolL2)
          ((1 / 2 : ℂ) •
            (burnolMultiplicativeDilation shift (rightAmbient : BurnolL2) +
              burnolMultiplicativeDilation (-shift)
                (rightAmbient : BurnolL2)))
      rw [inner_smul_right, inner_add_right]

/-- The ambient paired action commutes with ordinary Fourier because Fourier
interchanges the two dilation directions. -/
theorem pairedBurnolMultiplicativeDilation_fourier
    (shift : ℝ) (state : BurnolL2) :
    pairedBurnolMultiplicativeDilation shift (fourierL2 state) =
      fourierL2 (pairedBurnolMultiplicativeDilation shift state) := by
  unfold pairedBurnolMultiplicativeDilation
  simp only [smul_apply, add_apply, map_smul, map_add]
  change (1 / 2 : ℂ) •
      (burnolMultiplicativeDilation shift (fourierL2 state) +
        burnolMultiplicativeDilation (-shift) (fourierL2 state)) =
    (1 / 2 : ℂ) •
      (fourierL2 (burnolMultiplicativeDilation shift state) +
        fourierL2 (burnolMultiplicativeDilation (-shift) state))
  rw [fourierL2_burnolMultiplicativeDilation,
    fourierL2_burnolMultiplicativeDilation, neg_neg]
  abel

/-- The paired compression has the same diagonal coefficient on a state and
its Fourier sibling. -/
theorem burnolPairedCompression_fourier_diagonal
    (shift : ℝ) (state : BurnolPaOrthogonalCarrier) :
    inner ℂ
        (burnolPaFourierAction state)
        (burnolPaPairedDilationCompression shift
          (burnolPaFourierAction state)) =
      inner ℂ state (burnolPaPairedDilationCompression shift state) := by
  rw [burnolPaPairedDilationCompression_inner_eq_ambient,
    burnolPaPairedDilationCompression_inner_eq_ambient]
  change inner ℂ (fourierL2 (state : BurnolL2))
      (pairedBurnolMultiplicativeDilation shift
        (fourierL2 (state : BurnolL2))) = _
  rw [pairedBurnolMultiplicativeDilation_fourier]
  exact fourierL2.inner_map_map _ _

/-- The two off-diagonal coefficients of the Fourier sibling pair coincide. -/
theorem burnolPairedCompression_fourier_cross
    (shift : ℝ) (left right : BurnolPaOrthogonalCarrier) :
      inner ℂ left
        (burnolPaPairedDilationCompression shift
          (burnolPaFourierAction right)) =
      inner ℂ
        (burnolPaFourierAction left)
        (burnolPaPairedDilationCompression shift right) := by
  rw [burnolPaPairedDilationCompression_inner_eq_ambient,
    burnolPaPairedDilationCompression_inner_eq_ambient]
  change inner ℂ (left : BurnolL2)
      (pairedBurnolMultiplicativeDilation shift
        (fourierL2 (right : BurnolL2))) =
    inner ℂ (fourierL2 (left : BurnolL2))
      (pairedBurnolMultiplicativeDilation shift (right : BurnolL2))
  rw [pairedBurnolMultiplicativeDilation_fourier]
  have doubleFourier :
      fourierL2 (fourierL2 (left : BurnolL2)) = (left : BurnolL2) := by
    exact congrArg Subtype.val
      (evenFaceFourier_involutive burnolUnscaledCommonGapRadius
        (left : BurnolPaAmbientCarrier))
  calc
    inner ℂ (left : BurnolL2)
        (fourierL2
          (pairedBurnolMultiplicativeDilation shift (right : BurnolL2))) =
      inner ℂ
          (fourierL2 (fourierL2 (left : BurnolL2)))
          (fourierL2
            (pairedBurnolMultiplicativeDilation shift (right : BurnolL2))) := by
        rw [doubleFourier]
    _ = _ := fourierL2.inner_map_map _ _

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
