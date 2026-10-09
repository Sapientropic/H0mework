import H0mework.Versions.V2.Arithmetic.MellinProjection.AmbientMellinProjection
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaDiagonalBoundary

/-!
# Exact ambient commutator behind the `P_a⊥` diagonal defect

The fixed-annulus paired defect is not erased by naming a Fourier-symmetric
compression.  This file expands it into the ambient completed-Mellin kernel
covariance boundary and the literal commutator of the even Burnol projection
with paired multiplicative dilation.  No cancellation or kernel event is
assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

local instance boundaryCommutatorPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

local instance boundaryCommutatorPaOrthogonalComplete :
    CompleteSpace BurnolPaOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete

def burnolEvenAmbientProjection :
    BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
  (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto

def burnolEvenAmbientProjectionEndomorphism : BurnolL2 →L[ℂ] BurnolL2 :=
  (Submodule.subtypeL
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule).comp
    burnolEvenAmbientProjection

/-- Paired ambient failure of the explicit gap-tail kernel to transform by
its Mellin character. -/
def burnolPairedAmbientKernelCovarianceBoundary
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection
    (pairedMellinTranslationCharacter coordinate.value shift •
        burnolAmbientCompletedMellinRieszVector coordinate -
      pairedBurnolMultiplicativeDilation shift
        (burnolAmbientCompletedMellinRieszVector coordinate))

/-- Returned `P_even[P_even,A_h]K` commutator component. -/
def burnolPairedEvenProjectionCommutatorBoundary
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    BurnolPaAmbientCarrier :=
  burnolEvenAmbientProjection
      (pairedBurnolMultiplicativeDilation shift
        (burnolAmbientCompletedMellinRieszVector coordinate)) -
    burnolPairedAmbientCompression shift
      (burnolEvenAmbientProjection
        (burnolAmbientCompletedMellinRieszVector coordinate))

theorem burnolPairedEvenProjectionCommutatorBoundary_eq_commutator
    (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    burnolPairedEvenProjectionCommutatorBoundary coordinate shift =
      burnolEvenAmbientProjection
        ((burnolEvenAmbientProjectionEndomorphism.comp
              (pairedBurnolMultiplicativeDilation shift) -
            (pairedBurnolMultiplicativeDilation shift).comp
              burnolEvenAmbientProjectionEndomorphism)
          (burnolAmbientCompletedMellinRieszVector coordinate)) := by
  unfold burnolPairedEvenProjectionCommutatorBoundary
    burnolEvenAmbientProjectionEndomorphism burnolEvenAmbientProjection
    burnolPairedAmbientCompression evenBurnolMultiplicativeCompression
    SourceGeneratedCompressedUnitaryDefectPort.compression
    pairedBurnolMultiplicativeDilation
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    Submodule.subtypeL_apply, smul_apply, add_apply]
  rw [map_sub, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  simp only [map_smul, map_add]
  rfl

theorem burnolZeroPaRieszState_eq_ambientKernelProjection
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    (burnolZeroPaRieszState coordinate zero : BurnolPaAmbientCarrier) =
      burnolEvenAmbientProjection
        (burnolAmbientCompletedMellinRieszVector coordinate) := by
  change burnolCompletedMellinRieszVector coordinate = _
  exact burnolCompletedMellinRieszVector_eq_ambientProjection coordinate

/-- Paired boundary inside the fixed extended Sonine face. -/
def burnolZeroPairedFixedAnnulusBoundary
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    BurnolPaAmbientCarrier :=
  pairedMellinTranslationCharacter coordinate.value shift •
      (burnolZeroPaRieszState coordinate zero : BurnolPaAmbientCarrier) -
    burnolPairedAmbientCompression shift
      (burnolZeroPaRieszState coordinate zero : BurnolPaAmbientCarrier)

/-- Exact expansion into ambient covariance and projection commutator. -/
theorem burnolZeroPairedFixedAnnulusBoundary_ambient_commutator_factorization
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolZeroPairedFixedAnnulusBoundary coordinate zero shift =
      burnolPairedAmbientKernelCovarianceBoundary coordinate shift +
        burnolPairedEvenProjectionCommutatorBoundary coordinate shift := by
  rw [burnolZeroPairedFixedAnnulusBoundary,
    burnolZeroPaRieszState_eq_ambientKernelProjection]
  unfold burnolPairedAmbientKernelCovarianceBoundary
    burnolPairedEvenProjectionCommutatorBoundary
  simp only [map_sub, map_smul]
  module

def burnolZeroPairedFixedAnnulusBoundaryOrthogonal
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    BurnolPaOrthogonalCarrier :=
  burnolPaOrthogonalClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift)

theorem burnolZeroPairedBoundary_read_eq_orthogonalProjection_inner
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) =
      inner ℂ (burnolZeroPaRieszState coordinate zero)
        (burnolZeroPairedFixedAnnulusBoundaryOrthogonal
          coordinate zero shift) := by
  rw [← burnolZeroPaRieszState_readback coordinate zero
    (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift)]
  symm
  exact burnolPaOrthogonalClosedFace.toSubmodule
    |>.inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolZeroPaRieszState coordinate zero)
      (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift)

/-- The production diagonal defect is the negative read of the single
projected ambient covariance-plus-commutator boundary. -/
theorem burnolZeroPa_diagonalDefect_eq_neg_ambientCommutatorRead
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) (shift : ℝ) :
    inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolPaPairedDilationCompression shift
            (burnolZeroPaRieszState coordinate zero)) -
        pairedMellinTranslationCharacter coordinate.value shift *
          inner ℂ (burnolZeroPaRieszState coordinate zero)
            (burnolZeroPaRieszState coordinate zero) =
      -inner ℂ (burnolZeroPaRieszState coordinate zero)
        (burnolPaOrthogonalClosedFace.toSubmodule.orthogonalProjectionOnto
          (burnolPairedAmbientKernelCovarianceBoundary coordinate shift +
            burnolPairedEvenProjectionCommutatorBoundary coordinate shift)) := by
  have compressedRead :
      burnolCompletedMellinEvaluator coordinate
          (burnolPairedAmbientCompression shift
            (burnolZeroPaRieszState coordinate zero : BurnolPaAmbientCarrier)) =
        inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolPaPairedDilationCompression shift
            (burnolZeroPaRieszState coordinate zero)) := by
    rw [burnolPaPairedDilationCompression]
    simp only [ContinuousLinearMap.comp_apply]
    rw [burnolPaOrthogonalClosedFace.toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
    exact (burnolZeroPaRieszState_readback coordinate zero _).symm
  have baseRead :
      burnolCompletedMellinEvaluator coordinate
          (burnolZeroPaRieszState coordinate zero : BurnolPaAmbientCarrier) =
        inner ℂ (burnolZeroPaRieszState coordinate zero)
          (burnolZeroPaRieszState coordinate zero) :=
    (burnolZeroPaRieszState_readback coordinate zero _).symm
  calc
    _ = -burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero shift) := by
      unfold burnolZeroPairedFixedAnnulusBoundary
      rw [map_sub, map_smul, compressedRead, baseRead]
      ring
    _ = -inner ℂ (burnolZeroPaRieszState coordinate zero)
        (burnolZeroPairedFixedAnnulusBoundaryOrthogonal
          coordinate zero shift) :=
      congrArg Neg.neg
        (burnolZeroPairedBoundary_read_eq_orthogonalProjection_inner
          coordinate zero shift)
    _ = _ := by
      unfold burnolZeroPairedFixedAnnulusBoundaryOrthogonal
      rw [burnolZeroPairedFixedAnnulusBoundary_ambient_commutator_factorization]

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
