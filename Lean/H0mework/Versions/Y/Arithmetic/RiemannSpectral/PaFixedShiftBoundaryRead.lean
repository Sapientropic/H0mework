import H0mework.Versions.Y.Arithmetic.MellinProjection.PaBoundaryCommutator

/-!
# Fixed-shift Burnol boundary read

The existing completed-Mellin evaluator reads the exact ambient
covariance-plus-commutator boundary as the negative `P_a` diagonal residual.
This is a subordinate physical readback.  It neither defines a debt step nor
turns vanishing of the read into a source event; an actual complete-state
action must generate that vanishing before the responsibility compiler may
consume it.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open scoped InnerProductSpace

noncomputable section

/-- The existing ambient action boundary has exactly the negative of the live
`P_a` diagonal residual as its completed-Mellin read. -/
theorem fixedShiftBoundaryRead_eq_neg_residual
    (coordinate : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta coordinate.value = 0) :
    burnolCompletedMellinEvaluator coordinate
        (burnolZeroPairedFixedAnnulusBoundary coordinate zero
          (Real.log stageZeroSonineQ)) =
      -burnolPaFixedShiftResidual coordinate zero := by
  have diagonal := burnolZeroPa_diagonalDefect_eq_neg_ambientCommutatorRead
    coordinate zero (Real.log stageZeroSonineQ)
  rw [← burnolZeroPairedFixedAnnulusBoundary_ambient_commutator_factorization
    coordinate zero (Real.log stageZeroSonineQ)] at diagonal
  change _ = -inner ℂ (burnolZeroPaRieszState coordinate zero)
    (burnolZeroPairedFixedAnnulusBoundaryOrthogonal coordinate zero
      (Real.log stageZeroSonineQ)) at diagonal
  rw [← burnolZeroPairedBoundary_read_eq_orthogonalProjection_inner
    coordinate zero (Real.log stageZeroSonineQ)] at diagonal
  unfold burnolPaFixedShiftResidual
  have negated := congrArg Neg.neg diagonal
  simpa only [neg_neg] using negated.symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
