import H0mework.Versions.V2.Arithmetic.RiemannDivision.AnalyticComplementExactOrderPhysicalRead
import H0mework.Versions.V2.Arithmetic.RiemannSpectral.PaOrthogonalCompression

/-!
# Exact-order modified-WeakFE state in the Burnol residual face

The analytic-complement division state and its Fourier sibling are projected
to the actual `P_a` orthogonal carrier.  The source-generated nonzero Mellin
read forces the Fourier residual to be nonzero; Fourier invariance of `P_a`
then produces the nonzero position sibling in the same occurrence.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState

open SourceGeneratedHilbertCokernel
open scoped InnerProductSpace

noncomputable section

local instance analyticComplementPaAmbientComplete :
    CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The position face of the exact-order source occurrence in `P_a⊥`. -/
def burnolAnalyticComplementExactOrderPaPositionResidualState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    BurnolPaOrthogonalCarrier :=
  residual burnolCompactCoPoissonLanding
    (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)

/-- The Fourier face of the same exact-order source occurrence in `P_a⊥`. -/
def burnolAnalyticComplementExactOrderPaFourierResidualState
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    BurnolPaOrthogonalCarrier :=
  residual burnolCompactCoPoissonLanding
    (burnolAnalyticComplementExactOrderPhysicalFourierState
      observation nontrivial)

/-- Fourier action on the quotient sends the position face to its sibling. -/
theorem burnolAnalyticComplementExactOrderPaPositionResidualState_fourier
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolCompactCoPoissonActionSquare.orthogonalAction
        (burnolAnalyticComplementExactOrderPaPositionResidualState
          observation nontrivial) =
      burnolAnalyticComplementExactOrderPaFourierResidualState
        observation nontrivial := by
  exact burnolCompactCoPoissonActionSquare.orthogonalAction_residual
    (burnolAnalyticComplementExactOrderPhysicalState observation nontrivial)

/-- The same action returns the Fourier face to the position face. -/
theorem burnolAnalyticComplementExactOrderPaFourierResidualState_fourier
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    burnolCompactCoPoissonActionSquare.orthogonalAction
        (burnolAnalyticComplementExactOrderPaFourierResidualState
          observation nontrivial) =
      burnolAnalyticComplementExactOrderPaPositionResidualState
        observation nontrivial := by
  rw [← burnolAnalyticComplementExactOrderPaPositionResidualState_fourier]
  apply Subtype.ext
  exact evenFaceFourier_involutive burnolUnscaledCommonGapRadius _

/-- The exact Riesz pairing with the quotient state is the generated physical
Fourier read, not a separately supplied scalar. -/
theorem burnolAnalyticComplementExactOrderPaFourierResidualState_readback
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    inner ℂ
        (burnolZeroPaRieszState
          (burnolAnalyticComplementCompletedMellinCoordinate
            observation rightHalf)
          observation.mathlibZero)
        (burnolAnalyticComplementExactOrderPaFourierResidualState
          observation nontrivial) =
      burnolAnalyticComplementExpectedPhysicalFourierRead owner observation := by
  let coordinate :=
    burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
  have coordinateZero : riemannZeta coordinate.value = 0 := by
    simpa [coordinate, burnolAnalyticComplementCompletedMellinCoordinate] using
      observation.mathlibZero
  let riesz := burnolZeroPaRieszState coordinate coordinateZero
  let value := burnolAnalyticComplementExactOrderPhysicalFourierState
    observation nontrivial
  have projectionRead :
      inner ℂ riesz (residual burnolCompactCoPoissonLanding value) =
        inner ℂ (riesz : BurnolPaAmbientCarrier) value := by
    exact burnolPaOrthogonalClosedFace.toSubmodule
      |>.inner_orthogonalProjectionOnto_eq_of_mem_left riesz value
  rw [show burnolAnalyticComplementExactOrderPaFourierResidualState
      observation nontrivial =
        residual burnolCompactCoPoissonLanding value by rfl,
    projectionRead]
  change inner ℂ (riesz : BurnolL2) (value : BurnolL2) = _
  rw [burnolZeroPaRieszState_readback]
  exact burnolAnalyticComplementExactOrderPhysicalFourierRead_eq_expected
    observation nontrivial rightHalf

/-- The actual exact-order Fourier residual is occupied.  If it vanished,
the physical Fourier state would lie in `P_a`, contradicting its generated
nonzero completed-Mellin read at the same zero. -/
theorem burnolAnalyticComplementExactOrderPaFourierResidualState_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementExactOrderPaFourierResidualState
        observation nontrivial ≠ 0 := by
  intro stateZero
  let coordinate :=
    burnolAnalyticComplementCompletedMellinCoordinate observation rightHalf
  let value := burnolAnalyticComplementExactOrderPhysicalFourierState
    observation nontrivial
  have valueInRange : value ∈ burnolCompactCoPoissonClosedRange := by
    apply (residual_eq_zero_iff burnolCompactCoPoissonLanding value).mp
    exact stateZero
  have rieszOrthogonal : burnolCompletedMellinRieszVector coordinate ∈
      Submodule.orthogonal burnolCompactCoPoissonClosedRange.toSubmodule :=
    riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal
      coordinate observation.mathlibZero
  have evaluatorZero : burnolCompletedMellinEvaluator coordinate value = 0 := by
    rw [← burnolCompletedMellinRieszVector_readback]
    rw [inner_eq_zero_symm]
    exact rieszOrthogonal value valueInRange
  exact (burnolAnalyticComplementExactOrderPhysicalFourierRead_ne_zero_generated
    observation nontrivial rightHalf) evaluatorZero

/-- Fourier invariance transports actual occupation back to the position
face; no symmetrized-state nonvanishing assumption is used. -/
theorem burnolAnalyticComplementExactOrderPaPositionResidualState_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolAnalyticComplementExactOrderPaPositionResidualState
        observation nontrivial ≠ 0 := by
  intro stateZero
  apply burnolAnalyticComplementExactOrderPaFourierResidualState_ne_zero
    observation nontrivial rightHalf
  rw [← burnolAnalyticComplementExactOrderPaPositionResidualState_fourier,
    stateZero]
  change burnolCompactCoPoissonActionSquare.orthogonalAction
      (0 : OrthogonalResidual burnolCompactCoPoissonLanding) = 0
  exact burnolCompactCoPoissonActionSquare.orthogonalAction.map_zero

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
