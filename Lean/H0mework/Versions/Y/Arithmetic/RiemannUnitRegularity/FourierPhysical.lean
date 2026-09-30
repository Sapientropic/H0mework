import H0mework.Versions.Y.Arithmetic.RemainderSource.InnerPower
import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.FourierSource

/-! The same zero-owned unit source generates a nonzero Fourier-fixed vector
in the original Pa orthogonal face.  Its original paired dilation compression
is the downstream operator; no eigencharacter is supplied by this construction. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def burnolZeroOwnedUnitFourierState {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  burnolZeroOwnedUnitTailState observation nontrivial rightHalf +
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolZeroOwnedUnitTailState observation nontrivial rightHalf)

theorem burnolZeroOwnedUnitFourierState_fixed {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolZeroOwnedUnitFourierState observation nontrivial rightHalf) =
        burnolZeroOwnedUnitFourierState observation nontrivial rightHalf := by
  unfold burnolZeroOwnedUnitFourierState
  have twice : evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
        (burnolZeroOwnedUnitTailState observation nontrivial rightHalf)) =
      burnolZeroOwnedUnitTailState observation nontrivial rightHalf :=
    evenFaceFourier_involutive burnolUnscaledCommonGapRadius _
  rw [map_add, twice]
  exact add_comm _ _

theorem burnolZeroOwnedUnitFourierState_notInPa {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolZeroOwnedUnitFourierState observation nontrivial rightHalf ∉ burnolCompactCoPoissonClosedRange := by
  intro belongs
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  let state := burnolZeroOwnedUnitFourierState observation nontrivial rightHalf
  let tau := burnolNormalizedFirstSourceUnitTail coordinate
  apply burnolUnitFourierSourceDefect_nonzero coordinate state
  apply burnolRemainderSourceRead_faithful_of_innerPower coordinate.value coordinate.rightHalf (-1) _
    (burnolUnitFourierSourceDefect_even coordinate state) (burnolUnitFourierSourceDefect_innerPower coordinate state)
  intro test
  have original := burnolOriginalUnitTail_realizes coordinate test
  have dual := burnolRemainderRealization_fourier tau (burnolUnitTailResponse coordinate 4)
    (burnolOriginalUnitTail_realizes coordinate) test
  have replay : burnolRemainderSourceRead (burnolMobiusSourceL2 state) test =
      (Lp.toTemperedDistributionCLM ℂ volume 2 (state : BurnolL2)) test := by
    simpa only [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply, smul_eq_mul]
      using burnolRemainderSourceRead_Pa state belongs test
  rw [← burnolRemainderSourceReadCLM_apply, map_sub, map_add,
    burnolRemainderSourceReadCLM_apply, burnolRemainderSourceReadCLM_apply,
    burnolRemainderSourceReadCLM_apply, original, dual, replay]
  have whole : (state : BurnolL2) = burnolUnitTailResponse coordinate 4 +
      fourierL2 (burnolUnitTailResponse coordinate 4) := rfl
  change (Lp.toTemperedDistributionCLM ℂ volume 2 (burnolUnitTailResponse coordinate 4)) test +
      (Lp.toTemperedDistributionCLM ℂ volume 2 (fourierL2 (burnolUnitTailResponse coordinate 4))) test -
        (Lp.toTemperedDistributionCLM ℂ volume 2 (state : BurnolL2)) test = 0
  rw [whole, map_add, add_apply, sub_self]

def burnolZeroOwnedUnitFourierPaState {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaOrthogonalCarrier :=
  burnolPaOrthogonalClosedFace.toSubmodule.orthogonalProjectionOnto
    (burnolZeroOwnedUnitFourierState observation nontrivial rightHalf)

theorem burnolZeroOwnedUnitFourierPaState_nonzero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf ≠ 0 := by
  intro zero
  apply burnolZeroOwnedUnitFourierState_notInPa observation nontrivial rightHalf
  have projected := congrArg (fun value : BurnolPaOrthogonalCarrier => (value : BurnolPaAmbientCarrier)) zero
  have orthogonal := (Submodule.starProjection_apply_eq_zero_iff _).mp projected
  change burnolZeroOwnedUnitFourierState observation nontrivial rightHalf ∈
    (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ)ᗮ at orthogonal
  rw [Submodule.orthogonal_orthogonal] at orthogonal
  exact orthogonal

theorem burnolZeroOwnedUnitFourierPaState_fixed {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    evenFaceFourierEquiv burnolUnscaledCommonGapRadius
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) =
        (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  have same := burnolCompactCoPoissonActionSquare.orthogonalAction_residual
    (burnolZeroOwnedUnitFourierState observation nontrivial rightHalf)
  have read := congrArg (fun value : SourceGeneratedHilbertCokernel.OrthogonalResidual
    burnolCompactCoPoissonLanding => (value : BurnolPaAmbientCarrier)) same
  change evenFaceFourierEquiv burnolUnscaledCommonGapRadius
    (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) =
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
        (evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolZeroOwnedUnitFourierState observation nontrivial rightHalf)) at read
  rw [burnolZeroOwnedUnitFourierState_fixed] at read
  exact read

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
