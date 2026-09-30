import H0mework.Versions.Y.Arithmetic.RiemannBandResponse.ActionProjection

/-! The original nonzero Pa-orthogonal state has an actual paired action driven by its original first-response coupling. -/

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter FourierTransform
open scoped InnerProductSpace Topology
noncomputable section
local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The coupling of the original Pa projection of the actual first response; no datum is supplied. -/
def burnolNativePaHeadCoupling {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (shift : ℝ) : BurnolPaOrthogonalCarrier :=
  (burnolPaCombResponseCoefficient observation.coordinate 0)⁻¹ •
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.orthogonalProjectionOnto
      (burnolPairedAmbientCompression shift
        (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
          (burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0)))

/-- The original physical action retains its exact source-generated coupling. -/
theorem burnolZeroUnitPa_spectralAction {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (small : |shift| ≤ Real.log 2) :
    burnolPaPairedDilationCompression shift
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf) =
        pairedMellinTranslationCharacter observation.coordinate shift •
          burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf -
        burnolNativePaHeadCoupling observation nontrivial rightHalf shift := by
  apply Subtype.ext
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let whole := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
  let Q := burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
  let P := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection
  have wholeClass := burnolUnitOne_fourierClass observation nontrivial rightHalf
  change Q whole = (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) at wholeClass
  have split : (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) =
      whole - P whole := wholeClass.symm.trans
        (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_orthogonal_val whole)
  have forward := burnolPaResponseShift_bounds shift small
  have inverse := burnolPaResponseShift_bounds (-shift) (by simpa only [abs_neg] using small)
  have action := burnolUnitOne_sourcePairedAction_readsZ observation nontrivial rightHalf shift
    (by linarith) (by linarith) (by linarith) (by linarith)
  change Q (burnolPairedAmbientCompression shift whole) = _ at action
  have head := burnolUnitPaProjectedSource_head observation nontrivial rightHalf shift small
  change Q (burnolPairedAmbientCompression shift (P whole)) = _ at head
  change Q (burnolPairedAmbientCompression shift
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier)) =
    pairedMellinTranslationCharacter observation.coordinate shift •
      (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) -
        (burnolNativePaHeadCoupling observation nontrivial rightHalf shift : BurnolPaAmbientCarrier)
  calc
    _ = Q (burnolPairedAmbientCompression shift whole) -
        Q (burnolPairedAmbientCompression shift (P whole)) := by rw [split, map_sub, map_sub]
    _ = _ := by rw [action, head]; rfl
end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
