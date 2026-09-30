import H0mework.Versions.Y.Arithmetic.RiemannUnitFourier.ActionCurrent
import H0mework.Versions.Y.Arithmetic.RiemannUnitRegularity.FourierPhysical
import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.ResolventPhysical

/-! The actual unit-radius paired source action reads the same nonzero Fourier-fixed Pa class.
The action is on the full source state, before Q; it does not commute Q through dilation. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem originalQ_fourier (state : BurnolPaAmbientCarrier) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (evenFaceFourierEquiv burnolUnscaledCommonGapRadius state) =
        evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection state) := by
  have same := burnolCompactCoPoissonActionSquare.orthogonalAction_residual state
  exact (congrArg (fun value : SourceGeneratedHilbertCokernel.OrthogonalResidual
    burnolCompactCoPoissonLanding => (value : BurnolPaAmbientCarrier)) same).symm

theorem burnolUnitOne_fourierClass {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one) =
        (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  dsimp only
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitOneState observation nontrivial rightHalf +
        evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolZeroOwnedUnitOneState observation nontrivial rightHalf)) =
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitTailState observation nontrivial rightHalf +
        evenFaceFourierEquiv burnolUnscaledCommonGapRadius
          (burnolZeroOwnedUnitTailState observation nontrivial rightHalf))
  rw [map_add, map_add, originalQ_fourier, originalQ_fourier]
  have same := burnolZeroOwnedUnitResponse_one_class observation nontrivial rightHalf
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitOneState observation nontrivial rightHalf) =
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) at same
  rw [same]

theorem burnolUnitOne_sourcePairedAction_readsZ {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (shift : ℝ) (forwardLower : (1 / 4 : ℝ) < Real.exp (-shift))
    (forwardUpper : Real.exp (-shift) < 4)
    (inverseLower : (1 / 4 : ℝ) < Real.exp shift) (inverseUpper : Real.exp shift < 4) :
    let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolPairedAmbientCompression shift
        (one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one)) =
      pairedMellinTranslationCharacter observation.coordinate shift •
        (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) := by
  dsimp only
  let one := burnolZeroOwnedUnitOneState observation nontrivial rightHalf
  let state := one + evenFaceFourierEquiv burnolUnscaledCommonGapRadius one
  let character := pairedMellinTranslationCharacter observation.coordinate shift
  have generated := burnolUnitOne_pairedCurrent_memPa
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
    shift forwardLower forwardUpper inverseLower inverseUpper
  obtain ⟨current, currentIn, currentRead⟩ := Submodule.mem_map.mp generated
  have read := congrArg burnolEvenAmbientProjection currentRead
  change burnolEvenAmbientProjection (current : BurnolL2) =
    burnolEvenAmbientProjection (pairedBurnolMultiplicativeDilation shift (state : BurnolL2) -
      character • (state : BurnolL2)) at read
  simp only [map_sub, map_smul, burnolEvenAmbientProjection,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] at read
  have actionRead : (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.orthogonalProjectionOnto
      (pairedBurnolMultiplicativeDilation shift (state : BurnolL2)) =
        burnolPairedAmbientCompression shift state := by
    unfold pairedBurnolMultiplicativeDilation burnolPairedAmbientCompression
    simp only [smul_apply, add_apply, map_smul, map_add]
    rfl
  rw [actionRead] at read
  have projected := congrArg burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection read
  have killed : burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection current = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero currentIn
  rw [killed, map_sub, map_smul] at projected
  have sameClass := burnolUnitOne_fourierClass observation nontrivial rightHalf
  change burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection state =
    (burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf : BurnolPaAmbientCarrier) at sameClass
  rw [sameClass] at projected
  exact sub_eq_zero.mp projected.symm

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
