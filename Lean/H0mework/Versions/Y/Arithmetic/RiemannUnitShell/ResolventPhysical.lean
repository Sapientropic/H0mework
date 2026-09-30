import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.Difference
import H0mework.Versions.Y.Arithmetic.RiemannFirstSource.CutoffPhysical
import H0mework.Versions.Y.Arithmetic.RiemannMellinOrbit.ZeroPositiveMellinTateOrbit

/-! The same zero and its generated conjugate supply a physical strong-domain difference whose Pa read is the original pair of classes. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem burnolZeroOwnedUnitResponse_one_physical {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1 ∈
      evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have shell := burnolUnitTailResponse_shell coordinate 1 (by norm_num) (by norm_num)
  obtain ⟨wave, _, waveRead⟩ := Submodule.mem_map.mp
    (burnolUnitPowerShellWave_originalPa coordinate 1 (by norm_num) (by norm_num))
  rw [sub_eq_iff_eq_add.mp shell, ← waveRead]
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).add_mem wave.2
    (burnolZeroOwnedUnitTailResponse_physical observation nontrivial rightHalf)

theorem burnolZeroOwnedUnitResponse_one_class {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let point : BurnolPaAmbientCarrier := ⟨burnolUnitTailResponse
      (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1,
        burnolZeroOwnedUnitResponse_one_physical observation nontrivial rightHalf⟩
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection point =
      burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
        (burnolZeroOwnedUnitTailState observation nontrivial rightHalf) := by
  dsimp only
  let point : BurnolPaAmbientCarrier := ⟨burnolUnitTailResponse
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1,
      burnolZeroOwnedUnitResponse_one_physical observation nontrivial rightHalf⟩
  let reference := burnolZeroOwnedUnitTailState observation nontrivial rightHalf
  let coordinate := burnolDivisionZeroCompletedMellinCoordinate observation rightHalf
  have shell := burnolUnitTailResponse_shell coordinate 1 (by norm_num) (by norm_num)
  obtain ⟨wave, waveIn, waveRead⟩ := Submodule.mem_map.mp
    (burnolUnitPowerShellWave_originalPa coordinate 1 (by norm_num) (by norm_num))
  have same : point - reference = wave := by
    apply Subtype.ext
    change burnolUnitTailResponse coordinate 1 - burnolUnitTailResponse coordinate 4 = (wave : BurnolL2)
    exact shell.trans waveRead.symm
  apply sub_eq_zero.mp
  rw [← map_sub, same]
  apply (Submodule.starProjection_apply_eq_zero_iff _).mpr
  simpa only [Submodule.orthogonal_orthogonal] using waveIn

def burnolZeroOwnedUnitOneState {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  ⟨burnolUnitTailResponse (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf) 1,
    burnolZeroOwnedUnitResponse_one_physical observation nontrivial rightHalf⟩

def burnolZeroOwnedUnitConjugateState {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  burnolZeroOwnedUnitOneState (conjugateZeroObservation observation)
    (observation.conjugate_nontrivial nontrivial) rightHalf

/-- Two dependent faces of the same zero occurrence, represented in the original physical carrier. -/
def burnolZeroOwnedUnitConjugateDifference {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) : BurnolPaAmbientCarrier :=
  burnolZeroOwnedUnitOneState observation nontrivial rightHalf -
    burnolZeroOwnedUnitConjugateState observation nontrivial rightHalf

/-- The same-source difference generates a strong physical graph pair before Pa projection. -/
theorem burnolZeroOwnedUnitConjugateDifference_hasDerivAt {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation (-h / 2)
      (burnolZeroOwnedUnitConjugateDifference observation nontrivial rightHalf : BurnolL2))
      (((observation.coordinate / 2 - 1 / 4) •
          burnolZeroOwnedUnitOneState observation nontrivial rightHalf -
        ((starRingEnd ℂ observation.coordinate) / 2 - 1 / 4) •
          burnolZeroOwnedUnitConjugateState observation nontrivial rightHalf : BurnolPaAmbientCarrier) : BurnolL2) 0 := by
  exact burnolUnitTailResponse_difference_hasDerivAt
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
    (burnolDivisionZeroCompletedMellinCoordinate (conjugateZeroObservation observation) rightHalf)

/-- The graph point reads the original selected/conjugate Pa classes, including their actual subtraction. -/
theorem burnolZeroOwnedUnitConjugateDifference_class {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
      (burnolZeroOwnedUnitConjugateDifference observation nontrivial rightHalf) =
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolAnalyticComplementFirstPhysicalState observation nontrivial rightHalf) -
        burnolCompactCoPoissonClosedRange.toSubmoduleᗮ.starProjection
          (burnolAnalyticComplementFirstPhysicalState (conjugateZeroObservation observation)
            (observation.conjugate_nontrivial nontrivial) rightHalf) := by
  unfold burnolZeroOwnedUnitConjugateDifference burnolZeroOwnedUnitConjugateState
  rw [map_sub]
  apply congrArg₂ (fun left right : BurnolPaAmbientCarrier => left - right)
  · exact (burnolZeroOwnedUnitResponse_one_class observation nontrivial rightHalf).trans
      (burnolAnalyticComplementFirstPaResidual_eq_unitResponse_projection observation nontrivial rightHalf).symm
  · exact (burnolZeroOwnedUnitResponse_one_class (conjugateZeroObservation observation)
      (observation.conjugate_nontrivial nontrivial) rightHalf).trans
        (burnolAnalyticComplementFirstPaResidual_eq_unitResponse_projection (conjugateZeroObservation observation)
          (observation.conjugate_nontrivial nontrivial) rightHalf).symm

theorem burnolZeroOwnedUnitConjugateDifference_ne_zero {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re)
    (distinct : observation.coordinate ≠ starRingEnd ℂ observation.coordinate) :
    burnolZeroOwnedUnitConjugateDifference observation nontrivial rightHalf ≠ 0 := by
  intro zero
  have raw := congrArg (fun state : BurnolPaAmbientCarrier => (state : BurnolL2)) zero
  exact burnolUnitTailResponse_difference_ne_zero
    (burnolDivisionZeroCompletedMellinCoordinate observation rightHalf)
    (burnolDivisionZeroCompletedMellinCoordinate (conjugateZeroObservation observation) rightHalf) distinct raw

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
