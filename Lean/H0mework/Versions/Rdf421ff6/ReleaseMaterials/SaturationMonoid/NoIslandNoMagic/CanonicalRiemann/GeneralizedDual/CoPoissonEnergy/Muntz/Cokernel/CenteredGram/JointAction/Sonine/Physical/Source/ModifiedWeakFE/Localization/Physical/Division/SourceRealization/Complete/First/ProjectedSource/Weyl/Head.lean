import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.WeylPairing
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.OriginalHead
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Fourier

/-! The original A0/B0/p/Z relations generate a denominator-free source Weyl polynomial. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The original head source polynomial, with a probe independent of the observed zero. -/
def burnolPaHeadWeylSource {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) : ℂ :=
  let A := burnolPaCombApproximation 0
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
  let M := burnolPaResolventSourceCoefficient probe
  ((probe.value + observation.coordinate - 1) * M A -
    (probe.value - observation.coordinate) * M (evenFaceFourierEquiv burnolUnscaledCommonGapRadius A) -
    (probe.value - observation.coordinate) * (probe.value + observation.coordinate - 1) * M p) *
      inner ℂ (Z : BurnolL2) (burnolUnitTailResponse probe 4)

/-- The actual A₀/B₀/PB₀ decomposition and both resolvent actions generate the source identity. -/
theorem burnolPaHeadWeylSource_gram {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) (probe : BurnolCompletedMellinCoordinate) :
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    burnolPaHeadWeylSource observation nontrivial rightHalf probe =
    burnolPaCombResponseCoefficient observation.coordinate 0 *
      ((probe.value - observation.coordinate) * (probe.value + observation.coordinate - 1) *
        inner ℂ (Z : BurnolL2) (burnolDirectRightResolvent (probe.value / 2) (Z : BurnolL2)) +
        (2 * probe.value - 1) * (‖Z‖ : ℂ) ^ 2) := by
  let A := burnolPaCombApproximation 0
  let B := burnolPaCombPairedPhysicalResponse observation nontrivial rightHalf 0
  let p := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection B
  let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
  let F := evenFaceFourierEquiv burnolUnscaledCommonGapRadius
  let M := burnolPaResolventSourceCoefficient probe
  let D := burnolDirectRightResolventCLM probe
  let Ds := burnolDirectRightResolvent (observation.coordinate / 2)
  let read : BurnolL2 →L[ℂ] ℂ := innerSL ℂ (Z : BurnolL2)
  let lambda := burnolPaCombResponseCoefficient observation.coordinate 0
  have zr : 1 / 4 < (probe.value / 2).re := by
    rw [Complex.div_re]; norm_num; linarith [probe.rightHalf]
  have sr : 1 / 4 < (observation.coordinate / 2).re := by
    rw [Complex.div_re]; norm_num; linarith
  have hA : A ∈ burnolCompactCoPoissonClosedRange := burnolPaCombApproximation_mem 0
  have hFA : F A ∈ burnolCompactCoPoissonClosedRange :=
    burnolCompactCoPoissonActionSquare.toIsometricSquare.target_mem_closedRange hA
  have hp : p ∈ burnolCompactCoPoissonClosedRange := Submodule.starProjection_apply_mem _ _
  have Zfixed : fourierL2 (Z : BurnolL2) = Z :=
    congrArg Subtype.val (burnolZeroOwnedUnitFourierPaState_fixed observation nontrivial rightHalf)
  have readF (v : BurnolL2) : read (fourierL2 v) = read v := by
    have same := fourierL2.inner_map_map (Z : BurnolL2) v
    rw [Zfixed] at same
    exact same
  have split : (B : BurnolL2) = (p : BurnolL2) + lambda • (Z : BurnolL2) := by
    have q := burnolPaCombPairedPhysicalResponse_Q observation nontrivial rightHalf 0
    rw [Submodule.starProjection_orthogonal_val] at q
    change B - p = lambda • (Z : BurnolPaAmbientCarrier) at q
    have full : B = p + lambda • (Z : BurnolPaAmbientCarrier) := by rw [← q]; abel
    exact congrArg Subtype.val full
  have zero : read (p : BurnolL2) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp Z.property p hp
  have self : read (Z : BurnolL2) = (‖Z‖ : ℂ) ^ 2 :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (Z : BurnolL2)
  have headRead : read (Ds (A : BurnolL2)) = lambda * (‖Z‖ : ℂ) ^ 2 := by
    have b : read (B : BurnolL2) = read (Ds (A : BurnolL2)) := by
      change read ((1 / 2 : ℂ) • (Ds (A : BurnolL2) + fourierL2 (Ds (A : BurnolL2)))) = _
      rw [map_smul, map_add, readF]
      change (1 / 2 : ℂ) * (read (Ds (A : BurnolL2)) + read (Ds (A : BurnolL2))) = _
      ring
    rw [← b, split, map_add, map_smul, zero, self, zero_add]
    rfl
  have sourceA : read (D (A : BurnolL2)) = M A * read (burnolUnitTailResponse probe 4) :=
    burnolPaResolvent_source_pairing probe A hA Z
  have sourceFA : read (D (fourierL2 (A : BurnolL2))) =
      M (F A) * read (burnolUnitTailResponse probe 4) :=
    burnolPaResolvent_source_pairing probe (F A) hFA Z
  have sourceP : read (D (p : BurnolL2)) = M p * read (burnolUnitTailResponse probe 4) :=
    burnolPaResolvent_source_pairing probe p hp Z
  have same := congrArg read (burnolDirectRightResolvent_identity
    (probe.value / 2) (observation.coordinate / 2) zr sr (A : BurnolL2))
  change read (D (A : BurnolL2) - Ds (A : BurnolL2)) =
    read ((probe.value / 2 - observation.coordinate / 2) • D (Ds (A : BurnolL2))) at same
  rw [map_sub, map_smul, sourceA, headRead] at same
  have mixed := congrArg read (burnolDirectRightResolvent_fourier_mixed
    (probe.value / 2) (observation.coordinate / 2) zr sr (A : BurnolL2))
  change read ((probe.value / 2 + observation.coordinate / 2 - 1 / 2) •
      D (fourierL2 (Ds (A : BurnolL2)))) =
    read (-(D (fourierL2 (A : BurnolL2)) + fourierL2 (Ds (A : BurnolL2)))) at mixed
  rw [map_smul, map_neg, map_add, sourceFA, readF, headRead] at mixed
  have paired : read (D (B : BurnolL2)) =
      (1 / 2 : ℂ) * (read (D (Ds (A : BurnolL2))) + read (D (fourierL2 (Ds (A : BurnolL2))))) := by
    change read (D ((1 / 2 : ℂ) • (Ds (A : BurnolL2) + fourierL2 (Ds (A : BurnolL2))))) = _
    rw [map_smul, map_add, map_smul, map_add]
    rfl
  rw [split, map_add, map_smul, map_add, map_smul, sourceP] at paired
  change ((probe.value + observation.coordinate - 1) * M A -
      (probe.value - observation.coordinate) * M (F A) -
      (probe.value - observation.coordinate) * (probe.value + observation.coordinate - 1) * M p) *
      read (burnolUnitTailResponse probe 4) =
    lambda * ((probe.value - observation.coordinate) * (probe.value + observation.coordinate - 1) *
      read (D (Z : BurnolL2)) + (2 * probe.value - 1) * (‖Z‖ : ℂ) ^ 2)
  simp only [smul_eq_mul] at same mixed paired
  linear_combination (probe.value + observation.coordinate - 1) * same -
    (probe.value - observation.coordinate) * mixed -
    (probe.value - observation.coordinate) * (probe.value + observation.coordinate - 1) * paired

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
