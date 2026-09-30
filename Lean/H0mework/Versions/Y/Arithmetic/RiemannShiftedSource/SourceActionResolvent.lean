import H0mework.Versions.Y.Arithmetic.RiemannSourceGreen.OriginalHead

/-! Same-source contact and strong-action coordinates of the original Pa correction. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPaPhysicalGreen
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

theorem correction_source_resolvent_compact (coordinate : BurnolCompletedMellinCoordinate)
    (source : burnolCompactAnnulusSource) :
    let p : burnolCompactCoPoissonClosedRange := ⟨burnolCompactAdditivePhysicalState source, by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))⟩
    burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate p) =
      burnolDirectRightResolvent (coordinate.value / 2) (burnolMobiusSourceL2 (p : BurnolPaAmbientCarrier)) -
        burnolPaResolventSourceCoefficient coordinate (p : BurnolPaAmbientCarrier) •
          burnolNormalizedFirstSourceUnitTail coordinate := by
  dsimp only
  rw [burnolPaSourceCorrection_compact_source, burnolPaResolventSourceCoefficient_compact]
  have generated := burnolCompleteFirstSource_eq_weighted_add_tail coordinate source
  change burnolDirectRightResolvent (coordinate.value / 2)
    ((2 : ℂ) • burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) = _ at generated
  rw [burnolDirectRightResolvent_smul] at generated
  calc
    _ = (1 / 2 : ℂ) •
      ((2 : ℂ) • burnolDirectRightResolvent (coordinate.value / 2)
        (burnolMobiusSourceL2 (burnolCompactAdditivePhysicalState source)) -
        burnolFirstSourceMellinCoefficient coordinate.value source • burnolNormalizedFirstSourceUnitTail coordinate) := by
      rw [generated]
      module
    _ = _ := by module

theorem correction_source_resolvent (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inside : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate ⟨p, inside⟩) =
      burnolDirectRightResolvent (coordinate.value / 2) (burnolMobiusSourceL2 p) -
        burnolPaResolventSourceCoefficient coordinate p • burnolNormalizedFirstSourceUnitTail coordinate := by
  let project := burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto
  let left : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    burnolMobiusSourceL2.comp ((burnolPaSourceCorrection coordinate).comp project)
  let right : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    (burnolDirectRightResolventCLM coordinate).comp burnolMobiusSourceL2 -
      (burnolPaResolventSourceCoefficient coordinate).smulRight (burnolNormalizedFirstSourceUnitTail coordinate)
  have onCompact (source : burnolCompactAnnulusSource) :
      left (burnolCompactAdditivePhysicalState source) = right (burnolCompactAdditivePhysicalState source) := by
    have inPa : burnolCompactAdditivePhysicalState source ∈ burnolCompactCoPoissonClosedRange := by
      simpa only [burnolCompactCoPoissonGenerator, Fin.isValue, ↓reduceIte] using
        burnolCompactCoPoissonGenerator_mem_closedRange (source, (0 : Fin 2))
    have projected : project (burnolCompactAdditivePhysicalState source) =
        ⟨burnolCompactAdditivePhysicalState source, inPa⟩ :=
      burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self
        ⟨burnolCompactAdditivePhysicalState source, inPa⟩
    change burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate (project (burnolCompactAdditivePhysicalState source))) = _
    rw [projected]
    exact correction_source_resolvent_compact coordinate source
  have generator (i : BurnolCompactCoPoissonGeneratorIndex) :
      left (burnolCompactCoPoissonGenerator i) = right (burnolCompactCoPoissonGenerator i) := by
    rcases i with ⟨source, parity⟩
    fin_cases parity
    · exact onCompact source
    · have same : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change left (burnolCompactCoPoissonGenerator (source, (1 : Fin 2))) =
        right (burnolCompactCoPoissonGenerator (source, (1 : Fin 2)))
      rw [same]
      exact onCompact _
  have sourceRead (input : BurnolCompactCoPoissonLinearSource) :
      left (burnolCompactCoPoissonLanding input) = right (burnolCompactCoPoissonLanding input) := by
    induction input using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single i c => rw [burnolCompactCoPoissonLanding_single, map_smul, map_smul, generator]
  let equation := (left - right).ker
  have included : LinearMap.range burnolCompactCoPoissonLanding ≤ equation := by
    rintro _ ⟨input, rfl⟩
    change left (burnolCompactCoPoissonLanding input) - right (burnolCompactCoPoissonLanding input) = 0
    rw [sourceRead, sub_self]
  have closed : IsClosed (equation : Set BurnolPaAmbientCarrier) :=
    isClosed_eq (left.continuous.sub right.continuous) continuous_const
  have result := (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal included closed inside
  change left p - right p = 0 at result
  have same := sub_eq_zero.mp result
  have projected : project p = ⟨p, inside⟩ :=
    burnolCompactCoPoissonClosedRange.toSubmodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨p, inside⟩
  change burnolMobiusSourceL2 (burnolPaSourceCorrection coordinate (project p)) = _ at same
  rw [projected] at same
  exact same

end
end OriginalPaPhysicalGreen
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
