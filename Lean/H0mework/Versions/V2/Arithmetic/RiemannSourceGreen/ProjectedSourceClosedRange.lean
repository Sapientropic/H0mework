import H0mework.Versions.V2.Arithmetic.RiemannSourceGreen.ProjectedSourceCompact
import H0mework.Versions.V2.Arithmetic.RiemannFirstSource.GeneratorResolventOperator

/-! The actual source coefficient and correction extend together to the full original Pa closure. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

theorem burnolPaResolvent_source_correction (coordinate : BurnolCompletedMellinCoordinate)
    (p : BurnolPaAmbientCarrier) (inPa : p ∈ burnolCompactCoPoissonClosedRange) :
    burnolDirectRightResolvent (coordinate.value / 2) (p : BurnolL2) -
      burnolPaResolventSourceCoefficient coordinate p • burnolUnitTailResponse coordinate 4 ∈
        burnolOriginalPaInL2 := by
  let response : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    (burnolDirectRightResolventCLM coordinate).comp
      (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.subtypeL
  let tail : BurnolPaAmbientCarrier →L[ℂ] BurnolL2 :=
    (burnolPaResolventSourceCoefficient coordinate).smulRight (burnolUnitTailResponse coordinate 4)
  let correction := response - tail
  let admitted := burnolOriginalPaInL2.comap correction.toLinearMap
  have compactIn (source : burnolCompactAnnulusSource) :
      correction (burnolCompactAdditivePhysicalState source) ∈ burnolOriginalPaInL2 := by
    change burnolDirectRightResolvent (coordinate.value / 2) (burnolCompactAdditiveL2 source) -
      burnolPaResolventSourceCoefficient coordinate (burnolCompactAdditivePhysicalState source) •
        burnolUnitTailResponse coordinate 4 ∈ _
    rw [burnolPaResolventSourceCoefficient_compact]
    exact burnolCompactFirstResponse_correction coordinate source
  have generatorIn (index : BurnolCompactCoPoissonGeneratorIndex) :
      correction (burnolCompactCoPoissonGenerator index) ∈ burnolOriginalPaInL2 := by
    rcases index with ⟨source, parity⟩
    fin_cases parity
    · exact compactIn source
    · have same : burnolCompactCoPoissonGenerator (source, (1 : Fin 2)) =
          burnolCompactAdditivePhysicalState (burnolCompactTateReciprocalSource source) := by
        apply Subtype.ext
        exact burnolCompactFourierL2_eq_reciprocalL2 source
      change correction (burnolCompactCoPoissonGenerator (source, (1 : Fin 2))) ∈ _
      rw [same]
      exact compactIn (burnolCompactTateReciprocalSource source)
  have sourceIn (input : BurnolCompactCoPoissonLinearSource) :
      correction (burnolCompactCoPoissonLanding input) ∈ burnolOriginalPaInL2 := by
    induction input using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact burnolOriginalPaInL2.zero_mem
    | add a b ha hb => simpa only [map_add] using burnolOriginalPaInL2.add_mem ha hb
    | single index coefficient =>
        rw [burnolCompactCoPoissonLanding_single, map_smul]
        exact burnolOriginalPaInL2.smul_mem _ (generatorIn index)
  have rangeLe : LinearMap.range burnolCompactCoPoissonLanding ≤ admitted := by
    rintro _ ⟨input, rfl⟩
    exact sourceIn input
  exact (LinearMap.range burnolCompactCoPoissonLanding).topologicalClosure_minimal
    rangeLe (burnolOriginalPaInL2_closed.preimage correction.continuous) inPa

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
