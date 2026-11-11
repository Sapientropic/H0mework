import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.ProjectedSource.Weyl.Head
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.Generator.Resolvent.Gram

/-! The free real probe 3/4 reads the original head source polynomial as an actual Z resolvent norm. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

local instance : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The free real probe reads the source polynomial through the norm of the same original Z. -/
theorem burnolPaHeadWeylSource_three_quarter {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
    (rightHalf : 1 / 2 < observation.coordinate.re) :
    let probe : BurnolCompletedMellinCoordinate := ⟨(3 / 4 : ℂ), by norm_num, by norm_num⟩
    let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
    burnolPaHeadWeylSource observation nontrivial rightHalf probe =
      burnolPaCombResponseCoefficient observation.coordinate 0 *
        ((1 / 2 : ℂ) * (‖Z‖ : ℂ) ^ 2 -
          ((3 / 4 : ℂ) - observation.coordinate) * (observation.coordinate - 1 / 4) / 8 *
            (‖burnolDirectRightResolvent (3 / 8) (Z : BurnolL2)‖ : ℂ) ^ 2) := by
  let probe : BurnolCompletedMellinCoordinate := ⟨(3 / 4 : ℂ), by norm_num, by norm_num⟩
  let Z := burnolZeroOwnedUnitFourierPaState observation nontrivial rightHalf
  have fixed : fourierL2 (Z : BurnolL2) = Z :=
    congrArg Subtype.val (burnolZeroOwnedUnitFourierPaState_fixed observation nontrivial rightHalf)
  have normRead := burnolDirectRightResolvent_realDiagonal (3 / 8) (by norm_num) (Z : BurnolL2) fixed
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at normRead
  have source := burnolPaHeadWeylSource_gram observation nontrivial rightHalf probe
  change burnolPaHeadWeylSource observation nontrivial rightHalf probe =
    burnolPaCombResponseCoefficient observation.coordinate 0 *
      (((3 / 4 : ℂ) - observation.coordinate) * (3 / 4 + observation.coordinate - 1) *
        inner ℂ (Z : BurnolL2) (burnolDirectRightResolvent ((3 / 4 : ℂ) / 2) (Z : BurnolL2)) +
        (2 * (3 / 4 : ℂ) - 1) * (‖Z‖ : ℂ) ^ 2) at source
  rw [show ((3 / 4 : ℂ) / 2) = 3 / 8 by norm_num, normRead] at source
  change burnolPaHeadWeylSource observation nontrivial rightHalf probe = _
  rw [source]
  ring

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
