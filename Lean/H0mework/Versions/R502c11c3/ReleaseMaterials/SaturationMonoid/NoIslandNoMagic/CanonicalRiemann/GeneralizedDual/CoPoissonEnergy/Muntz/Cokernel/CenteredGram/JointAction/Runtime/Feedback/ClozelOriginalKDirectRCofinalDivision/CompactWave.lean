import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.CompactResolventWaveSource
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.OriginTraceAction

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex MeasureTheory BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open private actual_raw_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source
open private density_actual from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PositionGap


local notation "q" => (1/4 : ℝ)
local notation "r₀" => (q/2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R" => burnolDirectRightResolventCLM

private theorem original_quarter_cut_supported (value : BurnolL2) :
    originalPhysicalCutoff q (originalPhysicalCutoff q value) = originalPhysicalCutoff q value := by
  unfold originalPhysicalCutoff
  rw [burnolRadiusRestriction_zeroExtension]

private theorem original_quarter_cut_even (value : BurnolL2) (even : reflectL2 value = value) :
    reflectL2 (originalPhysicalCutoff q value) = originalPhysicalCutoff q value := by
  unfold originalPhysicalCutoff
  rw [burnolRadiusZeroExtension_reflect]
  change burnolRadiusZeroExtension q (reflectRestricted q (restrictToInterval q value)) =
    burnolRadiusZeroExtension q (restrictToInterval q value)
  rw [← restrictToInterval_reflectL2, even]

private theorem conjugate_original_resolvent (c : BurnolCompletedMellinCoordinate) :
    R (barC (barC c)) = R c := by
  apply ContinuousLinearMap.ext
  intro value
  change burnolDirectRightResolvent (star (star c.value)/2) value =
    burnolDirectRightResolvent (c.value/2) value
  rw [star_star]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c₀" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "old" => D.raw observation nontrivial half depth ordinal
local notation "born" => DirectRDivisionControls.bornRead observation nontrivial half depth ordinal

def actualDivisionQuarterSource : BurnolL2 :=
  positionGapCentreDensity (splitAtPhysicalCutoff r₀ old).1 • ConstantDual.seed

theorem actual_division_quarter_source_value :
    actualDivisionQuarterSource observation nontrivial half depth ordinal = originalPhysicalCutoff q old := by
  have gap := OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal
  obtain ⟨a, given⟩ := mem_locallyConstantFace_iff_exists.mp gap
  have position : burnolQuarterRestriction old = a • intervalConstant q := given.symm
  unfold actualDivisionQuarterSource
  rw [density_actual old a position]
  change a • burnolQuarterZeroExtension (intervalConstant q) =
    burnolQuarterZeroExtension (burnolQuarterRestriction old)
  rw [position, map_smul]

local notation "centre" => actualDivisionQuarterSource observation nontrivial half depth ordinal

/-- Execute the exterior R action and compute the compact wave from the actual position gap. -/
def actualDivisionCompactWave : BurnolL2 :=
  fourierL2 (R c₀ (old-centre))+compactResolventHilbertWave (barC c₀) centre
    (by
      rw [actual_division_quarter_source_value]
      exact original_quarter_cut_supported old)
    (by
      rw [actual_division_quarter_source_value]
      exact original_quarter_cut_even old (actual_raw_even observation nontrivial half depth ordinal))

theorem actual_division_compact_wave_value :
    actualDivisionCompactWave observation nontrivial half depth ordinal = fourierL2 born := by
  have source : born = P.R observation nontrivial half old :=
    (Parent.Full.complete_of_branches observation nontrivial half _ _
      (OriginalKDirectRCofinalMaterial.actual_successor_branches observation nontrivial half depth ordinal)).2.2.1
  rw [OriginalKCombCofinalRAction.original_R_direct] at source
  change born = R c₀ old at source
  unfold actualDivisionCompactWave
  rw [actual_compact_resolvent_hilbert_wave_value]
  change fourierL2 (R c₀ (old-centre))+fourierL2 (R (barC (barC c₀)) centre) = _
  rw [conjugate_original_resolvent, ← map_add fourierL2, ← map_add (R c₀), sub_add_cancel, ← source]

/-- Invert the computed full wave and write the original two inventory slots. -/
theorem actual_division_compact_wave_writeback :
    let returned := fourierL2.symm (actualDivisionCompactWave observation nontrivial half depth ordinal)
    originalPhysicalCutoff q old =
        positionGapCentreDensity (splitAtPhysicalCutoff r₀ old).1 • ConstantDual.seed ∧
      returned = born ∧
      ((burnolEvenAmbientProjection returned : BurnolL2),
        returned-(burnolEvenAmbientProjection returned : BurnolL2)) =
          OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1) := by
  have result : fourierL2.symm (actualDivisionCompactWave observation nontrivial half depth ordinal) = born := by
    rw [actual_division_compact_wave_value, fourierL2.symm_apply_apply]
  have original := actual_division_position_gap_mixed_next observation nontrivial half depth ordinal
  have slots := original.2.2.2.2.1
  rw [original.1, original_physical_projection_from_split r₀ (by norm_num)] at slots
  refine ⟨(actual_division_quarter_source_value observation nontrivial half depth ordinal).symm, result, ?_⟩
  rw [result]
  exact slots

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
