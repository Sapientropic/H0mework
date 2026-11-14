import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PositionGap
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WeakEulerFibre

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex MeasureTheory BurnolPhysicalState
open OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open private density_unit from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.PositionGap

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "r₀" => ((1/4 : ℝ)/2)
local notation "unit₁" => Prod.fst (splitAtPhysicalCutoff r₀ (FiniteMobiusResolventFlux.box r₀))
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The original position gap drives the continuous mixed update. Its Euler
read determines the whole mixed born, which writes both existing slots. -/
theorem actual_division_position_gap_mixed_next
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
    let x := D.raw observation nontrivial half depth ordinal
    let current := splitAtPhysicalCutoff r₀ x
    let mixed := positionGapMixedAction c current
    let born := DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
    mixed = splitAtPhysicalCutoff r₀ born ∧ recoverPositionGapSplit mixed = born ∧
      positionGapCentreDensity mixed.1 = -positionGapCentreDensity current.1/(c.value/2) ∧
      eulerOfPhysicalSplit (barC c) mixed = -(2 : ℂ) • (x : S') ∧
      ((physicalProjectionFromCentre mixed : BurnolL2), born-(physicalProjectionFromCentre mixed : BurnolL2)) =
        OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1) ∧
      ∀ other : L¹ × BurnolL2, IsEvenPhysicalSplit other → (∃ a : ℂ, other.1 = a • unit₁) →
        eulerOfPhysicalSplit (barC c) other = -(2 : ℂ) • (x : S') → other = mixed := by
  dsimp only
  let c := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let x := D.raw observation nontrivial half depth ordinal
  let y := D.raw observation nontrivial half depth (ordinal+1)
  let current := splitAtPhysicalCutoff r₀ x
  let mixed := positionGapMixedAction c current
  let born := DirectRDivisionControls.bornRead observation nontrivial half depth ordinal
  have rawNext := D.raw_successor observation nontrivial half depth ordinal
  have bornAction : born = P.R observation nontrivial half x :=
    (Parent.Full.complete_of_branches observation nontrivial half _ _
      (OriginalKDirectRCofinalMaterial.actual_successor_branches observation nontrivial half depth ordinal)).2.2.1
  have literalBorn : born = y := bornAction.trans rawNext.symm
  have originalAction : burnolDirectRightResolventCLM c x = y :=
    (OriginalKCombCofinalRAction.original_R_direct observation nontrivial half x).symm.trans rawNext.symm
  have gap := OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ordinal
  have fibre := actual_division_weak_euler_fibre observation nontrivial half depth ordinal
  have splitNext : mixed = splitAtPhysicalCutoff r₀ y :=
    (actual_position_gap_mixed_action c x gap).trans (congrArg (splitAtPhysicalCutoff r₀) originalAction)
  have splitBorn : mixed = splitAtPhysicalCutoff r₀ born :=
    splitNext.trans (congrArg (splitAtPhysicalCutoff r₀) literalBorn.symm)
  have recovered : recoverPositionGapSplit mixed = born :=
    (congrArg recoverPositionGapSplit splitNext).trans
      ((recover_actual_position_gap_split y fibre.2.1).trans literalBorn.symm)
  have equation : eulerOfPhysicalSplit (barC c) mixed = -(2 : ℂ) • (x : S') :=
    (congrArg (eulerOfPhysicalSplit (barC c)) splitNext).trans fibre.2.2.1
  refine ⟨splitBorn, recovered, ?_, equation, ?_, ?_⟩
  · change positionGapCentreDensity (((-(1 : ℂ)/(c.value/2))*positionGapCentreDensity current.1) • unit₁) = _
    rw [map_smul, density_unit, smul_eq_mul, mul_one]
    ring
  · change ((physicalProjectionFromCentre mixed : BurnolL2), born-(physicalProjectionFromCentre mixed : BurnolL2)) = _
    rw [splitNext, literalBorn]
    exact fibre.2.2.2.1
  · intro other domain flat source
    exact (position_gap_euler_injective (barC c) domain fibre.1 flat
      (actual_position_gap_mixed_centre y fibre.2.1) (source.trans fibre.2.2.1.symm)).trans splitNext.symm

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
