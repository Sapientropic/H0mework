import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin.Unit.Collar.NormalizedFibre.HomogeneousFibre
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKDirectRCofinalDivision

open Complex MeasureTheory BurnolPhysicalState
open OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
open OriginalKSourceResolventReconstruction

open private actual_raw_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

local notation "L¹" => Lp ℂ 1 (volume : Measure ℝ)
local notation "S'" => TemperedDistribution ℝ ℂ
local notation "r₀" => ((1/4 : ℝ)/2)
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

/-- The literal cofinal R action generates the complete mixed solution and
writes both original inventory slots. Its weak Euler observation and the
physical slot determine that solution at the very same source ordinal. -/
theorem actual_division_weak_euler_fibre
    (observation : GeneratedRiemannZeroObservation)
    (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
    (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) :
    let c := barC (burnolDivisionZeroCompletedMellinCoordinate observation half.down)
    let x := D.raw observation nontrivial half depth ordinal
    let y := D.raw observation nontrivial half depth (ordinal+1)
    let written := OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1)
    let split := splitAtPhysicalCutoff r₀ y
    IsEvenPhysicalSplit split ∧ y ∈ locallyConstantFace burnolUnscaledCommonGapRadius ∧
      eulerOfPhysicalSplit c split = -(2 : ℂ) • (x : S') ∧
      ((physicalProjectionFromCentre split : BurnolL2), y-(physicalProjectionFromCentre split : BurnolL2)) = written ∧
      ∀ other : L¹ × BurnolL2, IsEvenPhysicalSplit other →
        eulerOfPhysicalSplit c other = -(2 : ℂ) • (x : S') →
        (physicalProjectionFromCentre other : BurnolL2) = written.1 → other = split := by
  dsimp only
  let original := burnolDivisionZeroCompletedMellinCoordinate observation half.down
  let c := barC original
  let x := D.raw observation nontrivial half depth ordinal
  let y := D.raw observation nontrivial half depth (ordinal+1)
  let written := OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1)
  let split := splitAtPhysicalCutoff r₀ y
  have successor := D.raw_successor observation nontrivial half depth ordinal
  have action : sourceResolvent c x = y := by
    calc
      _ = P.R observation nontrivial half x := by
        rw [OriginalKCombCofinalRAction.original_R_direct]
        change burnolDirectRightResolvent (star (star original.value)/2) x = _
        rw [star_star]
        rfl
      _ = _ := successor.symm
  have supported : IsEvenPhysicalSplit split := actual_even_physical_split y
    (actual_raw_even observation nontrivial half depth (ordinal+1))
  have equation : eulerOfPhysicalSplit c split = -(2 : ℂ) • (x : S') := by
    exact (congrArg (fun value => eulerOfPhysicalSplit c (splitAtPhysicalCutoff r₀ value)) action.symm).trans
      (actual_split_R_equation c x)
  have physical : (physicalProjectionFromCentre split : BurnolL2) = written.1 := by
    have read := congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2))
      (original_physical_projection_from_split r₀ (by norm_num) y)
    have born := congrArg Prod.fst (OriginalKCombFirstFullSourceDynamics.next_pair observation nontrivial half depth ordinal)
    change written.1 = OriginalKCombPhysicalAction.physicalProjection (P.R observation nontrivial half x) at born
    rw [← successor] at born
    exact read.trans born.symm
  have gap := OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth (ordinal+1)
  refine ⟨supported, gap, equation, Prod.ext physical ?_, ?_⟩
  · change y-(physicalProjectionFromCentre split : BurnolL2) = written.2
    rw [physical]
    change written.1+written.2-written.1 = written.2
    abel
  · intro other domain source first
    have zero : riemannZeta c.value = 0 := observation.conjugate_mathlibZero
    exact original_split_euler_physical_injective c zero domain supported
      (source.trans equation.symm) (Subtype.ext (first.trans physical.symm))

end OriginalKDirectRCofinalDivision
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
