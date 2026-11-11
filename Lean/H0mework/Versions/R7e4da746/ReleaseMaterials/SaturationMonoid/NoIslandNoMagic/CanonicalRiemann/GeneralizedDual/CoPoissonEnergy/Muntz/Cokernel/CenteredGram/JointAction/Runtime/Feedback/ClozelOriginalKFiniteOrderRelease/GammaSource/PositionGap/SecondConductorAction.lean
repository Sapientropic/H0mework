import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondConductorStock
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionBranchSecondConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogHeadInverse

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock

open BurnolPhysicalState
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped InnerProductSpace

open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private gamma_graph from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogStockAction

namespace H
export OriginalKCrossParameterRAdjointSource.GammaOutsideHistory (write write_graph)
export OriginalKCrossParameterRAdjointSource.GammaOutsideHistory.Second (writeSecond write_second_graph)
end H

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "P" => OriginalKCombPhysicalAction.physicalProjection

private theorem first_outside_read (x : Base) :
    LogStock.gamma (LogStock.split x).2 = firstOutside x := by
  change LogStock.gamma (x - LogStock.physical x) = _
  rw [map_sub]
  rfl

private theorem first_outside_graph (x : Base) :
    GammaPair (O (LogStock.field x)) (firstOutside x) := by
  have graph := gamma_graph (LogStock.split x).2
  have split : P (LogStock.field x) + O (LogStock.field x) = LogStock.field x :=
    (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal _
  have outside : LogStock.field (LogStock.split x).2 = O (LogStock.field x) := by
    change LogStock.field (x - LogStock.physical x) = _
    rw [map_sub, LogStock.physical_field]
    exact sub_eq_iff_eq_add.mpr ((add_comm _ _).trans split).symm
  rwa [outside, first_outside_read] at graph

private theorem full_second_graph (x : Whole) :
    GammaPair (LogStock.gamma (base x)) (physicalSecond x + outsideSecond x) := by
  have paid := second_pairs x
  have split : firstPhysical (base x) + firstOutside (base x) = LogStock.gamma (base x) := by
    change firstPhysical (base x) + (LogStock.gamma (base x) - firstPhysical (base x)) =
      LogStock.gamma (base x)
    abel
  intro test
  rw [← split, inner_add_right, inner_add_right, paid.1 test, paid.2 test]

private def outsideWrite (c : BurnolCompletedMellinCoordinate) : Whole →L[ℂ] BurnolL2 :=
  (H.writeSecond c).comp ((LogStock.field.comp base).prod outsideSecond)

private def physicalWrite (c : BurnolCompletedMellinCoordinate) : Whole →L[ℂ] BurnolL2 :=
  (R c).comp (physicalSecond + outsideSecond) - outsideWrite c

private theorem written_graphs (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (x : Whole) :
    GammaPair (firstPhysical (LogStock.advance c (base x))) (physicalWrite c x) ∧
      GammaPair (firstOutside (LogStock.advance c (base x))) (outsideWrite c x) := by
  let y := LogStock.advance c (base x)
  have external := first_outside_graph y
  rw [show LogStock.field y = R c (LogStock.field (base x)) from LogStock.advance_field c (base x)] at external
  have first := H.write_graph c zero _ _ (first_outside_graph (base x))
  have outsideRead : firstOutside y =
      H.write c (LogStock.field (base x), firstOutside (base x)) :=
    conductor_unique _ _ _ external first
  have outside := H.write_second_graph c (LogStock.field (base x)) _ _ (second_pairs x).2
  rw [← outsideRead] at outside
  change GammaPair (firstOutside y) (outsideWrite c x) at outside
  have firstNext := gamma_graph y
  rw [show LogStock.field y = R c (LogStock.field (base x)) from LogStock.advance_field c (base x)] at firstNext
  have sameFull := conductor_unique _ _ _ firstNext (actual_Gamma_R c _ _ (gamma_graph (base x)))
  have full := actual_Gamma_R c _ _ (full_second_graph x)
  rw [← sameFull] at full
  refine ⟨?_, outside⟩
  have split : firstPhysical y = LogStock.gamma y - firstOutside y :=
    (sub_sub_cancel _ _).symm
  intro test
  change _ = inner ℂ (test.toLp 2 MeasureTheory.volume)
    (R c (physicalSecond x + outsideSecond x) - outsideWrite c x)
  rw [split, inner_sub_right, inner_sub_right, full test, outside test]

private def ambientWrite (c : BurnolCompletedMellinCoordinate) : Whole →L[ℂ] Ambient :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ Base SecondSlots).symm.toContinuousLinearMap.comp
    (((LogStock.advance c).comp base).prod
      ((WithLp.prodContinuousLinearEquiv 2 ℂ BurnolL2 BurnolL2).symm.toContinuousLinearMap.comp
        ((physicalWrite c).prod (outsideWrite c))))

/-- The same original R and outside writer act boundedly on the closed second conductor stock. -/
def advance (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) : Whole →L[ℂ] Whole :=
  (ambientWrite c).codRestrict carrier fun x =>
    (ofFields (LogStock.advance c (base x)) (physicalWrite c x) (outsideWrite c x)
      (written_graphs c zero x).1 (written_graphs c zero x).2).property

theorem advance_second_fields (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    (x : Whole) :
    let out := H.writeSecond c (LogStock.field (base x), outsideSecond x);
    (physicalSecond (advance c zero x), outsideSecond (advance c zero x)) =
      (R c (physicalSecond x + outsideSecond x) - out, out) := rfl

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "logs" => LogStock.actualAt observation nontrivial half depth
local notation "first" => DivisionConductor.branchGammaAt observation nontrivial half depth
local notation "second" => DivisionConductor.branchSecondAt observation nontrivial half depth

/-- The exact graph fields already generated by the literal occurrence initialize the closed stock. -/
def actualAt (ordinal : Nat) : Whole := by
  have matched := (LogStock.actual_graph_slots observation nontrivial half depth ordinal).2
  have p : firstPhysical (logs ordinal) = (first ordinal).1 := congrArg Prod.fst matched
  have o := congrArg Prod.snd matched
  change LogStock.gamma (LogStock.split (logs ordinal)).2 = (first ordinal).2 at o
  rw [first_outside_read] at o
  have graphs := DivisionConductor.actual_division_branch_second_conductor observation nontrivial half depth ordinal
  rw [← p, ← o] at graphs
  exact ofFields (logs ordinal) (second ordinal).1 (second ordinal).2 graphs.1 graphs.2

theorem actual_second_fields (ordinal : Nat) :
    (physicalSecond (actualAt observation nontrivial half depth ordinal),
      outsideSecond (actualAt observation nontrivial half depth ordinal)) = second ordinal := by
  exact Prod.ext rfl rfl

theorem actual_second_graph_next (ordinal : Nat) :
    advance c observation.mathlibZero (actualAt observation nontrivial half depth ordinal) =
      actualAt observation nontrivial half depth (ordinal+1) := by
  apply base_injective
  exact LogStock.actual_graph_next observation nontrivial half depth ordinal

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
