import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullAdjointSource.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalCalculatedSource.Projection

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
open Complex MeasureTheory Set
open BurnolPhysicalState BurnolPhysicalState.OriginalRieszSource
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKForcingGapAction
open OriginalKDirectRCofinalMaterial
open SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local instance actionGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
local instance actionPhysicalComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

/-- The full invisible field retains both its physical Q source and its actual outside-P material. -/
theorem full_invisible_source_inventory (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) :
    inner ℂ (burnolCompletedMellinRieszVector coordinate : BurnolL2)
      (burnolDirectRightResolvent (coordinate.value/2) (OriginalKCombCofinalPaAction.invisible value)) =
    inner ℂ (sourceAdjointField coordinate) (OriginalKCombCofinalPaAction.Q value : BurnolL2)+
    inner ℂ (sourceAdjointField coordinate) (value-(burnolEvenAmbientProjection value : BurnolL2)) := by
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection value)
  have inventory := congrArg (fun field : BurnolPaAmbientCarrier => (field : BurnolL2)) split
  change (OriginalKCombCofinalPaAction.E value : BurnolL2)+
    (OriginalKCombCofinalPaAction.Q value : BurnolL2) = (burnolEvenAmbientProjection value : BurnolL2) at inventory
  have actual : OriginalKCombCofinalPaAction.invisible value =
      (OriginalKCombCofinalPaAction.Q value : BurnolL2)+
      (value-(burnolEvenAmbientProjection value : BurnolL2)) := by
    unfold OriginalKCombCofinalPaAction.invisible
    linear_combination (norm := module) -inventory
  rw [original_R_full_input,actual,inner_add_right]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "H" => sourceAdjointField c

/-- This reads both original normal rows and all four target slots from the calculated full-R value. -/
theorem calculated_full_R_source_reads :
    let packet := D.packet observation nontrivial half depth ordinal
    let result := CF.collapseValue packet.1
      (OriginalKDirectRCofinalCalculatedSource.calculatedValue observation nontrivial half depth ordinal)
    inner ℂ K (result.1.1+result.1.2) = inner ℂ H (D.input observation nontrivial half depth ordinal).1 ∧
    inner ℂ K (result.2.1+result.2.2) = inner ℂ H (D.input observation nontrivial half depth ordinal).2 ∧
    inner ℂ K ((result.1.1+result.1.2)+(result.2.1+result.2.2)) =
      inner ℂ H (D.raw observation nontrivial half depth ordinal) := by
  have actual := OriginalKDirectRCofinalCalculatedSource.calculated_full_R_action observation nontrivial half depth ordinal
  refine ⟨?_,?_,?_⟩
  · rw [actual.1,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _
  · rw [actual.2.1,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _
  · rw [actual.2.2,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _

/-- The normal's true sourcePayload input is used directly, before transport to the macro next axis. -/
theorem calculated_source_input_action :
    inner ℂ K (OriginalKDirectRCofinalCalculatedSource.calculatedTargetRaw observation nontrivial half depth ordinal) =
      inner ℂ H (OriginalKDirectRCofinalCalculatedSource.calculatedInputRaw observation nontrivial half depth ordinal) := by
  rw [OriginalKDirectRCofinalCalculatedSource.calculated_input_raw]
  exact (calculated_full_R_source_reads observation nontrivial half depth ordinal).2.2

/-- The macro raw successor is read from the calculated target, not identified with the inner normal tick. -/
theorem actual_raw_source_successor :
    inner ℂ K (D.raw observation nontrivial half depth (ordinal+1)) =
      inner ℂ H (D.raw observation nontrivial half depth ordinal) := by
  rw [←OriginalKDirectRCofinalCalculatedSource.calculated_target_raw observation nontrivial half depth ordinal]
  exact (calculated_full_R_source_reads observation nontrivial half depth ordinal).2.2

/-- The native born environment is consumed through its paid four-branch receipt, not a same-value occurrence assertion. -/
theorem actual_born_four_branch_source_read :
    let successor := D.packet observation nontrivial half depth (ordinal+1)
    let result := CF.collapseValue successor.1 (successor.2.1.1.activeEnvironment () (),0)
    inner ℂ K (result.1.1+result.1.2) = inner ℂ H (D.input observation nontrivial half depth ordinal).1 ∧
    inner ℂ K (result.2.1+result.2.2) = inner ℂ H (D.input observation nontrivial half depth ordinal).2 ∧
    inner ℂ K ((result.1.1+result.1.2)+(result.2.1+result.2.2)) =
      inner ℂ H (D.raw observation nontrivial half depth ordinal) := by
  have paid := Full.complete_of_branches observation nontrivial half _ _
    (actual_successor_branches observation nontrivial half depth ordinal)
  refine ⟨?_,?_,?_⟩
  · rw [paid.1,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _
  · rw [paid.2.1,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _
  · rw [paid.2.2.1,OriginalKCombCofinalRAction.original_R_direct]
    exact original_R_full_input c _

/-- The actual current's complete invisible input is calculated by H, with no outside-P deletion. -/
theorem actual_invisible_source_read :
    inner ℂ K (P.R observation nontrivial half
      (OriginalKCombCofinalPaAction.invisible (D.raw observation nontrivial half depth ordinal))) =
    inner ℂ H (OriginalKCombCofinalPaAction.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2)+
    inner ℂ H (D.raw observation nontrivial half depth ordinal-
      (burnolEvenAmbientProjection (D.raw observation nontrivial half depth ordinal) : BurnolL2)) := by
  rw [OriginalKCombCofinalRAction.original_R_direct]
  exact full_invisible_source_inventory c _

/-- The complete source inventory directly determines the actual next K read. -/
theorem actual_raw_source_inventory :
    inner ℂ K (D.raw observation nontrivial half depth (ordinal+1)) =
    inner ℂ H (OriginalKCombCofinalPaAction.E (D.raw observation nontrivial half depth ordinal) : BurnolL2)+
    inner ℂ H (OriginalKCombCofinalPaAction.Q (D.raw observation nontrivial half depth ordinal) : BurnolL2)+
    inner ℂ H (D.raw observation nontrivial half depth ordinal-
      (burnolEvenAmbientProjection (D.raw observation nontrivial half depth ordinal) : BurnolL2)) := by
  have actual := actual_raw_source_successor observation nontrivial half depth ordinal
  have invisible := actual_invisible_source_read observation nontrivial half depth ordinal
  rw [OriginalKCombCofinalRAction.original_R_direct] at invisible
  change inner ℂ K (burnolDirectRightResolvent ((c).value/2)
    (OriginalKCombCofinalPaAction.invisible (D.raw observation nontrivial half depth ordinal))) = _ at invisible
  rw [original_R_full_input c] at invisible
  have split : D.raw observation nontrivial half depth ordinal =
      (OriginalKCombCofinalPaAction.E (D.raw observation nontrivial half depth ordinal) : BurnolL2)+
      OriginalKCombCofinalPaAction.invisible (D.raw observation nontrivial half depth ordinal) := by
    unfold OriginalKCombCofinalPaAction.invisible
    module
  calc
    _ = inner ℂ H (D.raw observation nontrivial half depth ordinal) := actual
    _ = inner ℂ H (OriginalKCombCofinalPaAction.E (D.raw observation nontrivial half depth ordinal) : BurnolL2)+
        inner ℂ H (OriginalKCombCofinalPaAction.invisible (D.raw observation nontrivial half depth ordinal)) := by
      nth_rw 1 [split]
      rw [inner_add_right]
    _ = _ := by rw [invisible];ring

/-- The CP290 projected source input is read by the same complete H, at its actual original coordinate. -/
theorem actual_physicalGapZeroPart_source_read :
    inner ℂ K (burnolDirectRightResolvent ((c).value/2)
      (OriginalKSourcePhysicalProjection.physicalGapZeroPart c : BurnolL2)) =
      inner ℂ H K - (∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i)*
        inner ℂ H OriginalKSourcePhysicalProjection.constantPhysicalVector := by
  rw [original_R_full_input,OriginalKSourcePhysicalProjection.physicalGapZeroPart_source]
  change inner ℂ H (K-(∑ i : Fin 2,sourceCoefficients c i*sourcePositionCoefficients c i) •
    OriginalKSourcePhysicalProjection.constantPhysicalVector) = _
  rw [inner_sub_right,inner_smul_right]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullAdjointSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
