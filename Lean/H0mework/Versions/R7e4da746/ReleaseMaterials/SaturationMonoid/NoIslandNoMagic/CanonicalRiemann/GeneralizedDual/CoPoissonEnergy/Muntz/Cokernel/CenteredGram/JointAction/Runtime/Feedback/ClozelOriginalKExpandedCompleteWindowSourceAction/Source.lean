import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance windowComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
open OriginalKWholePaSourceRankAction OriginalKQBSourceWindowAction
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def actualUnitTailWindowProgramme (t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  burnolRadiusRestriction (radius t) (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2) -
    paSourceWindowProgramme (actualUnitTailPaSource observation nontrivial half) t

def actualUnitPairWindowProgramme (t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  burnolRadiusRestriction (radius t) (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf : BurnolL2) -
    paSourceWindowProgramme (actualUnitFourierPaSource observation nontrivial half) t

def actualUnitSiblingWindowProgramme (t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  (2:ℂ) • actualUnitTailWindowProgramme observation nontrivial half t - actualUnitPairWindowProgramme observation nontrivial half t

def actualNonPaPairWindowProgramme (h t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  burnolRadiusRestriction (radius t) (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2) -
    paSourceWindowProgramme (actualFullPairPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) • actualUnitPairWindowProgramme observation nontrivial half t

def actualNonPaSiblingWindowProgramme (h t : ℝ) : BurnolRadiusIntervalL2 (radius t) :=
  burnolRadiusRestriction (radius t) (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2) -
    paSourceWindowProgramme (actualFullSiblingPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) • actualUnitSiblingWindowProgramme observation nontrivial half t

private theorem physical_source_Pa_split (value : BurnolPaAmbientCarrier) :
    (value : BurnolL2) = (E (value : BurnolL2) : BurnolL2) + (OP value : BurnolPaAmbientCarrier) := by
  have projected : P (value : BurnolL2) = value := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  have paid := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal value
  change (value : BurnolL2) =
    ((burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (P (value : BurnolL2)) : BurnolPaAmbientCarrier) : BurnolL2) +
      (OP value : BurnolPaAmbientCarrier)
  rw [projected]
  exact (congrArg (fun field : BurnolPaAmbientCarrier => (field : BurnolL2)) paid).symm

/-- The actual unit fields retain their full recovered Pa windows; no original unit or constant pole is erased. -/
theorem actual_unit_window_programmes (t : ℝ) :
    burnolRadiusRestriction (radius t) (actualOriginalUnitPaTail observation nontrivial half : BurnolL2) =
      actualUnitTailWindowProgramme observation nontrivial half t ∧
    burnolRadiusRestriction (radius t) (actualOriginalUnitPaPair observation nontrivial half : BurnolL2) =
      actualUnitPairWindowProgramme observation nontrivial half t ∧
    burnolRadiusRestriction (radius t) (actualOriginalUnitPaSibling observation nontrivial half : BurnolL2) =
      actualUnitSiblingWindowProgramme observation nontrivial half t := by
  have tail := congrArg (burnolRadiusRestriction (radius t))
    (physical_source_Pa_split (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf))
  have pair := congrArg (burnolRadiusRestriction (radius t))
    (physical_source_Pa_split (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf))
  simp only [map_add] at tail pair
  have tailPa := burnolSourceOnlyCoPoissonWindow_replay (radius t)
    (E (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2)) (Submodule.starProjection_apply_mem _ _)
  have pairPa := burnolSourceOnlyCoPoissonWindow_replay (radius t)
    (E (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf : BurnolL2)) (Submodule.starProjection_apply_mem _ _)
  have tailRead : burnolRadiusRestriction (radius t) (actualOriginalUnitPaTail observation nontrivial half : BurnolL2) =
      actualUnitTailWindowProgramme observation nontrivial half t := by
    unfold actualUnitTailWindowProgramme paSourceWindowProgramme actualUnitTailPaSource
    rw [tailPa]
    exact eq_sub_of_add_eq' tail.symm
  have pairRead : burnolRadiusRestriction (radius t) (actualOriginalUnitPaPair observation nontrivial half : BurnolL2) =
      actualUnitPairWindowProgramme observation nontrivial half t := by
    unfold actualUnitPairWindowProgramme paSourceWindowProgramme actualUnitFourierPaSource
    rw [pairPa]
    exact eq_sub_of_add_eq' pair.symm
  refine ⟨tailRead,pairRead,?_⟩
  change burnolRadiusRestriction (radius t) ((2:ℂ) • (actualOriginalUnitPaTail observation nontrivial half : BurnolL2) -
    (actualOriginalUnitPaPair observation nontrivial half : BurnolL2)) = _
  rw [map_sub,map_smul,tailRead,pairRead]
  rfl

/-- Complete source windows are restored before any scalar mean or weighted cotest projection. -/
theorem actual_nonPa_complete_window_programmes (h t : ℝ) :
    burnolRadiusRestriction (radius t) (Q (actualNonPaPairedR observation nontrivial half h) : BurnolL2) =
      actualNonPaPairWindowProgramme observation nontrivial half h t ∧
    burnolRadiusRestriction (radius t) (Q (actualNonPaSiblingR observation nontrivial half h) : BurnolL2) =
      actualNonPaSiblingWindowProgramme observation nontrivial half h t := by
  have source := actual_nonPa_Q_source_split observation nontrivial half h
  have unit := actual_unit_window_programmes observation nontrivial half t
  have pairPa := burnolSourceOnlyCoPoissonWindow_replay (radius t)
    (E (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) (Submodule.starProjection_apply_mem _ _)
  have siblingPa := burnolSourceOnlyCoPoissonWindow_replay (radius t)
    (E (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) (Submodule.starProjection_apply_mem _ _)
  constructor
  · rw [source.1]
    simp only [Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul]
    unfold actualNonPaPairWindowProgramme paSourceWindowProgramme actualFullPairPaSource
    rw [pairPa,unit.2.1]
  · rw [source.2]
    simp only [Submodule.coe_sub,Submodule.coe_smul,map_sub,map_smul]
    unfold actualNonPaSiblingWindowProgramme paSourceWindowProgramme actualFullSiblingPaSource
    rw [siblingPa,unit.2.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKExpandedCompleteWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
