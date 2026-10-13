import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKQBSourceWindowAction.UnitSource
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance qbProjectionComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction
def actualFullPairPaSource (h : ℝ) : BurnolL2 :=
  burnolMobiusSourceL2 (E (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h))
def actualFullSiblingPaSource (h : ℝ) : BurnolL2 :=
  burnolMobiusSourceL2 (E (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h))
def actualUnitTailPaSource : BurnolL2 :=
  burnolMobiusSourceL2 (E (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2))
def actualUnitFourierPaSource : BurnolL2 :=
  burnolMobiusSourceL2 (E (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf : BurnolL2))

def actualUnitPaTailMeanProgramme (t : ℝ) : ℂ :=
  actualUnitTailMeanProgramme observation nontrivial half t -
    paSourceMovingMean (actualUnitTailPaSource observation nontrivial half) t

def actualUnitPaPairMeanProgramme (t : ℝ) : ℂ :=
  actualUnitFourierWholeMeanProgramme observation nontrivial half t -
    paSourceMovingMean (actualUnitFourierPaSource observation nontrivial half) t

def actualUnitPaSiblingMeanProgramme (t : ℝ) : ℂ :=
  2*actualUnitPaTailMeanProgramme observation nontrivial half t -
    actualUnitPaPairMeanProgramme observation nontrivial half t

private theorem physical_Q_Pa_split (value : BurnolPaAmbientCarrier) :
    (E (value:BurnolL2) : BurnolL2) +
      (burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection value : BurnolPaAmbientCarrier) =
        (value:BurnolL2) := by
  have p : P (value:BurnolL2) = value := Submodule.orthogonalProjectionOnto_mem_subspace_eq_self value
  change ((burnolCompactCoPoissonClosedRange.toSubmodule.starProjection (P (value:BurnolL2)) : BurnolPaAmbientCarrier) : BurnolL2) + _ = _
  rw [p]
  exact congrArg (fun v : BurnolPaAmbientCarrier => (v:BurnolL2))
    (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal value)

/-- Original Pa-unit means are generated from the weighted unit source and its own recovered Pa source; the Pa projection is never erased. -/
theorem actual_unit_Pa_mean_programmes (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (actualOriginalUnitPaTail observation nontrivial half : BurnolL2)) =
      actualUnitPaTailMeanProgramme observation nontrivial half t ∧
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (actualOriginalUnitPaPair observation nontrivial half : BurnolL2)) =
      actualUnitPaPairMeanProgramme observation nontrivial half t ∧
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (actualOriginalUnitPaSibling observation nontrivial half : BurnolL2)) =
      actualUnitPaSiblingMeanProgramme observation nontrivial half t := by
  have tail := congrArg (fun value : BurnolL2 => FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t value))
    (physical_Q_Pa_split (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf))
  have pair := congrArg (fun value : BurnolL2 => FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t value))
    (physical_Q_Pa_split (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf))
  simp only [map_add] at tail pair
  have tailPa := pa_source_window_read
    (E (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2))
    (Submodule.starProjection_apply_mem _ _) t
  have pairPa := pa_source_window_read
    (E (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf : BurnolL2))
    (Submodule.starProjection_apply_mem _ _) t
  rw [tailPa,actual_unit_tail_mean_source] at tail
  rw [pairPa,actual_unit_fourier_whole_mean_source] at pair
  have tailRead : FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (actualOriginalUnitPaTail observation nontrivial half : BurnolL2)) =
        actualUnitPaTailMeanProgramme observation nontrivial half t := by
    unfold actualUnitPaTailMeanProgramme actualUnitTailPaSource
    exact eq_sub_of_add_eq' tail
  have pairRead : FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (actualOriginalUnitPaPair observation nontrivial half : BurnolL2)) =
        actualUnitPaPairMeanProgramme observation nontrivial half t := by
    unfold actualUnitPaPairMeanProgramme actualUnitFourierPaSource
    exact eq_sub_of_add_eq' pair
  refine ⟨tailRead,pairRead,?_⟩
  change FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
    ((2:ℂ) • (actualOriginalUnitPaTail observation nontrivial half : BurnolL2) -
      (actualOriginalUnitPaPair observation nontrivial half : BurnolL2))) = _
  rw [map_sub,map_smul,map_sub,map_smul,tailRead,pairRead]
  rfl

def actualNonPaPairMeanProgramme (h t : ℝ) : ℂ :=
  OriginalKPhysicalWindowSourceAction.actualPhysicalPairedGeneratedWindow observation nontrivial half h t -
    paSourceMovingMean (actualFullPairPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) *
      actualUnitPaPairMeanProgramme observation nontrivial half t

def actualNonPaSiblingMeanProgramme (h t : ℝ) : ℂ :=
  OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingGeneratedWindow observation nontrivial half h t -
    paSourceMovingMean (actualFullSiblingPaSource observation nontrivial half h) t -
    (actualWholePaSourceCoefficient observation nontrivial half h/2) *
      actualUnitPaSiblingMeanProgramme observation nontrivial half t

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
