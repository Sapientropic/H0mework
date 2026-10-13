import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Source
import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


local notation "O" => OriginalKPairedResponseGramAction.originalOutside

def actualWholePaPairedR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.paired (actualWholePaR observation nontrivial half h)
def actualWholePaSiblingR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.sibling (actualWholePaR observation nontrivial half h)
def actualNonPaPairedR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.paired (actualNonPaR observation nontrivial half h)
def actualNonPaSiblingR (h : ℝ) : BurnolL2 :=
  OriginalKCombCofinalPaAction.sibling (actualNonPaR observation nontrivial half h)

def actualWholePaPairedVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualWholePaSiblingR observation nontrivial half h +
    (1/2 : ℂ) • ((actualWholePaSource observation nontrivial half h : BurnolL2) -
      fourierL2 (actualWholePaSource observation nontrivial half h : BurnolL2))
def actualWholePaSiblingVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualWholePaPairedR observation nontrivial half h +
    (1/2 : ℂ) • ((actualWholePaSource observation nontrivial half h : BurnolL2) +
      fourierL2 (actualWholePaSource observation nontrivial half h : BurnolL2))
def actualNonPaPairedVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualNonPaSiblingR observation nontrivial half h +
    (1/2 : ℂ) • (actualNonPaSource observation nontrivial half h - fourierL2 (actualNonPaSource observation nontrivial half h))
def actualNonPaSiblingVelocity (h : ℝ) : BurnolL2 :=
  (observation.coordinate/2-1/4) • actualNonPaPairedR observation nontrivial half h +
    (1/2 : ℂ) • (actualNonPaSource observation nontrivial half h + fourierL2 (actualNonPaSource observation nontrivial half h))

/-- Pa and nonPa sides consume their own actual R action before any projected flux equation. -/
theorem actual_Pa_nonPa_R_source_actions (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (actualWholePaPairedR observation nontrivial half h))
      (actualWholePaPairedVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (actualWholePaSiblingR observation nontrivial half h))
      (actualWholePaSiblingVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (actualNonPaPairedR observation nontrivial half h))
      (actualNonPaPairedVelocity observation nontrivial half h) 0 ∧
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation (-t/2) (actualNonPaSiblingR observation nontrivial half h))
      (actualNonPaSiblingVelocity observation nontrivial half h) 0 := by
  have pa := OriginalKFullSourceRResponse.Paid.ambient_R_paired_equations _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) (actualWholePaSource observation nontrivial half h : BurnolL2)
  have nonPa := OriginalKFullSourceRResponse.Paid.ambient_R_paired_equations _
    (OriginalKCombCofinalRAction.parameter_rightQuarter observation half) (actualNonPaSource observation nontrivial half h)
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [actualWholePaPairedR,actualWholePaSiblingR,actualWholePaR,actualWholePaPairedVelocity,
      OriginalKCombCofinalRAction.original_R_direct] using pa.1
  · simpa only [actualWholePaPairedR,actualWholePaSiblingR,actualWholePaR,actualWholePaSiblingVelocity,
      OriginalKCombCofinalRAction.original_R_direct] using pa.2
  · simpa only [actualNonPaPairedR,actualNonPaSiblingR,actualNonPaR,actualNonPaPairedVelocity,
      OriginalKCombCofinalRAction.original_R_direct] using nonPa.1
  · simpa only [actualNonPaPairedR,actualNonPaSiblingR,actualNonPaR,actualNonPaSiblingVelocity,
      OriginalKCombCofinalRAction.original_R_direct] using nonPa.2

/-- Source-owned Pa membership and original Division pay all four physical legs of the complete actual Pa stock. -/
theorem actual_whole_Pa_four_faces_physical (h : ℝ) :
    actualWholePaPairedR observation nontrivial half h ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    actualWholePaSiblingR observation nontrivial half h ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    actualWholePaPairedVelocity observation nontrivial half h ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius ∧
    actualWholePaSiblingVelocity observation nontrivial half h ∈ evenBurnolClosedFace burnolUnscaledCommonGapRadius := by
  let face := evenBurnolClosedFace burnolUnscaledCommonGapRadius
  have r := actual_whole_Pa_R_physical observation nontrivial half h
  have fr := fourierL2_mem_evenBurnolClosedFace r
  have source := (actualWholePaSource observation nontrivial half h).property
  have fsource := fourierL2_mem_evenBurnolClosedFace source
  have pair : actualWholePaPairedR observation nontrivial half h ∈ face := face.smul_mem _ (face.add_mem r fr)
  have sibling : actualWholePaSiblingR observation nontrivial half h ∈ face := face.smul_mem _ (face.sub_mem r fr)
  exact ⟨pair,sibling,
    face.add_mem (face.smul_mem _ sibling) (face.smul_mem _ (face.sub_mem source fsource)),
    face.add_mem (face.smul_mem _ pair) (face.smul_mem _ (face.add_mem source fsource))⟩

theorem actual_whole_Pa_outside_zero (h : ℝ) :
    O (actualWholePaPairedR observation nontrivial half h) = 0 ∧
    O (actualWholePaSiblingR observation nontrivial half h) = 0 ∧
    O (actualWholePaPairedVelocity observation nontrivial half h) = 0 ∧
    O (actualWholePaSiblingVelocity observation nontrivial half h) = 0 := by
  have source := actual_whole_Pa_four_faces_physical observation nontrivial half h
  exact ⟨Submodule.starProjection_orthogonal_apply_eq_zero source.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.2.1,
    Submodule.starProjection_orthogonal_apply_eq_zero source.2.2.2⟩

private theorem actual_whole_Pa_nonPa_faces (h : ℝ) :
    OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h =
      actualWholePaPairedR observation nontrivial half h + actualNonPaPairedR observation nontrivial half h ∧
    OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h =
      actualWholePaSiblingR observation nontrivial half h + actualNonPaSiblingR observation nontrivial half h := by
  unfold OriginalKFullSourceRResponse.pairedResponse OriginalKFullSourceRResponse.siblingResponse
  rw [actual_whole_R_Pa_nonPa]
  unfold actualWholePaPairedR actualNonPaPairedR actualWholePaSiblingR actualNonPaSiblingR
    OriginalKCombCofinalPaAction.paired OriginalKCombCofinalPaAction.sibling
  simp only [map_add]
  constructor <;> module

private theorem actual_whole_Pa_nonPa_velocities (h : ℝ) :
    OriginalKPairedResponseGramAction.pairedVelocity observation nontrivial half h =
      actualWholePaPairedVelocity observation nontrivial half h + actualNonPaPairedVelocity observation nontrivial half h ∧
    OriginalKPairedResponseGramAction.siblingVelocity observation nontrivial half h =
      actualWholePaSiblingVelocity observation nontrivial half h + actualNonPaSiblingVelocity observation nontrivial half h := by
  have response := actual_whole_Pa_nonPa_faces observation nontrivial half h
  have material : OriginalKFullSourceRResponse.completeSource observation nontrivial half h =
      (actualWholePaSource observation nontrivial half h : BurnolL2) + actualNonPaSource observation nontrivial half h := by
    unfold actualNonPaSource
    module
  unfold OriginalKPairedResponseGramAction.pairedVelocity OriginalKPairedResponseGramAction.siblingVelocity
    actualWholePaPairedVelocity actualNonPaPairedVelocity actualWholePaSiblingVelocity actualNonPaSiblingVelocity
  rw [response.1,response.2,material,map_add]
  constructor <;> module

def actualNonPaOutsideFlux (h : ℝ) : ℂ :=
  inner ℂ (O (actualNonPaPairedR observation nontrivial half h)) (O (actualNonPaSiblingVelocity observation nontrivial half h)) +
  inner ℂ (O (actualNonPaPairedVelocity observation nontrivial half h)) (O (actualNonPaSiblingR observation nontrivial half h))

/-- The complete original Outside consumer pays every Pa source leg, leaving exactly the original Pa-orthogonal and ambient-outside material. -/
theorem actual_outside_flux_consumes_whole_Pa_source (h : ℝ) :
    OriginalKPairedResponseGramAction.actualOutsideFlux observation nontrivial half h =
      actualNonPaOutsideFlux observation nontrivial half h := by
  have response := actual_whole_Pa_nonPa_faces observation nontrivial half h
  have velocity := actual_whole_Pa_nonPa_velocities observation nontrivial half h
  have pa := actual_whole_Pa_outside_zero observation nontrivial half h
  unfold OriginalKPairedResponseGramAction.actualOutsideFlux actualNonPaOutsideFlux
  rw [response.1,response.2,velocity.1,velocity.2]
  simp only [map_add,pa.1,pa.2.1,pa.2.2.1,pa.2.2.2,zero_add]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaSourceRankAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
