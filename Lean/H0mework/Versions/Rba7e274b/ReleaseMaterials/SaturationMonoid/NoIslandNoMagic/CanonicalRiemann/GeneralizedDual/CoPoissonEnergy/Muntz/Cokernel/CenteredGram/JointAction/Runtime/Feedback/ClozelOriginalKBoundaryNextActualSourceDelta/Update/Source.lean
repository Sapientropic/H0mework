import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholePaSourceRankAction.Character

import H0mework.Versions.V2.Arithmetic.RiemannNativeCurrent.ProjectedSourcePhysical
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance wholePaNativeUpdateComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


open OriginalKWholePaSourceRankAction
local notation "E" => OriginalKCombCofinalPaAction.E

def actualWholePaNativeSourceUpdate (h nextShift : ℝ) : BurnolPaAmbientCarrier :=
  E (OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift)
def actualNonPaNativeSourceUpdate (h nextShift : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.completeNativeUpdate observation nontrivial half h nextShift -
    (actualWholePaNativeSourceUpdate observation nontrivial half h nextShift : BurnolL2)
def actualNativeSourceCoefficientUpdate (h nextShift : ℝ) : ℂ :=
  burnolPaResolventSourceCoefficient (actualWholePaDivisionCoordinate observation nontrivial half)
    (actualWholePaNativeSourceUpdate observation nontrivial half h nextShift)
def actualNonPaNativeRUpdate (h nextShift : ℝ) : BurnolL2 :=
  OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualNonPaNativeSourceUpdate observation nontrivial half h nextShift)

/-- The already-generated original full source update acts on both dependent Pa/nonPa projections before coefficient or target price changes. -/
theorem actual_native_source_Pa_nonPa_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    actualWholePaSource observation nontrivial half nextShift - actualWholePaSource observation nontrivial half h =
      actualWholePaNativeSourceUpdate observation nontrivial half h nextShift ∧
    actualNonPaSource observation nontrivial half nextShift - actualNonPaSource observation nontrivial half h =
      actualNonPaNativeSourceUpdate observation nontrivial half h nextShift := by
  have source := OriginalKFullSourceRResponse.actual_complete_native_update observation nontrivial half h nextShift nonnegative ordered
  have pa := congrArg E source
  simp only [map_sub] at pa
  refine ⟨pa,?_⟩
  unfold actualNonPaSource actualNonPaNativeSourceUpdate
  have rawPa := congrArg (fun x : BurnolPaAmbientCarrier => (x : BurnolL2)) pa
  change (actualWholePaSource observation nontrivial half nextShift : BurnolL2) -
    (actualWholePaSource observation nontrivial half h : BurnolL2) =
    (actualWholePaNativeSourceUpdate observation nontrivial half h nextShift : BurnolL2) at rawPa
  linear_combination (norm := module) source - rawPa

/-- The original source coefficient and original R consume this exact generated update; no target character difference is an input. -/
theorem actual_native_rank_R_source_update (h nextShift : ℝ) (nonnegative : 0 ≤ h) (ordered : h ≤ nextShift) :
    actualWholePaSourceCoefficient observation nontrivial half nextShift - actualWholePaSourceCoefficient observation nontrivial half h =
      actualNativeSourceCoefficientUpdate observation nontrivial half h nextShift ∧
    actualNonPaR observation nontrivial half nextShift - actualNonPaR observation nontrivial half h =
      actualNonPaNativeRUpdate observation nontrivial half h nextShift := by
  have source := actual_native_source_Pa_nonPa_update observation nontrivial half h nextShift nonnegative ordered
  constructor
  · unfold actualWholePaSourceCoefficient actualNativeSourceCoefficientUpdate
    rw [←source.1,map_sub]
  · unfold actualNonPaR actualNonPaNativeRUpdate
    rw [←source.2,map_sub]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKWholePaNativeRankSourceUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
