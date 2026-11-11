import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance rawWindowComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "radius" t => ((1/4:ℝ)*Real.exp t)
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- Qualification comes from the already generated exact R source and both actual quarter corrections, before constructing its window vector. -/
theorem actual_physical_source_raw_qualified (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) :
    MemLp (OriginalKPhysicalWindowSourceAction.actualPhysicalPairedRaw observation nontrivial half h) 2 volume ∧
    MemLp (OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingRaw observation nontrivial half h) 2 volume := by
  have source := OriginalKPhysicalWindowSourceAction.actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative bounded
  exact ⟨(memLp_congr_ae source.1).mp (Lp.memLp _),(memLp_congr_ae source.2).mp (Lp.memLp _)⟩

def actualPhysicalPairRawWindow (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    BurnolRadiusIntervalL2 (radius t) :=
  ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).1.restrict
    (symmetricInterval (radius t))).toLp (OriginalKPhysicalWindowSourceAction.actualPhysicalPairedRaw observation nontrivial half h)

def actualPhysicalSiblingRawWindow (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    BurnolRadiusIntervalL2 (radius t) :=
  ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).2.restrict
    (symmetricInterval (radius t))).toLp (OriginalKPhysicalWindowSourceAction.actualPhysicalSiblingRaw observation nontrivial half h)

/-- The full P window is generated from the same raw source field, including both inverse correction feet; no point trace is assumed. -/
theorem actual_physical_source_raw_window_vectors (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2) (t : ℝ) :
    burnolRadiusRestriction (radius t) (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2) =
      actualPhysicalPairRawWindow observation nontrivial half h nonnegative bounded t ∧
    burnolRadiusRestriction (radius t) (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2) =
      actualPhysicalSiblingRawWindow observation nontrivial half h nonnegative bounded t := by
  have source := OriginalKPhysicalWindowSourceAction.actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative bounded
  constructor
  · apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (radius t))
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2),
      ae_restrict_of_ae source.1,
      MemLp.coeFn_toLp ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).1.restrict
        (symmetricInterval (radius t)))] with x restricted raw generated
    exact restricted.trans (raw.trans generated.symm)
  · apply Lp.ext
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval (radius t))
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2),
      ae_restrict_of_ae source.2,
      MemLp.coeFn_toLp ((actual_physical_source_raw_qualified observation nontrivial half h nonnegative bounded).2.restrict
        (symmetricInterval (radius t)))] with x restricted raw generated
    exact restricted.trans (raw.trans generated.symm)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalRawWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
