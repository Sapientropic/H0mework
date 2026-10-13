import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.Action
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Feet
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.CanonicalRaw.BoundaryTrace.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance projectionEffectComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


private theorem actual_source_window_read (value : BurnolL2) (raw : ℝ → ℂ)
    (source : (value : ℝ → ℂ) =ᵐ[volume] raw) (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t value) =
      actualPhysicalMovingWindow raw t := by
  rw [OriginalJointFluxSource.actual_mean_dilation_source]
  unfold actualPhysicalMovingWindow
  have radius : (1/4 : ℝ)*Real.exp t = Real.exp t/4 := by ring
  have interval : (∫ x : ℝ in symmetricInterval ((1/4 : ℝ)*Real.exp t), value x) =
      ∫ x in -(Real.exp t/4)..Real.exp t/4, raw x := by
    rw [radius]
    change (∫ x : ℝ in Icc (-(Real.exp t/4)) (Real.exp t/4), value x) = _
    rw [intervalIntegral.integral_of_le (by have positive := Real.exp_pos t; linarith)]
    rw [integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    exact ae_restrict_of_ae source
  rw [interval]

/-- The paid mean dilation consumer reads the generated complete P programme at every real shift. -/
theorem actual_physical_moving_window_read (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h) : BurnolL2)) =
      actualPhysicalPairedMovingWindow observation nontrivial half h t ∧
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h) : BurnolL2)) =
      actualPhysicalSiblingMovingWindow observation nontrivial half h t := by
  have source := actual_physical_pair_sibling_source_raw observation nontrivial half h nonnegative bounded
  exact ⟨actual_source_window_read _ _ source.1 t, actual_source_window_read _ _ source.2 t⟩

/-- The source P gap pays the contracting half of each contact; the expanding half remains its actual annulus programme. -/
def actualPhysicalPairedSeedPrice (h t : ℝ) : ℂ :=
  (1/4 : ℂ) * (star ((Real.exp (-t/2) : ℂ)*actualPhysicalPairedMovingWindow observation nontrivial half h 0) +
    star (actualPhysicalPairedMovingWindow observation nontrivial half h t) -
    2*star (actualPhysicalPairedMovingWindow observation nontrivial half h 0))

def actualPhysicalSiblingSeedPrice (h t : ℝ) : ℂ :=
  (1/4 : ℂ) * (star ((Real.exp (-t/2) : ℂ)*actualPhysicalSiblingMovingWindow observation nontrivial half h 0) +
    star (actualPhysicalSiblingMovingWindow observation nontrivial half h t) -
    2*star (actualPhysicalSiblingMovingWindow observation nontrivial half h 0))

/-- Both original complete seed contacts consume their own actual source windows with the correct quarter normalization. -/
theorem actual_physical_seed_window_price (h : ℝ) (nonnegative : 0 ≤ h) (bounded : h ≤ Real.log 2)
    (t : ℝ) (positive : 0 ≤ t) :
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) t =
      actualPhysicalPairedSeedPrice observation nontrivial half h t ∧
    OriginalKBoundarySourceAction.actualSeedWindowPrice
      (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) t =
      actualPhysicalSiblingSeedPrice observation nontrivial half h t := by
  have initial := actual_physical_moving_window_read observation nontrivial half h nonnegative bounded 0
  simp only [burnolMultiplicativeDilation_zero] at initial
  have expanded := actual_physical_moving_window_read observation nontrivial half h nonnegative bounded t
  have pairNegative := FiniteMobiusResolventFlux.actual_mean_source_negative
    (P (OriginalKFullSourceRResponse.pairedResponse observation nontrivial half h)) (-t) (neg_nonpos.mpr positive)
  have siblingNegative := FiniteMobiusResolventFlux.actual_mean_source_negative
    (P (OriginalKFullSourceRResponse.siblingResponse observation nontrivial half h)) (-t) (neg_nonpos.mpr positive)
  constructor
  · unfold OriginalKBoundarySourceAction.actualSeedWindowPrice actualPhysicalPairedSeedPrice
    rw [pairNegative, initial.1, expanded.1]
  · unfold OriginalKBoundarySourceAction.actualSeedWindowPrice actualPhysicalSiblingSeedPrice
    rw [siblingNegative, initial.2, expanded.2]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
