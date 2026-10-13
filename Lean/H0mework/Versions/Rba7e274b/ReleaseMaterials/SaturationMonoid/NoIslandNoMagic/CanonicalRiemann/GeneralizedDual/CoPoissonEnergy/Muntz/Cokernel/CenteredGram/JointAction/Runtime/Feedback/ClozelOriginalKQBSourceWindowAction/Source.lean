import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
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
local instance qbSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
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
/-- The complete finite window is produced from one actual Mobius source, with its source-owned constant mode. -/
def paSourceWindowProgramme (source : BurnolL2) (t : ℝ) : BurnolRadiusIntervalL2 ((1/4:ℝ)*Real.exp t) :=
  burnolSourceOnlyCoPoissonWindow ((1/4:ℝ)*Real.exp t) source

def paSourceMovingMean (source : BurnolL2) (t : ℝ) : ℂ :=
  (2:ℂ) * (Real.exp (-t/2):ℂ) *
    inner ℂ (intervalConstant ((1/4:ℝ)*Real.exp t)) (paSourceWindowProgramme source t)

private theorem restriction_mean_integral (radius : ℝ) (value : BurnolL2) :
    inner ℂ (intervalConstant radius) (burnolRadiusRestriction radius value) =
      ∫ x : ℝ in symmetricInterval radius, value x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [intervalConstant_coeFn radius,LpToLpRestrictCLM_coeFn ℂ (symmetricInterval radius) value]
    with x unit restricted
  change burnolRadiusRestriction radius value x = value x at restricted
  rw [unit,restricted,RCLike.inner_apply]
  simp only [starRingEnd_apply,star_one,mul_one]

/-- Membership is supplied by the actual Pa projection; the source programme is generated before the moving mean reader. -/
theorem pa_source_window_read (value : BurnolPaAmbientCarrier)
    (qualified : value ∈ burnolCompactCoPoissonClosedRange) (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t (value:BurnolL2)) =
      paSourceMovingMean (burnolMobiusSourceL2 value) t := by
  unfold paSourceMovingMean paSourceWindowProgramme
  rw [burnolSourceOnlyCoPoissonWindow_replay _ value qualified,
    restriction_mean_integral,OriginalJointFluxSource.actual_mean_dilation_source]

/-- The hidden Pa part of the actual full R response is itself a qualified source occurrence, not a free window scalar. -/
def actualFullResponsePaSource (h : ℝ) : BurnolL2 :=
  burnolMobiusSourceL2 (E (OriginalKFullSourceRResponse.Op.R observation nontrivial half
    (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)))

def actualFullResponsePaMeanProgramme (h t : ℝ) : ℂ :=
  paSourceMovingMean (actualFullResponsePaSource observation nontrivial half h) t

theorem actual_full_response_Pa_window (h t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (E (OriginalKFullSourceRResponse.Op.R observation nontrivial half
        (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)) : BurnolL2)) =
      actualFullResponsePaMeanProgramme observation nontrivial half h t :=
  pa_source_window_read _ (Submodule.starProjection_apply_mem _ _) t

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
