import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCvelCompressedSourceAction.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open OriginalRieszSource
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local instance priceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

def actualExpandedSourceRead (test : BurnolPaAmbientCarrier) (source : BurnolL2) (h : ℝ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..h, inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) source)

def actualContactVelocityPrice (coordinate : BurnolCompletedMellinCoordinate) (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (∫ t : ℝ in (0:ℝ)..h, inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (actualContactVelocity coordinate))) +
  (∫ t : ℝ in (0:ℝ)..(-h), inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (actualContactVelocity coordinate)))

def actualResponseVelocityPrice (coordinate : BurnolCompletedMellinCoordinate) (test : BurnolPaAmbientCarrier) (h : ℝ) : ℂ :=
  (∫ t : ℝ in (0:ℝ)..h, inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (actualResponseVelocity coordinate))) +
  (∫ t : ℝ in (0:ℝ)..(-h), inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t (actualResponseVelocity coordinate)))

private theorem source_orbit_integrable (test : BurnolPaAmbientCarrier) (source : BurnolL2) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation t source)) volume a b :=
  ((innerSL ℂ (test : BurnolL2)).continuous.comp (burnolMultiplicativeDilation_stronglyContinuous source)).intervalIntegrable a b

private theorem source_expanded_integrable (test : BurnolPaAmbientCarrier) (source : BurnolL2) (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) source)) volume a b :=
  (((innerSL ℂ (test : BurnolL2)).continuous.comp (burnolMultiplicativeDilation_stronglyContinuous source)).comp continuous_neg).intervalIntegrable a b

theorem actual_Cvel_contact_inventory_price (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) :
    OriginalKBoundarySourceAction.actualCorrectedVelocityPrice coordinate test h =
      actualContactVelocityPrice coordinate test h + actualResponseVelocityPrice coordinate test h := by
  unfold OriginalKBoundarySourceAction.actualCorrectedVelocityPrice
  rw [actual_source_velocity_contact_inventory]
  simp only [map_add,inner_add_right]
  rw [intervalIntegral.integral_add (source_orbit_integrable test _ 0 h) (source_orbit_integrable test _ 0 h),
    intervalIntegral.integral_add (source_orbit_integrable test _ 0 (-h)) (source_orbit_integrable test _ 0 (-h))]
  unfold actualContactVelocityPrice actualResponseVelocityPrice
  ring

/-- The actual source action removes both compressed halves, retaining the full U/V expansion fields and their physical Fourier cotests. -/
theorem actual_response_velocity_compressed_price (coordinate : BurnolCompletedMellinCoordinate)
    (test : BurnolPaAmbientCarrier) (h : ℝ) (nonnegative : 0 ≤ h) :
    actualResponseVelocityPrice coordinate test h =
      Kernel.A coordinate * actualExpandedSourceRead (F test) Response.wholeU h -
      Kernel.beta coordinate * actualExpandedSourceRead (F test) Response.wholeV h +
      Kernel.A coordinate * actualExpandedSourceRead test Response.wholeV h -
      Kernel.beta coordinate * actualExpandedSourceRead test Response.wholeU h := by
  unfold actualResponseVelocityPrice
  have first : (∫ t : ℝ in (0:ℝ)..h, inner ℂ (test : BurnolL2)
      (burnolMultiplicativeDilation t (actualResponseVelocity coordinate))) =
      Kernel.A coordinate*actualExpandedSourceRead (F test) Response.wholeU h -
      Kernel.beta coordinate*actualExpandedSourceRead (F test) Response.wholeV h := by
    calc
      _ = ∫ t : ℝ in (0:ℝ)..h,
        Kernel.A coordinate*inner ℂ (F test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeU) -
        Kernel.beta coordinate*inner ℂ (F test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeV) := by
          apply intervalIntegral.integral_congr
          intro t inside
          have positive := (uIcc_of_le nonnegative ▸ inside).1
          exact actual_positive_response_cotest coordinate test t positive
      _ = _ := by
        rw [intervalIntegral.integral_sub ((source_expanded_integrable (F test) _ 0 h).const_mul _)
          ((source_expanded_integrable (F test) _ 0 h).const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
        rfl
  have second : (∫ t : ℝ in (0:ℝ)..(-h), inner ℂ (test : BurnolL2)
      (burnolMultiplicativeDilation t (actualResponseVelocity coordinate))) =
      Kernel.A coordinate*actualExpandedSourceRead test Response.wholeV h -
      Kernel.beta coordinate*actualExpandedSourceRead test Response.wholeU h := by
    have negaction := intervalIntegral.integral_comp_neg (f:=fun t : ℝ => inner ℂ (test : BurnolL2)
      (burnolMultiplicativeDilation t (actualResponseVelocity coordinate))) (a:=(0:ℝ)) (b:=h)
    simp only [neg_zero] at negaction
    rw [intervalIntegral.integral_symm (a:=(-h)) (b:=(0:ℝ)),←negaction]
    have generated : (∫ t : ℝ in (0:ℝ)..h, inner ℂ (test : BurnolL2)
        (burnolMultiplicativeDilation (-t) (actualResponseVelocity coordinate))) =
        -Kernel.A coordinate*actualExpandedSourceRead test Response.wholeV h +
        Kernel.beta coordinate*actualExpandedSourceRead test Response.wholeU h := by
      calc
        _ = ∫ t : ℝ in (0:ℝ)..h,
          -Kernel.A coordinate*inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeV) +
          Kernel.beta coordinate*inner ℂ (test : BurnolL2) (burnolMultiplicativeDilation (-t) Response.wholeU) := by
            apply intervalIntegral.integral_congr
            intro t inside
            have positive := (uIcc_of_le nonnegative ▸ inside).1
            exact actual_negative_response_cotest coordinate test t positive
        _ = _ := by
          rw [intervalIntegral.integral_add ((source_expanded_integrable test _ 0 h).const_mul _)
            ((source_expanded_integrable test _ 0 h).const_mul _),intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
          rfl
    rw [generated]
    ring
  rw [first,second]
  ring

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCvelCompressedSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
