import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWholeWardSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance boundarySourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
namespace Source
export OriginalKConstantContactSourceAction.ConstantSource (value velocity seed)
end Source
local notation "P" => burnolEvenAmbientProjection

/-- The actual two-contact corrected source carries its already-generated strong action to every shift. -/
theorem actual_corrected_source_action (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    HasDerivAt (fun t : ℝ => burnolMultiplicativeDilation t (Source.value coordinate))
      (burnolMultiplicativeDilation h (Source.velocity coordinate)) h := by
  have original := OriginalKConstantContactSourceAction.ConstantSource.strong_derivative coordinate
  have chart : HasDerivAt (fun t : ℝ => t-h) 1 h := by
    convert! (hasDerivAt_id h).sub_const h using 1
  have shifted := original.scomp_of_eq h chart (by simp)
  have action := ((burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt h shifted
  convert! action using 1
  · funext t
    change burnolMultiplicativeDilation t (Source.value coordinate) =
      burnolMultiplicativeDilation h (burnolMultiplicativeDilation (t-h) (Source.value coordinate))
    rw [burnolMultiplicativeDilation_add]
    congr 1
    ring
  · change _ = burnolMultiplicativeDilation h ((1 : ℝ) • Source.velocity coordinate)
    rw [one_smul]

/-- The complete source velocity is integrated before any physical projection or scalar target. -/
theorem actual_corrected_source_finite_action (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    burnolMultiplicativeDilation h (Source.value coordinate) = Source.value coordinate +
      ∫ t : ℝ in (0 : ℝ)..h, burnolMultiplicativeDilation t (Source.velocity coordinate) := by
  have integrable : IntervalIntegrable (fun t : ℝ => burnolMultiplicativeDilation t (Source.velocity coordinate)) volume 0 h :=
    (burnolMultiplicativeDilation_stronglyContinuous (Source.velocity coordinate)).intervalIntegrable 0 h
  have generated := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => actual_corrected_source_action coordinate t) integrable
  simp only [burnolMultiplicativeDilation_zero] at generated
  calc
    _ = Source.value coordinate +
        (burnolMultiplicativeDilation h (Source.value coordinate)-Source.value coordinate) := by module
    _ = _ := by rw [← generated]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKBoundarySourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
