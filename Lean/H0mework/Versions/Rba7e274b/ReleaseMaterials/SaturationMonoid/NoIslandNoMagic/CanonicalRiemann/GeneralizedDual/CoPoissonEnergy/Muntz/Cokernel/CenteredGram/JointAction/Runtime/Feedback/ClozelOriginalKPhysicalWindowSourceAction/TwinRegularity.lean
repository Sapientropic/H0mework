import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.TwinSource

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
local instance twinRegularityComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half


/-- The actual born source primitive is continuous on its admitted positive radial carrier. -/
theorem actual_tate_fourier_R_raw_continuous (h : ℝ) :
    ContinuousOn (actualTateFourierRRaw observation nontrivial half h) (Ioi 0) := by
  have primitive : ContinuousOn
      (fun x : ℝ => ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ)^(observation.coordinate-1) * actualTateFourierSourceMaterial observation nontrivial half h t)
      (Ioi 0) := by
    apply continuousOn_of_locally_continuousOn
    intro x positive
    have bound : 0 < x+1 := by have hx : 0 < x := positive; linarith
    have source : IntervalIntegrable
        (fun t : ℝ => (t : ℂ)^(observation.coordinate-1) * actualTateFourierSourceMaterial observation nontrivial half h t)
        volume 0 (x+1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le bound.le]
      exact actual_material_weighted_integrable observation nontrivial half (actualTateFourierSourceMaterial observation nontrivial half h) (x+1) bound
    have continuous := intervalIntegral.continuousOn_primitive_interval' source
      (show (0 : ℝ) ∈ uIcc 0 (x+1) by rw [uIcc_of_le bound.le]; exact ⟨le_rfl,bound.le⟩)
    refine ⟨Ioo 0 (x+1), isOpen_Ioo, ⟨positive, by linarith⟩, continuous.mono ?_⟩
    rw [uIcc_of_le bound.le]
    rintro t ⟨_,inside⟩
    exact ⟨inside.1.le, inside.2.le⟩

  unfold actualTateFourierRRaw
  have scalar : ContinuousOn (fun x : ℝ => -(2 : ℂ) * (x : ℂ)^(-observation.coordinate)) (Ioi 0) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.cpow_const (by fun_prop)
    intro x inside
    exact Complex.ofReal_mem_slitPlane.mpr (show 0 < x from inside)

  exact scalar.mul (primitive.congr (fun x positive => (intervalIntegral.integral_of_le (show 0 ≤ x from (show 0 < x from positive).le)).symm))

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPhysicalWindowSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
