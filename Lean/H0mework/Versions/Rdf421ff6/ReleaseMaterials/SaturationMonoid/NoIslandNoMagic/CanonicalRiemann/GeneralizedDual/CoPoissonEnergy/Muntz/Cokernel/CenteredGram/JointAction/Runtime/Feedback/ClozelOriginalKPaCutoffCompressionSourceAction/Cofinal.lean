import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Inverse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Support
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace



open Filter
open scoped Topology

/-- Cofinal support exhausts the actual original physical source, with all projection leakage retained. -/
theorem physical_tail_strong_tendsto (value : BurnolPaAmbientCarrier) :
 Tendsto (fun N : Nat => physicalTailAction (N+1:ℝ) value) atTop (𝓝 0) := by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 exact squeeze_zero (fun N => norm_nonneg _) (fun N => physical_tail_norm_le_outside _ _)
  (outside_tail_norm_tendsto (value : BurnolL2))

theorem actual_inverse_residual_strong_tendsto (material : F.Branches) :
 Tendsto (fun N : Nat => F.firstInverseResidual (N+1:ℝ) (Native.sourceFields (actualNu material))) atTop (𝓝 0) := by
 apply tendsto_zero_iff_norm_tendsto_zero.mpr
 have source := (outside_tail_norm_tendsto (actualPaField material : BurnolL2)).const_mul ‖burnolMobiusSourceL2‖
 exact squeeze_zero (fun N => norm_nonneg _) (fun N => actual_inverse_residual_norm_cost _ _)
  (by simpa only [mul_zero] using source)

theorem actual_finite_inverse_source_tendsto (material : F.Branches) :
 Tendsto (fun N : Nat => burnolMobiusSourceL2 (physicalCutoffAction (N+1:ℝ) (actualPaField material))) atTop
  (𝓝 (actualNu material)) := by
 have generated := (tendsto_const_nhds (x:=actualNu material)).sub (actual_inverse_residual_strong_tendsto material)
 rw [sub_zero] at generated
 exact generated.congr (fun N => actual_source_recovery_is_finite_inverse (N+1:ℝ) material)

/-- A fixed source window consumes the generated inverse limit; its scalar/radius is not a runtime tick. -/
theorem actual_fixed_window_inverse_tendsto (radius : ℝ) (material : F.Branches) :
 Tendsto (fun N : Nat => burnolSourceOnlyCoPoissonWindow radius
  (burnolMobiusSourceL2 (physicalCutoffAction (N+1:ℝ) (actualPaField material)))) atTop
  (𝓝 (burnolRadiusRestriction radius (actualPaField material : BurnolL2))) := by
 have generated := (burnolSourceOnlyCoPoissonWindow radius).continuous.continuousAt.tendsto.comp
  (actual_finite_inverse_source_tendsto material)
 have read := burnolSourceOnlyCoPoissonWindow_replay radius (actualPaField material)
  (OriginalKMaterialPaWindowSourceAction.source_pa_qualified material)
 change burnolSourceOnlyCoPoissonWindow radius (actualNu material) = _ at read
 rw [read] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
