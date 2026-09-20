import H0mework.Physics.RadialDynamics.MatterProfile

/-! The reduced forcing term is the original Dirac kinetic density. The
phase contributes its explicit total derivative, rather than frozen matter. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics

open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineEnrichedProofFreeSource StageNineDiracKineticLocalSpinDensity
open StageNineP286GaugeConnectionVariationDensity
open DiracCliffordRepresentation Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous

noncomputable section

theorem movingDual_swap (angle : ℝ) :
    movingDual angle (spinPairMatter (unitPhase (-angle)) (unitPhase angle)) = (4*spinScale : ℝ) := by
  change (∑ spin, ∑ state, spinPairCoefficients ((spinScale : ℂ)*unitPhase angle)
    ((spinScale : ℂ)*unitPhase (-angle)) spin state *
      sourceColorDoubletDual state
        (sourceColorDiracMatter (spinPairCoefficients (unitPhase (-angle)) (unitPhase angle)) spin)) = _
  simp only [sourceColorDoubletDual_diracMatter]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  have opposite := unitPhase_opposite angle
  linear_combination 4*(spinScale : ℂ)*opposite

theorem matterDensity_eq (amplitude rate angle : ℝ) :
    generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
      (matterJet amplitude rate angle) = 4*spinScale*rate - 6*lapse*spinScale*(spinScale-amplitude) := by
  unfold generatedDensitizedContinuumMatterKineticDensity
  rw [kineticVector_eq, matterDualFrameRelative_zeroChart]
  change |(homogeneousCoframe lapse).det| * (movingDual angle (_ • _)).re = _
  rw [map_smul, movingDual_swap, homogeneousCoframe_det, abs_of_pos lapse_pos]
  simp [Complex.mul_re, Complex.div_re]
  field_simp [ne_of_gt lapse_pos]
  ring

theorem jointDensity_eq (amplitude velocity rate angle : ℝ) :
    gaugeLagrangian amplitude velocity +
      generatedDensitizedContinuumMatterKineticDensity positiveSmoothUnifiedSource 0 0
        (matterJet amplitude rate angle) =
      lagrangian amplitude velocity + 4*spinScale*rate - 6*lapse*spinScale^2 := by
  rw [matterDensity_eq]
  unfold lagrangian
  rw [sourceLoad_eq]
  ring

theorem phaseBoundary_hasDerivAt (parameter time : ℝ) :
    HasDerivAt (fun t => 4*spinScale*responseAngle parameter t)
      (4*spinScale*deriv (responseAngle parameter) time) time := by
  rw [(responseAngle_hasDerivAt parameter time).deriv]
  exact (responseAngle_hasDerivAt parameter time).const_mul (4*spinScale)

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics
