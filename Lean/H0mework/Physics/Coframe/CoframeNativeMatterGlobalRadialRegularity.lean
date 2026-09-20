import H0mework.Physics.Coframe.CoframeNativeMatterDualGlobalRadialActionWrite
import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity

/-!
# Global regularity of the coframe-native matter response one-form

This module factors the radial response regularity through an arbitrary smooth,
nondegenerate holonomic current.  No radial exactification, residual, target,
or output action-law certificate is consumed.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterGlobalRadialRegularity

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeMatterDualGlobalRadialActionWrite
open StageNineCoframeNativeMatterFrameAction
open StageNineCoframeNativeMatterOriginActionWrite
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCoframeHolonomicRegularity
open StageNineDiracDualFormNativeLiveCoframeConjugateMatterActionResponse
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open SU7MotherLieAlgebra
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- Every read entering the coframe-native radial matter response is smooth
when it is generated from one smooth nondegenerate holonomic current. -/
theorem coframeNativeGlobalMatterResponseOneForm_contDiff
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    ContDiff ℝ ∞ (coframeNativeGlobalMatterResponseOneForm current) := by
  have coframeRegular : ContDiff ℝ ∞ current.coframe := by
    apply contDiff_pi'
    intro row
    apply contDiff_pi'
    intro column
    exact smooth.1 row column
  have matterCovariantDerivativeRegular :
      ContDiff ℝ ∞ fun point direction =>
        matterCoordinateEquiv
          (holonomicMatterCovariantDerivative current point direction) := by
    apply contDiff_pi'
    intro direction
    exact holonomicMatterCovariantDerivative_coordinate_contDiff_local current
      smooth direction
  have coframeInverseRegular :
      ContDiff ℝ ∞ fun point => (current.coframe point)⁻¹ := by
    rw [contDiff_iff_contDiffAt]
    intro point
    exact
      (coframe_inv_contDiffAt (current.coframe point) (nondegenerate point)).comp
        point coframeRegular.contDiffAt
  have frameMatterDerivativeRegular
      (internal : LorentzianIndex) :
      ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (frameMatterDerivative (current.coframe point)
          (holonomicMatterCovariantDerivative current point) internal) := by
    unfold frameMatterDerivative
    simp only [map_sum, map_smul]
    apply ContDiff.sum
    intro coordinate _
    have inverseEntryRegular : ContDiff ℝ ∞ fun point =>
        (current.coframe point)⁻¹ coordinate internal :=
      contDiff_pi.mp (contDiff_pi.mp coframeInverseRegular coordinate) internal
    have inverseComplexRegular : ContDiff ℝ ∞ fun point =>
        ((current.coframe point)⁻¹ coordinate internal : ℂ) :=
      Complex.ofRealCLM.contDiff.comp inverseEntryRegular
    exact inverseComplexRegular.smul
      (contDiff_pi.mp matterCovariantDerivativeRegular coordinate)
  have frameTimeKnownVectorRegular :
      ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (frameTimeMatterKnownVector (current.coframe point)
          (holonomicMatterCovariantDerivative current point)
          (scalarCoordinateEquiv.symm (current.scalar point))
          (current.matter point)) := by
    have kineticDirectionRegular : ∀ spatial : Fin 3,
        ContDiff ℝ ∞ fun point => matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma spatial.succ)
            (frameMatterDerivative (current.coframe point)
              (holonomicMatterCovariantDerivative current point)
              spatial.succ)) := by
      intro spatial
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.comp (contDiff_const : ContDiff ℝ ∞
            (fun _ : BasePoint => diracGamma spatial.succ))).clm_apply
          (frameMatterDerivativeRegular spatial.succ)
      change ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma spatial.succ)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (frameMatterDerivative (current.coframe point)
                (holonomicMatterCovariantDerivative current point)
                spatial.succ)))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    have kineticSumRegular : ContDiff ℝ ∞ fun point =>
        ∑ spatial : Fin 3, matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma spatial.succ)
            (frameMatterDerivative (current.coframe point)
              (holonomicMatterCovariantDerivative current point)
              spatial.succ)) :=
      ContDiff.sum fun spatial _ => kineticDirectionRegular spatial
    have kineticRegular : ContDiff ℝ ∞ fun point =>
        Complex.I • ∑ spatial : Fin 3, matterCoordinateEquiv
          (diracMatrixMatterAction (diracGamma spatial.succ)
            (frameMatterDerivative (current.coframe point)
              (holonomicMatterCovariantDerivative current point)
              spatial.succ)) :=
      (contDiff_const : ContDiff ℝ ∞
        (fun _ : BasePoint => (Complex.I : ℂ))).smul kineticSumRegular
    have matterRegular : ContDiff ℝ ∞ fun point =>
        matterCoordinateEquiv (current.matter point) :=
      smooth.2.2.2.2.2.2.2.1
    have scalarRegular : ContDiff ℝ ∞ current.scalar :=
      smooth.2.2.2.2.2.2.1
    have yukawaRegular : ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (current.scalar point))
          (current.matter point)) := by
      have actual :=
        (diracDualYukawaCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.comp scalarRegular).clm_apply matterRegular
      change ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (diracDualRightChiralYukawaAction
          (scalarCoordinateEquiv.symm (current.scalar point))
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (current.matter point)))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    unfold frameTimeMatterKnownVector
    simp only [map_add, map_smul, map_sum]
    exact kineticRegular.add yukawaRegular
  have generatedFrameTimeDerivativeRegular :
      ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (globalFrameTimeMatterGeneratedDerivativeAt current point) := by
    have gammaActionRegular : ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma 0)
          (frameTimeMatterKnownVector (current.coframe point)
            (holonomicMatterCovariantDerivative current point)
            (scalarCoordinateEquiv.symm (current.scalar point))
            (current.matter point))) := by
      have actual :=
        (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
          |>.comp (contDiff_const : ContDiff ℝ ∞
            (fun _ : BasePoint => diracGamma 0))).clm_apply
          frameTimeKnownVectorRegular
      change ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (diracMatrixMatterAction (diracGamma 0)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv
              (frameTimeMatterKnownVector (current.coframe point)
                (holonomicMatterCovariantDerivative current point)
                (scalarCoordinateEquiv.symm (current.scalar point))
                (current.matter point))))) at actual
      simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
    unfold globalFrameTimeMatterGeneratedDerivativeAt
      actionGeneratedFrameTimeMatterDerivative
      identityCoframeMatterTimePrincipal
    simp only [map_neg, map_smul]
    exact ((contDiff_const : ContDiff ℝ ∞
      (fun _ : BasePoint => (Complex.I : ℂ))).smul gammaActionRegular).neg
  have frameTimeResponseCoordinatesRegular :
      ContDiff ℝ ∞ fun point => matterCoordinateEquiv
        (globalFrameTimeMatterResponseAt current point) := by
    unfold globalFrameTimeMatterResponseAt
    simp only [map_sub]
    exact generatedFrameTimeDerivativeRegular.sub
      (frameMatterDerivativeRegular 0)
  have rowRegular : ContDiff ℝ ∞ fun point =>
      coframeRowLinearFunctional (current.coframe point) := by
    unfold coframeRowLinearFunctional
    apply ContDiff.sum
    intro coordinate _
    exact (smooth.1 0 coordinate).smul contDiff_const
  unfold coframeNativeGlobalMatterResponseOneForm
  exact rowRegular.smulRight frameTimeResponseCoordinatesRegular

end

end SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterGlobalRadialRegularity
