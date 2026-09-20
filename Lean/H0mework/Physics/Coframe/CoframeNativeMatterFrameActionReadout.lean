import H0mework.Physics.Coframe.CoframeNativeMatterFrameAction
import H0mework.Physics.DualVariation.ConjugateMatterVariation
import H0mework.Physics.DualVariation.MotherAction

/-!
# Coframe-native matter frame-action readout

This module identifies the branch-free frame-time action law with the
primitive Dirac-dual matter equation of the same mother action.  It is a
readout only: neither direction constructs a response or accepts a target
zero fiber.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterFrameActionReadout

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeNativeMatterFrameAction
open StageNineConjugateMatterVariation
open StageNineDiracDualFormNativeConjugateMatterVariation
open StageNineDiracDualFormNativeMotherAction
open StageNineDiracDualYukawaSpinJurisdiction
open StageNineDiracDualYukawaLocalSpinDensity
open StageNineDiracKineticLocalSpinDensity
open StageNineDynamicBreakingVacuum
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineMatterActionTimeVelocity
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionVariationDensity
open SU7ExteriorBreakingYukawa
open scoped Matrix

noncomputable section

set_option autoImplicit false

/-- The primitive Dirac--Yukawa vector is the complete frame-time action
readout: internal time plus all three frame-spatial legs. -/
theorem generatedContinuumDiracDualMatterVector_eq_frameTimeActionReadout
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point) =
      identityCoframeMatterTimePrincipal
          (frameMatterDerivative (configuration.coframe point)
            (holonomicMatterCovariantDerivative configuration point) 0) +
        frameTimeMatterKnownVector (configuration.coframe point)
          (holonomicMatterCovariantDerivative configuration point)
          (scalarCoordinateEquiv.symm (configuration.scalar point))
          (configuration.matter point) := by
  unfold generatedContinuumDiracDualMatterVector
    generatedContinuumMatterKineticVector
    generatedContinuumDiracDualYukawaVector
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
  simp only [toContinuumPointField,
    matterDerivativeFrameRelative_zeroChart,
    scalarFrameRelativeCoordinates_zeroChart,
    matterFrameRelative_zeroChart]
  have kineticEq :
    (Complex.I • ∑ direction : LorentzianIndex,
      diracMatrixMatterAction
        (inverseCoframeDiracGamma
          { coframe := configuration.coframe point, derivative := 0 }
          direction)
        (holonomicMatterCovariantDerivative configuration point direction)) =
      Complex.I • ∑ internal : LorentzianIndex,
        diracMatrixMatterAction (diracGamma internal)
          (frameMatterDerivative (configuration.coframe point)
            (holonomicMatterCovariantDerivative configuration point)
            internal) := by
    unfold frameMatterDerivative
    congr 1
    simp_rw [diracMatrixMatterAction_inverseGamma_expand]
    simp only [map_sum, map_smul]
    rw [Finset.sum_comm]
  rw [kineticEq]
  unfold frameTimeMatterKnownVector identityCoframeMatterTimePrincipal
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  simp
  module

/-- The coframe-native frame action law and the mother-action Dirac vector
have exactly the same zero fiber at every spacetime point. -/
theorem frameTimeMatterActionLaw_iff_generatedContinuumDiracDualMatterVector_zero
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    FrameTimeMatterActionLaw (configuration.coframe point)
        (holonomicMatterCovariantDerivative configuration point)
        (scalarCoordinateEquiv.symm (configuration.scalar point))
        (configuration.matter point)
        (frameMatterDerivative (configuration.coframe point)
          (holonomicMatterCovariantDerivative configuration point) 0) ↔
      generatedContinuumDiracDualMatterVector source 0 point
          (toContinuumPointField configuration point) = 0 := by
  rw [generatedContinuumDiracDualMatterVector_eq_frameTimeActionReadout]
  rfl

/-- At one nondegenerate point, the full real/imaginary family of independent
dual coefficients faithfully detects the primitive Dirac vector. -/
theorem generatedContinuumDiracDualMatterVector_eq_zero_of_conjugateCoefficients
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint)
    (nondegenerate : Matrix.det (configuration.coframe point) ≠ 0)
    (coefficientsZero :
      (fun direction =>
        diracDualConjugateMatterDirectionalCoefficient source configuration
          direction point) = 0) :
    generatedContinuumDiracDualMatterVector source 0 point
        (toContinuumPointField configuration point) = 0 := by
  let vector := generatedContinuumDiracDualMatterVector source 0 point
    (toContinuumPointField configuration point)
  have volumeNe :
      generatedVolumeDensity (toContinuumPointField configuration point) ≠
        0 := by
    unfold generatedVolumeDensity toContinuumPointField
    exact abs_ne_zero.mpr nondegenerate
  apply matterCoordinateEquiv.injective
  apply PiLp.ext
  intro index
  let realDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index (1 : ℂ)
  let imaginaryDirection : MatterCoordinateCarrier :=
    EuclideanSpace.single index Complex.I
  have realEquation := congrFun coefficientsZero realDirection
  have imaginaryEquation := congrFun coefficientsZero imaginaryDirection
  simp only [Pi.zero_apply] at realEquation imaginaryEquation
  have realPartZero : (matterCoordinateEquiv vector index).re = 0 := by
    unfold diracDualConjugateMatterDirectionalCoefficient realDirection
      at realEquation
    rw [matterDualOfCoordinates_single_apply] at realEquation
    simp only [mul_one] at realEquation
    exact (mul_eq_zero.mp realEquation).resolve_left volumeNe
  have imaginaryPartZero : (matterCoordinateEquiv vector index).im = 0 := by
    unfold diracDualConjugateMatterDirectionalCoefficient imaginaryDirection
      at imaginaryEquation
    rw [matterDualOfCoordinates_single_apply] at imaginaryEquation
    have productReal :
        (matterCoordinateEquiv vector index * Complex.I).re =
          -(matterCoordinateEquiv vector index).im := by
      simp
    rw [productReal] at imaginaryEquation
    have negImaginaryZero :=
      (mul_eq_zero.mp imaginaryEquation).resolve_left volumeNe
    exact neg_eq_zero.mp negImaginaryZero
  have coordinateZero : matterCoordinateEquiv vector index = 0 :=
    Complex.ext realPartZero imaginaryPartZero
  simpa [vector] using coordinateZero

end

end
  SaturationMonoid.PhysicsCore.StageNineCoframeNativeMatterFrameActionReadout
