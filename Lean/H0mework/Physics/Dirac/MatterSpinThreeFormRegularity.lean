import H0mework.Physics.Dirac.MatterSpinThreeForm
import H0mework.Physics.Lorentz.LorentzConnectionActualVariationRegularity

/-!
# Regularity of the form-native matter spin three-form

This module proves continuity in the base point of the action-generated
matter spin three-form.  The direction used to read one W13 coordinate is a
fixed lowered Lorentz one-form, not a compactly supported field variation;
therefore the proof regenerates the finite-dimensional matter coefficient
regularity directly from the live coframe, matter, and conjugate-matter
fields.

No action equation, stationarity theorem, pointwise residual, torsion
solution, source slot, or fixed actual is consumed.  Nondegeneracy appears
only where the inverse coframe enters the Dirac kinetic coefficient.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineFormNativeMatterSpinThreeFormRegularity

open ComplexConjugate
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineLorentzConnectionActualVariationRegularity
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineTopologicalLorentzThreeFormDualInverse
open StageNineTopologicalLorentzThreeFormDuality
open SU7ExteriorBreakingYukawa
open scoped Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 600000

local instance matterCoordinateIndexFintype : Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-! ## Fixed-direction matter coefficient -/

theorem pointwiseMatterLorentzConnectionDirection_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (direction : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (pointwiseMatterLorentzConnectionVariation
          (toContinuumPointField configuration point) direction
            formDirection) := by
  have matrixContinuous : Continuous fun _ : BasePoint =>
      diracSpinConnectionLift
        (lorentzSkewConnectionOfBivectorOneForm direction) formDirection :=
    continuous_const
  have matterContinuous : Continuous fun point =>
      matterCoordinateEquiv (configuration.matter point) :=
    smooth.2.2.2.2.2.2.2.1.continuous
  unfold pointwiseMatterLorentzConnectionVariation toContinuumPointField
  exact diracMatrixMatterCoordinate_raw_apply_continuous _ _
    matrixContinuous matterContinuous

theorem pointwiseMatterLorentzKineticSummand_coordinate_continuous
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm)
    (formDirection : LorentzianIndex) :
    Continuous fun point =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := configuration.coframe point, derivative := 0 }
            formDirection)
          (pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField configuration point) direction
              formDirection)) :=
  diracMatrixMatterCoordinate_raw_apply_continuous _ _
    (holonomicInverseCoframeDiracGamma_continuous configuration smooth
      nondegenerate formDirection)
    (pointwiseMatterLorentzConnectionDirection_coordinate_continuous
      configuration smooth direction formDirection)

theorem pointwiseMatterLorentzKineticSum_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterCovariantDerivativeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField configuration point) direction)) := by
  have sumContinuous : Continuous fun point =>
      ∑ formDirection : LorentzianIndex,
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := configuration.coframe point, derivative := 0 }
              formDirection)
            (pointwiseMatterLorentzConnectionVariation
              (toContinuumPointField configuration point) direction
                formDirection)) := by
    apply continuous_finsetSum
    intro formDirection _
    exact pointwiseMatterLorentzKineticSummand_coordinate_continuous
      configuration smooth nondegenerate direction formDirection
  exact sumContinuous.congr fun point => by
    unfold matterCovariantDerivativeKineticSum
      matterDerivativeFrameRelative
    simp only [toContinuumPointField, matterFrameRelative_zeroChart, map_sum]

theorem pointwiseMatterLorentzVariationVector_coordinate_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCoordinateEquiv
        (matterCovariantDerivativeVariationVector source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField configuration point) direction)) := by
  have kineticContinuous :=
    pointwiseMatterLorentzKineticSum_coordinate_continuous source
      configuration smooth nondegenerate direction
  have coordinateContinuous : Continuous fun point =>
      Complex.I • matterCoordinateEquiv
        (matterCovariantDerivativeKineticSum source 0 point
          (toContinuumPointField configuration point)
          (pointwiseMatterLorentzConnectionVariation
            (toContinuumPointField configuration point) direction)) :=
    ((continuous_const : Continuous fun _ : BasePoint => Complex.I).smul
      kineticContinuous).congr fun point => rfl
  unfold matterCovariantDerivativeVariationVector
  exact coordinateContinuous.congr fun point => by rw [map_smul]

theorem pointwiseMatterLorentzFirstDensity_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      matterCovariantDerivativeFirstVariationDensity source 0 point
        (toContinuumPointField configuration point)
        (pointwiseMatterLorentzConnectionVariation
          (toContinuumPointField configuration point) direction) := by
  let vector := fun point =>
    matterCovariantDerivativeVariationVector source 0 point
      (toContinuumPointField configuration point)
      (pointwiseMatterLorentzConnectionVariation
        (toContinuumPointField configuration point) direction)
  have vectorCoordinateContinuous : Continuous fun point =>
      matterCoordinateEquiv (vector point) :=
    pointwiseMatterLorentzVariationVector_coordinate_continuous source
      configuration smooth nondegenerate direction
  have dualCoefficientContinuous : ∀ index : MatterCoordinateIndex,
      Continuous fun point =>
        configuration.conjugateMatter point
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))) :=
    fun index => smooth.2.2.2.2.2.2.2.2 index |>.continuous
  have pairingContinuous : Continuous fun point =>
      ∑ index : MatterCoordinateIndex,
        matterCoordinateEquiv (vector point) index *
          configuration.conjugateMatter point
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))) := by
    apply continuous_finsetSum
    intro index _
    have vectorCoefficientContinuous : Continuous fun point =>
        matterCoordinateEquiv (vector point) index :=
      (PiLp.continuous_apply 2
        (fun _ : MatterCoordinateIndex => ℂ) index).comp
          vectorCoordinateContinuous
    exact vectorCoefficientContinuous.mul (dualCoefficientContinuous index)
  have realPairingContinuous := Complex.continuous_re.comp pairingContinuous
  unfold matterCovariantDerivativeFirstVariationDensity
  simp only [toContinuumPointField, matterDualFrameRelative_zeroChart]
  exact realPairingContinuous.congr fun point => by
    simp only [Function.comp_apply]
    rw [← matterDual_coordinate_expansion
      (configuration.conjugateMatter point)
      (matterCoordinateEquiv (vector point))]
    simp only [matterCoordinateEquiv.symm_apply_apply]
    rfl

theorem holonomicFormNativeLorentzMatterFirstCoefficient_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate)
    (direction : LorentzBivectorOneForm) :
    Continuous fun point =>
      formNativeLorentzMatterFirstCoefficient source 0 point
        (toContinuumPointField configuration point) direction := by
  have volumeContinuous : Continuous fun point =>
      generatedVolumeDensity (toContinuumPointField configuration point) := by
    unfold generatedVolumeDensity toContinuumPointField
    exact (holonomicCoframe_continuous configuration smooth).matrix_det.abs
  exact volumeContinuous.mul
    (pointwiseMatterLorentzFirstDensity_continuous source configuration smooth
      nondegenerate direction)

/-! ## Three-form regularity -/

/-- The unique action-signed matter spin representative varies continuously
with the same actual holonomic fields. -/
theorem holonomicFormNativeMatterSpinThreeForm_continuous
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (nondegenerate : configuration.Nondegenerate) :
    Continuous fun point =>
      formNativeMatterSpinThreeForm source 0 point
        (toContinuumPointField configuration point) := by
  apply continuous_pi
  intro internalPair
  apply continuous_pi
  intro triple
  change Continuous fun point =>
    oneWedgeThreeSign (missingTripleOfOneForm triple) *
      formNativeLorentzMatterFirstCoefficient source 0 point
        (toContinuumPointField configuration point)
        (loweredLorentzBivectorOneFormCoordinate
          (missingTripleOfOneForm triple) internalPair)
  exact continuous_const.mul
    (holonomicFormNativeLorentzMatterFirstCoefficient_continuous source
      configuration smooth nondegenerate
      (loweredLorentzBivectorOneFormCoordinate
        (missingTripleOfOneForm triple) internalPair))

end

end
  SaturationMonoid.PhysicsCore.StageNineFormNativeMatterSpinThreeFormRegularity
