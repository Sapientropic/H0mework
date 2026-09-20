import H0mework.Physics.CartanAction.CartanConnectionLocalActualLift
import H0mework.Physics.CoframeVariation.CoframeHolonomicRegularity

/-!
# Point--coframe regularity of the action-native Cartan response

The identity-EC Hessian write changes the primitive coframe by a quadratic
field while retaining the matter and conjugate-matter paths.  To compare the
Cartan connection before and after that write, the W13 response must therefore
be read as a function of the joint carrier

`BasePoint × LorentzianCoframe`.

This module supplies that dependency seam directly from the live Dirac
connection variation.  It does not accept a response derivative, torsion,
contorsion, connection, curvature, or settlement receipt.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanPointCoframeRegularity

open DiracExteriorMatterAction
open DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift
open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCartanTorsionThreeFormEquiv
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeTwoFormPairing
open StageNineCoframeVariation
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanConnectionLocalActualLift
open StageNineDiracDualFormNativeSpinTorsionAcceptance
open StageNineEnrichedProofFreeSource
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeMatterSpinThreeForm
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineIIPlusRestriction
open StageNineLorentzConnectionVariation
open StageNineMatterCovariantDerivativeAffine
open StageNineMatterVariation
open StageNineResidualLinearPlebanskiTorsionReduction
open StageNineTopologicalLorentzThreeFormDuality
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

local instance cartanPointCoframeMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

/-- The physical W13 response with the point path retained from one actual
configuration and the coframe exposed as an independent finite-dimensional
input.  Matter and conjugate matter still come from the same actual at the
same point. -/
def diracDualFormNativeActionSpinResponsePointCoframe
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (joint : BasePoint × LorentzianCoframe) :
    PhysicalBivectorThreeForm :=
  formNativePhysicalSpinCurrentThreeForm source 0 joint.1
    (withCoframe
      (toContinuumPointField configuration joint.1) joint.2)

/-- Re-inserting the actual coframe recovers the exact W13 response generated
from that actual.  This is a readout identity, not a response equation. -/
theorem diracDualFormNativeActionSpinResponseAt_eq_pointCoframe
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    diracDualFormNativeActionSpinResponseAt source configuration point =
      diracDualFormNativeActionSpinResponsePointCoframe
        source configuration (point, configuration.coframe point) := by
  ext internalPair triple
  change
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus configuration) point)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (withCoframe (toContinuumPointField configuration point)
            (configuration.coframe point))
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair))
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  rfl

/-- A response from another actual may be represented on the exposed
point--coframe carrier exactly when the three primitive fields consumed by
W13 agree at that contact. -/
theorem
    diracDualFormNativeActionSpinResponseAt_eq_pointCoframe_of_fields_at
    (source : SmoothUnifiedSource)
    (actual carrier : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (coframeEqual : actual.coframe point = candidate)
    (matterEqual : actual.matter point = carrier.matter point)
    (conjugateEqual :
      actual.conjugateMatter point = carrier.conjugateMatter point) :
    diracDualFormNativeActionSpinResponseAt source actual point =
      diracDualFormNativeActionSpinResponsePointCoframe
        source carrier (point, candidate) := by
  ext internalPair triple
  change
    -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (toContinuumPointField
            (restrictHolonomicConfigurationToIIPlus actual) point)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair)) =
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 point
          (withCoframe (toContinuumPointField carrier point) candidate)
          (loweredLorentzBivectorOneFormCoordinate
            (missingTripleOfOneForm triple) internalPair))
  rw [formNativeLorentzMatterFirstCoefficient_restrictToIIPlus]
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField,
    matterDualFrameRelative_zeroChart_local,
    matterDerivativeFrameRelative_zeroChart]
  rw [coframeEqual, matterEqual, conjugateEqual]

/-- Joint point--coframe regularity of one action coefficient.  At chart zero
the source frame is normalized, so the only coframe dependencies are the live
volume and inverse-coframe Dirac gamma. -/
theorem
    formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt_of_local_order
    {n : WithTop ℕ∞}
    (orderLeSmooth : n ≤ ∞)
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (direction : LorentzBivectorOneForm)
    (matterSmoothAt : ContDiffAt ℝ n
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateSmoothAt : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ n
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction)
      (point, candidate) := by
  let variation := fun joint : BasePoint × LorentzianCoframe =>
    fun formDirection : LorentzianIndex =>
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm direction) formDirection)
        (configuration.matter joint.1)
  let vector := fun joint : BasePoint × LorentzianCoframe =>
    Complex.I •
      ∑ formDirection : LorentzianIndex,
        diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } formDirection)
          (variation joint formDirection)
  have matterSmooth : ContDiffAt ℝ n (fun joint :
      BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (configuration.matter joint.1))
      (point, candidate) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (configuration.matter joint.1)) =
      (fun target => matterCoordinateEquiv (configuration.matter target)) ∘
        (fun joint : BasePoint × LorentzianCoframe => joint.1) by rfl]
    exact matterSmoothAt.comp (point, candidate) contDiffAt_fst
  have variationSmooth (formDirection : LorentzianIndex) :
      ContDiffAt ℝ n (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (variation joint formDirection))
        (point, candidate) := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp (point, candidate)
        (contDiffAt_const : ContDiffAt ℝ n (fun _ :
          BasePoint × LorentzianCoframe =>
            diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm direction)
              formDirection) (point, candidate))).clm_apply matterSmooth
    change ContDiffAt ℝ n (fun joint : BasePoint × LorentzianCoframe =>
      matterCoordinateEquiv
        (diracMatrixMatterAction
          (diracSpinConnectionLift
            (lorentzSkewConnectionOfBivectorOneForm direction) formDirection)
          (matterCoordinateEquiv.symm
            (matterCoordinateEquiv (configuration.matter joint.1)))))
      (point, candidate) at actual
    simpa only [variation, matterCoordinateEquiv.symm_apply_apply] using actual
  have gammaSmooth (formDirection : LorentzianIndex) :
      ContDiffAt ℝ n
        (fun joint : BasePoint × LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } formDirection)
        (point, candidate) := by
    rw [show (fun joint : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } formDirection) =
      (fun coframe : LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := coframe, derivative := 0 } formDirection) ∘
        (fun joint : BasePoint × LorentzianCoframe => joint.2) by rfl]
    exact
      ((inverseCoframeDiracGamma_contDiffAt candidate
        candidateNondegenerate formDirection).of_le orderLeSmooth).comp
          (point, candidate) contDiffAt_snd
  have kineticDirectionSmooth (formDirection : LorentzianIndex) :
      ContDiffAt ℝ n
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } formDirection)
              (variation joint formDirection)))
        (point, candidate) := by
    have actual :=
      (diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap.contDiff
        |>.contDiffAt.comp (point, candidate) (gammaSmooth formDirection)
        ).clm_apply (variationSmooth formDirection)
    change ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.2, derivative := 0 } formDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (variation joint formDirection)))))
      (point, candidate) at actual
    simpa only [matterCoordinateEquiv.symm_apply_apply] using actual
  have vectorCoordinateSmooth : ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector joint)) (point, candidate) := by
    have withISmooth : ContDiffAt ℝ n
        (fun joint : BasePoint × LorentzianCoframe =>
          Complex.I •
            ∑ formDirection : LorentzianIndex,
              matterCoordinateEquiv
                (diracMatrixMatterAction
                  (inverseCoframeDiracGamma
                    { coframe := joint.2, derivative := 0 } formDirection)
                  (variation joint formDirection)))
        (point, candidate) :=
      (contDiffAt_const : ContDiffAt ℝ n
        (fun _ : BasePoint × LorentzianCoframe => (Complex.I : ℂ))
        (point, candidate)).smul
          (ContDiffAt.sum fun formDirection _ =>
            kineticDirectionSmooth formDirection)
    dsimp only [vector]
    simpa only [map_sum, map_smul] using withISmooth
  have dualCoordinateSmooth (index : MatterCoordinateIndex) :
      ContDiffAt ℝ n (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ))))
        (point, candidate) :=
    (conjugateSmoothAt index).comp (point, candidate) contDiffAt_fst
  have pairingSumSmooth : ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector joint) index *
            configuration.conjugateMatter joint.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))))
      (point, candidate) := by
    apply ContDiffAt.sum
    intro index _
    have vectorEntrySmooth : ContDiffAt ℝ n
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector joint) index)
        (point, candidate) := by
      fun_prop
    exact vectorEntrySmooth.mul (dualCoordinateSmooth index)
  have dualPairingSmooth : ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint))
      (point, candidate) := by
    rw [show (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint)) =
      fun joint =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector joint) index *
            configuration.conjugateMatter joint.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))) by
      funext joint
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion
          (configuration.conjugateMatter joint.1)
          (matterCoordinateEquiv (vector joint))]
    exact pairingSumSmooth
  have realPairingSmooth : ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        (configuration.conjugateMatter joint.1 (vector joint)).re)
      (point, candidate) :=
    Complex.reCLM.contDiff.contDiffAt.comp
      (point, candidate) dualPairingSmooth
  have volumeSmooth : ContDiffAt ℝ n
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2)) (point, candidate) :=
    ((coframe_volume_contDiffAt candidate candidateNondegenerate).of_le
      orderLeSmooth).comp
      (point, candidate) contDiffAt_snd
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField,
    matterDualFrameRelative_zeroChart_local,
    matterDerivativeFrameRelative_zeroChart]
  change ContDiffAt ℝ n
    (fun joint : BasePoint × LorentzianCoframe =>
      abs (Matrix.det joint.2) *
        (configuration.conjugateMatter joint.1 (vector joint)).re)
    (point, candidate)
  exact volumeSmooth.mul realPairingSmooth

/-- Infinite-order convenience specialization of the order-parametric local
point--coframe coefficient theorem. -/
theorem
    formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (direction : LorentzBivectorOneForm)
    (matterSmoothAt : ContDiffAt ℝ ∞
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateSmoothAt : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ ∞
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction)
      (point, candidate) :=
  formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt_of_local_order
    le_rfl source configuration point candidate candidateNondegenerate direction
    matterSmoothAt conjugateSmoothAt

/-- First-germ version of the point--coframe W13 coefficient calculus.

The action coefficient only consumes the differentiability of the actual
matter and dual-matter coordinates at the judged occurrence.  This is the
correct mouth for a generated temporal primitive whose first germ is known
without assuming a global `Smooth` receipt for the surrounding current. -/
theorem
    formNativeLorentzMatterFirstCoefficient_pointCoframe_differentiableAt_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (direction : LorentzBivectorOneForm)
    (matterDifferentiableAt : DifferentiableAt ℝ
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateDifferentiableAt : ∀ index : MatterCoordinateIndex,
      DifferentiableAt ℝ
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction)
      (point, candidate) := by
  let variation := fun joint : BasePoint × LorentzianCoframe =>
    fun formDirection : LorentzianIndex =>
      diracMatrixMatterAction
        (diracSpinConnectionLift
          (lorentzSkewConnectionOfBivectorOneForm direction) formDirection)
        (configuration.matter joint.1)
  let vector := fun joint : BasePoint × LorentzianCoframe =>
    Complex.I •
      ∑ formDirection : LorentzianIndex,
        diracMatrixMatterAction
          (inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } formDirection)
          (variation joint formDirection)
  have matterDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (configuration.matter joint.1))
      (point, candidate) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (configuration.matter joint.1)) =
      (fun target => matterCoordinateEquiv (configuration.matter target)) ∘
        (fun joint : BasePoint × LorentzianCoframe => joint.1) by rfl]
    exact matterDifferentiableAt.comp
      (point, candidate) differentiableAt_fst
  have variationDifferentiable (formDirection : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (variation joint formDirection))
        (point, candidate) := by
    let bilinear :=
      diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
    let matrix : BasePoint × LorentzianCoframe → DiracMatrix := fun _ =>
      diracSpinConnectionLift
        (lorentzSkewConnectionOfBivectorOneForm direction) formDirection
    have matrixDifferentiable : DifferentiableAt ℝ matrix
        (point, candidate) := differentiableAt_const _
    have outerDerivative : HasFDerivAt
        (fun joint => bilinear (matrix joint))
        (bilinear.comp (fderiv ℝ matrix (point, candidate)))
        (point, candidate) :=
      bilinear.hasFDerivAt.comp (point, candidate)
        matrixDifferentiable.hasFDerivAt
    have total :=
      (outerDerivative.clm_apply matterDifferentiable.hasFDerivAt
        ).differentiableAt
    change DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (diracSpinConnectionLift
              (lorentzSkewConnectionOfBivectorOneForm direction)
                formDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (configuration.matter joint.1)))))
      (point, candidate) at total
    simpa only [variation, matterCoordinateEquiv.symm_apply_apply] using total
  have gammaDifferentiable (formDirection : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } formDirection)
        (point, candidate) :=
    ((inverseCoframeDiracGamma_contDiffAt candidate
      candidateNondegenerate formDirection).comp
        (point, candidate) contDiffAt_snd).differentiableAt (by simp)
  have kineticDirectionDifferentiable (formDirection : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } formDirection)
              (variation joint formDirection)))
        (point, candidate) := by
    let bilinear :=
      diracMatrixMatterCoordinateRealBilinear.toContinuousBilinearMap
    have outerDerivative : HasFDerivAt
        (fun joint => bilinear
          (inverseCoframeDiracGamma
            { coframe := joint.2, derivative := 0 } formDirection))
        (bilinear.comp
          (fderiv ℝ
            (fun joint : BasePoint × LorentzianCoframe =>
              inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } formDirection)
            (point, candidate)))
        (point, candidate) :=
      bilinear.hasFDerivAt.comp (point, candidate)
        (gammaDifferentiable formDirection).hasFDerivAt
    have total :=
      (outerDerivative.clm_apply
        (variationDifferentiable formDirection).hasFDerivAt).differentiableAt
    change DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv
          (diracMatrixMatterAction
            (inverseCoframeDiracGamma
              { coframe := joint.2, derivative := 0 } formDirection)
            (matterCoordinateEquiv.symm
              (matterCoordinateEquiv (variation joint formDirection)))))
      (point, candidate) at total
    simpa only [matterCoordinateEquiv.symm_apply_apply] using total
  have vectorCoordinateDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector joint)) (point, candidate) := by
    have sumDifferentiable : DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          ∑ formDirection : LorentzianIndex,
            matterCoordinateEquiv
              (diracMatrixMatterAction
                (inverseCoframeDiracGamma
                  { coframe := joint.2, derivative := 0 } formDirection)
                (variation joint formDirection)))
        (point, candidate) :=
      DifferentiableAt.fun_sum fun formDirection _ =>
        kineticDirectionDifferentiable formDirection
    let iSmul : MatterCoordinateCarrier →L[ℝ] MatterCoordinateCarrier :=
      ContinuousLinearMap.lsmul ℝ ℂ Complex.I
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector joint)) =
      fun joint => iSmul
        (∑ formDirection : LorentzianIndex,
          matterCoordinateEquiv
            (diracMatrixMatterAction
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 } formDirection)
              (variation joint formDirection))) by
      funext joint
      simp [vector, iSmul]
      rw [Finset.smul_sum]]
    exact iSmul.differentiableAt.comp
      (point, candidate) sumDifferentiable
  have dualCoordinateDifferentiable (index : MatterCoordinateIndex) :
      DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          configuration.conjugateMatter joint.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
      (point, candidate) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) =
      (fun target =>
        configuration.conjugateMatter target
          (matterCoordinateEquiv.symm
            (EuclideanSpace.single index (1 : ℂ)))) ∘
        (fun joint : BasePoint × LorentzianCoframe => joint.1) by rfl]
    exact (conjugateDifferentiableAt index).comp
      (point, candidate) differentiableAt_fst
  have pairingSumDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector joint) index *
            configuration.conjugateMatter joint.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))))
      (point, candidate) := by
    apply DifferentiableAt.fun_sum
    intro index _
    have vectorEntryDifferentiable : DifferentiableAt ℝ
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector joint) index)
        (point, candidate) := by
      fun_prop
    exact vectorEntryDifferentiable.mul
      (dualCoordinateDifferentiable index)
  have dualPairingDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint))
      (point, candidate) := by
    rw [show (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint)) =
      fun joint =>
        ∑ index : MatterCoordinateIndex,
          matterCoordinateEquiv (vector joint) index *
            configuration.conjugateMatter joint.1
              (matterCoordinateEquiv.symm
                (EuclideanSpace.single index (1 : ℂ))) by
      funext joint
      simpa only [matterCoordinateEquiv.symm_apply_apply] using
        coframeMatterDual_coordinate_expansion
          (configuration.conjugateMatter joint.1)
          (matterCoordinateEquiv (vector joint))]
    exact pairingSumDifferentiable
  have realPairingDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        (configuration.conjugateMatter joint.1 (vector joint)).re)
      (point, candidate) :=
    Complex.reCLM.differentiableAt.comp
      (point, candidate) dualPairingDifferentiable
  have volumeDifferentiable : DifferentiableAt ℝ
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2)) (point, candidate) :=
    ((coframe_volume_contDiffAt candidate candidateNondegenerate).comp
      (point, candidate) contDiffAt_snd).differentiableAt (by simp)
  unfold formNativeLorentzMatterFirstCoefficient
    matterCovariantDerivativeFirstVariationDensity
    matterCovariantDerivativeVariationVector
    matterCovariantDerivativeKineticSum
    pointwiseMatterLorentzConnectionVariation
    generatedVolumeDensity
  simp only [withCoframe, toContinuumPointField,
    matterDualFrameRelative_zeroChart_local,
    matterDerivativeFrameRelative_zeroChart]
  change DifferentiableAt ℝ
    (fun joint : BasePoint × LorentzianCoframe =>
      abs (Matrix.det joint.2) *
        (configuration.conjugateMatter joint.1 (vector joint)).re)
    (point, candidate)
  exact volumeDifferentiable.mul realPairingDifferentiable

/-- Local first-germ regularity of the complete W13 response. -/
theorem
    diracDualFormNativeActionSpinResponsePointCoframe_differentiableAt_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (matterDifferentiableAt : DifferentiableAt ℝ
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateDifferentiableAt : ∀ index : MatterCoordinateIndex,
      DifferentiableAt ℝ
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    DifferentiableAt ℝ
      (diracDualFormNativeActionSpinResponsePointCoframe
        source configuration) (point, candidate) := by
  apply differentiableAt_pi.mpr
  intro internalPair
  apply differentiableAt_pi.mpr
  intro triple
  let direction :=
    loweredLorentzBivectorOneFormCoordinate
      (missingTripleOfOneForm triple) internalPair
  have coefficientDifferentiable :=
    formNativeLorentzMatterFirstCoefficient_pointCoframe_differentiableAt_of_local
      source configuration point candidate candidateNondegenerate direction
      matterDifferentiableAt conjugateDifferentiableAt
  change DifferentiableAt ℝ
    (fun joint : BasePoint × LorentzianCoframe =>
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction))
    (point, candidate)
  exact ((differentiableAt_const (c :=
    oneWedgeThreeSign (missingTripleOfOneForm triple))).mul
      coefficientDifferentiable).neg

/-- Global-smoothness convenience wrapper for the local W13 coefficient
regularity theorem. -/
theorem
    formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (direction : LorentzBivectorOneForm) :
    ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction)
      (point, candidate) :=
  formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt_of_local
    source configuration point candidate candidateNondegenerate direction
    smooth.2.2.2.2.2.2.2.1.contDiffAt
    (fun index => smooth.2.2.2.2.2.2.2.2 index |>.contDiffAt)

/-- Order-parametric local-data form of the full W13 response regularity
theorem.  In particular, value-continuous matter and dual matter produce a
value-continuous Cartan spin response without requiring a global smoothness
receipt for the surrounding current. -/
theorem
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local_order
    {n : WithTop ℕ∞}
    (orderLeSmooth : n ≤ ∞)
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (matterSmoothAt : ContDiffAt ℝ n
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateSmoothAt : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ n
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ n
      (diracDualFormNativeActionSpinResponsePointCoframe
        source configuration) (point, candidate) := by
  apply contDiffAt_pi'
  intro internalPair
  apply contDiffAt_pi'
  intro triple
  let direction :=
    loweredLorentzBivectorOneFormCoordinate
      (missingTripleOfOneForm triple) internalPair
  have coefficientSmooth :=
    formNativeLorentzMatterFirstCoefficient_pointCoframe_contDiffAt_of_local_order
      orderLeSmooth source configuration point candidate
      candidateNondegenerate direction matterSmoothAt conjugateSmoothAt
  change ContDiffAt ℝ n
    (fun joint : BasePoint × LorentzianCoframe =>
      -(oneWedgeThreeSign (missingTripleOfOneForm triple) *
        formNativeLorentzMatterFirstCoefficient source 0 joint.1
          (withCoframe
            (toContinuumPointField configuration joint.1) joint.2)
          direction))
    (point, candidate)
  exact (contDiffAt_const.mul coefficientSmooth).neg

/-- Local smooth-data specialization of the order-parametric W13 response
regularity theorem. -/
theorem
    diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (matterSmoothAt : ContDiffAt ℝ ∞
      (fun target => matterCoordinateEquiv (configuration.matter target))
      point)
    (conjugateSmoothAt : ∀ index : MatterCoordinateIndex,
      ContDiffAt ℝ ∞
        (fun target =>
          configuration.conjugateMatter target
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        point) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        source configuration) (point, candidate) :=
  diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local_order
    le_rfl source configuration point candidate candidateNondegenerate
    matterSmoothAt conjugateSmoothAt

/-- The full W13 response is jointly smooth in the point and the exposed
coframe on the nondegenerate contact. -/
theorem diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint) (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0) :
    ContDiffAt ℝ ∞
      (diracDualFormNativeActionSpinResponsePointCoframe
        source configuration) (point, candidate) :=
  diracDualFormNativeActionSpinResponsePointCoframe_contDiffAt_of_local
    source configuration point candidate candidateNondegenerate
    smooth.2.2.2.2.2.2.2.1.contDiffAt
    (fun index => smooth.2.2.2.2.2.2.2.2 index |>.contDiffAt)

/-! ## Algebraic KIN-3/KIN-2 regularity -/

/-- One component of the no-choice algebraic Cartan response

`(e, J) ↦ K(e, T(e, J))`.

The carrier contains only the coframe and the W13 response actually consumed
by KIN-3/KIN-2. -/
def cartanContorsionCoframeResponseComponent
    (formDirection : LorentzianIndex) (internalPair : Fin 6)
    (carrier : LorentzianCoframe × PhysicalBivectorThreeForm) : ℝ :=
  contorsionOfCartanTorsion carrier.1
    (cartanTorsionOfThreeForm carrier.1 carrier.2)
    formDirection internalPair

/-- The finite KIN-3/KIN-2 response map is differentiable at every
nondegenerate coframe fiber.  Matrix inversion is the only non-polynomial
operation; every other step is a finite sum/product or coordinate
projection. -/
theorem cartanContorsionCoframeResponseComponent_differentiableAt
    (coframe : LorentzianCoframe)
    (response : PhysicalBivectorThreeForm)
    (nondegenerate : Matrix.det coframe ≠ 0)
    (formDirection : LorentzianIndex) (internalPair : Fin 6) :
    DifferentiableAt ℝ
      (cartanContorsionCoframeResponseComponent
        formDirection internalPair) (coframe, response) := by
  have inverseEntryDifferentiable
      (row column : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          carrier.1⁻¹ row column)
        (coframe, response) := by
    exact
      ((contDiffAt_pi.mp
        (contDiffAt_pi.mp
          (coframe_inv_contDiffAt coframe nondegenerate) row) column).comp
        (coframe, response) contDiffAt_fst).differentiableAt
          (by simp)
  have undualEntryDifferentiable
      (pair : Fin 6) (triple : Fin 4) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          internalBivectorUndualThreeForm carrier.2 pair triple)
        (coframe, response) := by
    fin_cases pair <;>
      simp [internalBivectorUndualThreeForm,
        lorentzianCoframeHodge] <;>
      fun_prop
  have orderedUndualDifferentiable
      (internalFirst internalSecond first second third : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          orderedPhysicalBivectorThreeFormComponent
            (internalBivectorUndualThreeForm carrier.2)
            internalFirst internalSecond first second third)
        (coframe, response) := by
    unfold orderedPhysicalBivectorThreeFormComponent
      orderedInternalBivectorThreeFormComponent
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro triple _
    apply DifferentiableAt.mul
    · refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
      intro pair _
      exact (undualEntryDifferentiable pair triple).mul
        (by fun_prop)
    · fun_prop
  have firstContractionDifferentiable
      (internal first second : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanThreeFormFirstContraction carrier.1
            (internalBivectorUndualThreeForm carrier.2)
            internal first second)
        (coframe, response) := by
    unfold cartanThreeFormFirstContraction
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro contractedInternal _
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro direction _
    exact (inverseEntryDifferentiable direction contractedInternal).mul
      (orderedUndualDifferentiable internal contractedInternal
        direction first second)
  have doubleContractionDifferentiable
      (direction : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanThreeFormDoubleContraction carrier.1
            (internalBivectorUndualThreeForm carrier.2) direction)
        (coframe, response) := by
    unfold cartanThreeFormDoubleContraction
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro internal _
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro spacetime _
    exact (inverseEntryDifferentiable spacetime internal).mul
      (firstContractionDifferentiable internal spacetime direction)
  have torsionEntryDifferentiable
      (pair : Fin 6) (internal : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          cartanTorsionOfThreeForm carrier.1 carrier.2 pair internal)
        (coframe, response) := by
    unfold cartanTorsionOfThreeForm
      cartanTorsionOfUndualThreeForm
    apply DifferentiableAt.add
    · exact firstContractionDifferentiable internal
        (pairFirst pair) (pairSecond pair)
    · apply DifferentiableAt.mul (by fun_prop)
      apply DifferentiableAt.sub
      · exact
          (doubleContractionDifferentiable (pairFirst pair)).mul
            (by fun_prop)
      · exact
          (doubleContractionDifferentiable (pairSecond pair)).mul
            (by fun_prop)
  have pulledTorsionEntryDifferentiable
      (framePair : Fin 6) (internal : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          pullbackCartanTorsionTwoForm carrier.1
            (cartanTorsionOfThreeForm carrier.1 carrier.2)
            framePair internal)
        (coframe, response) := by
    unfold pullbackCartanTorsionTwoForm coframeTwoFormLinear
      coframeWedge
    simp only [Matrix.transpose_apply]
    change DifferentiableAt ℝ
      (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
        ∑ spacetimePair : Fin 6,
          (carrier.1⁻¹ (pairFirst spacetimePair) (pairFirst framePair) *
                carrier.1⁻¹ (pairSecond spacetimePair)
                  (pairSecond framePair) -
              carrier.1⁻¹ (pairSecond spacetimePair) (pairFirst framePair) *
                carrier.1⁻¹ (pairFirst spacetimePair)
                  (pairSecond framePair)) *
            cartanTorsionOfThreeForm carrier.1 carrier.2
              spacetimePair internal)
      (coframe, response)
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro spacetimePair _
    apply DifferentiableAt.mul
    · apply DifferentiableAt.sub
      · exact
          (inverseEntryDifferentiable
            (pairFirst spacetimePair) (pairFirst framePair)).mul
            (inverseEntryDifferentiable
              (pairSecond spacetimePair) (pairSecond framePair))
      · exact
          (inverseEntryDifferentiable
            (pairSecond spacetimePair) (pairFirst framePair)).mul
            (inverseEntryDifferentiable
              (pairFirst spacetimePair) (pairSecond framePair))
    · exact torsionEntryDifferentiable spacetimePair internal
  have raisedPulledTorsionEntryDifferentiable
      (framePair : Fin 6) (internal : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          minkowskiRaiseCartanTorsion
            (pullbackCartanTorsionTwoForm carrier.1
              (cartanTorsionOfThreeForm carrier.1 carrier.2))
            framePair internal)
        (coframe, response) := by
    unfold minkowskiRaiseCartanTorsion
    apply DifferentiableAt.mul
    · fun_prop
    · exact pulledTorsionEntryDifferentiable framePair internal
  have orderedRaisedTorsionDifferentiable
      (internal first second : LorentzianIndex) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          orderedCartanTorsionComponent
            (minkowskiRaiseCartanTorsion
              (pullbackCartanTorsionTwoForm carrier.1
                (cartanTorsionOfThreeForm carrier.1 carrier.2)))
            internal first second)
        (coframe, response) := by
    unfold orderedCartanTorsionComponent
    refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
    intro pair _
    exact (raisedPulledTorsionEntryDifferentiable pair internal).mul
      (by fun_prop)
  have internalContorsionEntryDifferentiable
      (internalDirection : LorentzianIndex) (pair : Fin 6) :
      DifferentiableAt ℝ
        (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
          internalFrameContorsionOfTorsion
            (minkowskiRaiseCartanTorsion
              (pullbackCartanTorsionTwoForm carrier.1
                (cartanTorsionOfThreeForm carrier.1 carrier.2)))
            internalDirection pair)
        (coframe, response) := by
    unfold internalFrameContorsionOfTorsion
    apply DifferentiableAt.mul (by fun_prop)
    exact
      ((orderedRaisedTorsionDifferentiable
          (pairFirst pair) internalDirection (pairSecond pair)).sub
        (orderedRaisedTorsionDifferentiable
          internalDirection (pairSecond pair) (pairFirst pair))).add
        (orderedRaisedTorsionDifferentiable
          (pairSecond pair) (pairFirst pair) internalDirection)
  unfold cartanContorsionCoframeResponseComponent
    contorsionOfCartanTorsion
    pushforwardLorentzBivectorOneForm
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  refine DifferentiableAt.fun_sum (u := Finset.univ) ?_
  intro internalDirection _
  exact (by fun_prop : DifferentiableAt ℝ
      (fun carrier : LorentzianCoframe × PhysicalBivectorThreeForm =>
        carrier.1 internalDirection formDirection) (coframe, response)).mul
    (internalContorsionEntryDifferentiable internalDirection internalPair)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCartanPointCoframeRegularity
