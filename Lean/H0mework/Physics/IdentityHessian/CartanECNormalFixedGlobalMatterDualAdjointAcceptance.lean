import H0mework.Physics.Coframe.CoframeScalarMatterRegularity
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalMatterDualFullCauchyActual

/-!
# Fixed KIN-16 matter-dual Euler--Lagrange acceptance

This module reads the densitized adjoint matter equation from the already
generated fixed P506/L0 matter-dual/full-EC successor.  The final actual has
identity coframe value and zero complete coframe first jet at the common
contact.  A proof-only identity-coframe comparison therefore has the same
first-order matter momentum there.

The comparison is used only to interpret the existing adjoint action law.
No Euler--Lagrange residual, target derivative, nondegeneracy receipt, branch,
or response coefficient is fed into the physical constructor.  In
particular, this module proves only a fixed-contact readout; it does not claim
global nondegeneracy or a continuous on-shell trajectory.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineCoframeVariation
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineHolonomicIdentityCoframeConjugateMatterActionAcceptance
open StageNineHolonomicIdentityCoframeConjugateMatterActionResponse
open StageNineMatterActionTemporalFirstGermResponse
open StageNineMatterPointwiseEquation
open StageNineMatterVariation
open StageNineP286ActionCauchySplit
open StageNineP286GaugeConnectionMomentumRegularity

open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

local instance fixedMatterDualAcceptanceMatterCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev FixedMatterDualActual : StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalFixedGlobalMatterDualFullCauchyActual

/-! ## Proof-only identity-coframe acceptance -/

def fixedGlobalMatterDualIdentityCoframeComparison :
    StageNineHolonomicConfiguration :=
  identityCoframeComparison FixedMatterDualActual

theorem fixedGlobalMatterDualIdentityCoframeComparison_smooth :
    fixedGlobalMatterDualIdentityCoframeComparison.Smooth :=
  identityCoframeComparison_smooth FixedMatterDualActual
    fixedGlobalMatterDualFullCauchy_smooth

theorem fixedGlobalMatterDualIdentityCoframeComparison_hasIdentityCoframe :
    HasIdentityCoframe fixedGlobalMatterDualIdentityCoframeComparison :=
  identityCoframeComparison_hasIdentityCoframe FixedMatterDualActual

theorem fixedGlobalMatterDualIdentityCoframeComparison_actionLaw :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      fixedGlobalMatterDualIdentityCoframeComparison 0
      (holonomicConjugateMatterDerivativeDual
        fixedGlobalMatterDualIdentityCoframeComparison 0
        canonicalLorentzianTimeDirection) := by
  apply
    (identityCoframeComparison_timeActionLaw_iff
      FixedMatterDualActual 0 _).2
  change
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
      FixedMatterDualActual 0
      (holonomicConjugateMatterDerivativeDual
        FixedMatterDualActual 0 canonicalLorentzianTimeDirection)
  exact fixedGlobalMatterDualFullCauchy_adjointActionLaw

theorem fixedGlobalMatterDualIdentityCoframeComparison_matterEuler_origin
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        fixedGlobalMatterDualIdentityCoframeComparison direction 0 =
      0 := by
  exact
    holonomicIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw
      positiveSmoothUnifiedSource
      fixedGlobalMatterDualIdentityCoframeComparison
      fixedGlobalMatterDualIdentityCoframeComparison_smooth
      fixedGlobalMatterDualIdentityCoframeComparison_hasIdentityCoframe
      0 fixedGlobalMatterDualIdentityCoframeComparison_actionLaw direction

/-! ## Point--coframe first-order momentum carrier -/

/-- The differential matter momentum with the spacetime point and coframe
exposed as one finite-dimensional carrier.  This helper is consumed directly
by the fixed-lineage theorem below. -/
def matterDifferentialMomentumPointCoframe
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex)
    (joint : BasePoint × LorentzianCoframe) : ℝ :=
  generatedVolumeDensity
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2) *
    (configuration.conjugateMatter joint.1
      (matterDifferentialVariationVector source joint.1
        (withCoframe
          (toContinuumPointField configuration joint.1) joint.2)
        direction derivativeDirection)).re

theorem matterDifferentialMomentumPointCoframe_contDiffAt
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (smooth : configuration.Smooth)
    (point : BasePoint)
    (candidate : LorentzianCoframe)
    (candidateNondegenerate : Matrix.det candidate ≠ 0)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (matterDifferentialMomentumPointCoframe source configuration
        direction derivativeDirection)
      (point, candidate) := by
  let vector := fun joint : BasePoint × LorentzianCoframe =>
    matterDifferentialVariationVector source joint.1
      (withCoframe
        (toContinuumPointField configuration joint.1) joint.2)
      direction derivativeDirection
  have gammaSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } derivativeDirection)
      (point, candidate) := by
    have outer :=
      inverseCoframeDiracGamma_contDiffAt
        candidate candidateNondegenerate derivativeDirection
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
        inverseCoframeDiracGamma
          { coframe := joint.2, derivative := 0 } derivativeDirection) =
        (fun candidate : LorentzianCoframe =>
          inverseCoframeDiracGamma
          { coframe := candidate, derivative := 0 } derivativeDirection) ∘
        (fun joint : BasePoint × LorentzianCoframe => joint.2) by
      rfl]
    exact outer.comp (point, candidate) contDiffAt_snd
  have vectorCoordinateSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        matterCoordinateEquiv (vector joint))
      (point, candidate) := by
    have actionSmooth :=
      (StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear
        |>.toContinuousBilinearMap.contDiff.contDiffAt.comp
          (point, candidate) gammaSmooth).clm_apply
        (contDiffAt_const :
          ContDiffAt ℝ ∞
            (fun _ : BasePoint × LorentzianCoframe => direction)
            (point, candidate))
    have withISmooth : ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe =>
          Complex.I •
            StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear
              (inverseCoframeDiracGamma
                { coframe := joint.2, derivative := 0 }
                derivativeDirection)
              direction)
        (point, candidate) :=
      (contDiffAt_const :
        ContDiffAt ℝ ∞
          (fun _ : BasePoint × LorentzianCoframe => (Complex.I : ℂ))
          (point, candidate)).smul actionSmooth
    simpa only [vector, matterDifferentialVariationVector, withCoframe,
      StageNineDiracMatterCoordinateCalculus.diracMatrixMatterCoordinateRealBilinear_apply,
      map_smul] using withISmooth
  have pairingSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        configuration.conjugateMatter joint.1 (vector joint))
      (point, candidate) := by
    rw [show
      (fun joint : BasePoint × LorentzianCoframe =>
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
    apply ContDiffAt.sum
    intro index _
    let projection : MatterCoordinateCarrier →L[ℂ] ℂ :=
      (PiLp.projₗ (𝕜 := ℂ) 2
        (fun _ : MatterCoordinateIndex => ℂ) index).toContinuousLinearMap
    have vectorEntrySmooth : ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe =>
          matterCoordinateEquiv (vector joint) index)
        (point, candidate) := by
      change ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe =>
          (projection.restrictScalars ℝ)
            (matterCoordinateEquiv (vector joint)))
        (point, candidate)
      exact
        (projection.restrictScalars ℝ).contDiff.contDiffAt.comp
          (point, candidate) vectorCoordinateSmooth
    have dualEntrySmooth : ContDiffAt ℝ ∞
        (fun joint : BasePoint × LorentzianCoframe =>
          configuration.conjugateMatter joint.1
            (matterCoordinateEquiv.symm
              (EuclideanSpace.single index (1 : ℂ))))
        (point, candidate) :=
      (smooth.2.2.2.2.2.2.2.2 index).comp contDiff_fst |>.contDiffAt
    exact vectorEntrySmooth.mul dualEntrySmooth
  have volumeSmooth : ContDiffAt ℝ ∞
      (fun joint : BasePoint × LorentzianCoframe =>
        abs (Matrix.det joint.2))
      (point, candidate) :=
    (coframe_volume_contDiffAt candidate candidateNondegenerate).comp
      (point, candidate) contDiffAt_snd
  unfold matterDifferentialMomentumPointCoframe generatedVolumeDensity
  simp only [withCoframe]
  exact
    volumeSmooth.mul
      (Complex.reCLM.contDiff.contDiffAt.comp
        (point, candidate) pairingSmooth)

/-- Re-inserting an actual coframe into the exposed carrier recovers the
ordinary differential momentum exactly. -/
theorem matterDifferentialMomentum_eq_pointCoframe_actualSection
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentum source configuration direction
        derivativeDirection =
      matterDifferentialMomentumPointCoframe source configuration
          direction derivativeDirection ∘
        fun point => (point, configuration.coframe point) := by
  funext point
  unfold matterDifferentialMomentum
    matterDifferentialMomentumPointCoframe
  simp only [Function.comp_apply, withCoframe, toContinuumPointField]

/-- Replacing a configuration by its proof-only identity-coframe comparison
does not change the exposed point--coframe momentum family. -/
theorem
    matterDifferentialMomentumPointCoframe_identityCoframeComparison
    (source : SmoothUnifiedSource)
    (configuration : StageNineHolonomicConfiguration)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    matterDifferentialMomentumPointCoframe source
        (identityCoframeComparison configuration) direction
        derivativeDirection =
      matterDifferentialMomentumPointCoframe source configuration direction
        derivativeDirection := by
  funext joint
  unfold matterDifferentialMomentumPointCoframe
    identityCoframeComparison
  rfl

/-- Fixed specialization of the directly consumed joint momentum carrier. -/
def fixedGlobalMatterDualMomentumPointCoframe
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    BasePoint × LorentzianCoframe → ℝ :=
  matterDifferentialMomentumPointCoframe positiveSmoothUnifiedSource
    FixedMatterDualActual direction derivativeDirection

private theorem fixedGlobalMatterDualMomentumPointCoframe_contDiffAt
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fixedGlobalMatterDualMomentumPointCoframe
        direction derivativeDirection)
      (0, 1) := by
  exact
    matterDifferentialMomentumPointCoframe_contDiffAt
      positiveSmoothUnifiedSource FixedMatterDualActual
      fixedGlobalMatterDualFullCauchy_smooth 0 1 (by norm_num)
      direction derivativeDirection

private def fixedGlobalMatterDualCoordinateAxis
    (direction : LorentzianIndex) : ℝ → BasePoint :=
  fun parameter => parameter • coordinateDirection direction

private theorem fixedGlobalMatterDualCoordinateAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedGlobalMatterDualCoordinateAxis direction)
      (coordinateDirection direction) 0 := by
  let line :=
    fun parameter : ℝ =>
      parameter • coordinateDirection direction
  change HasDerivAt line (coordinateDirection direction) 0
  simpa [line] using
    (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
      (coordinateDirection direction)

private theorem fixedGlobalMatterDualFullCauchy_coframeAxis_hasDerivAt_zero
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter =>
        FixedMatterDualActual.coframe
          (fixedGlobalMatterDualCoordinateAxis direction parameter))
      0 0 := by
  have coframeDifferentiable :
      DifferentiableAt ℝ FixedMatterDualActual.coframe 0 :=
    ((holonomicCoframe_contDiff FixedMatterDualActual
      fixedGlobalMatterDualFullCauchy_smooth).differentiable (by simp))
      |>.differentiableAt
  have coframeOuter :
      HasFDerivAt FixedMatterDualActual.coframe
        (fderiv ℝ FixedMatterDualActual.coframe 0)
        (fixedGlobalMatterDualCoordinateAxis direction 0) := by
    simpa [fixedGlobalMatterDualCoordinateAxis] using
      coframeDifferentiable.hasFDerivAt
  have composed :=
    coframeOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualCoordinateAxis_hasDerivAt direction)
  have derivativeZero :
      (fderiv ℝ FixedMatterDualActual.coframe 0)
          (coordinateDirection direction) =
        0 := by
    ext internal coordinate
    let evaluation : LorentzianCoframe →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj coordinate :
          (LorentzianIndex → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.proj internal :
          LorentzianCoframe →L[ℝ] (LorentzianIndex → ℝ))
    have evaluatedDerivative :
        HasFDerivAt
          (fun point : BasePoint =>
            evaluation (FixedMatterDualActual.coframe point))
          (evaluation.comp
            (fderiv ℝ FixedMatterDualActual.coframe 0)) 0 :=
      evaluation.hasFDerivAt.comp 0 coframeDifferentiable.hasFDerivAt
    have componentDerivativeZero :=
      congrArg
        (fun jet => jet.derivative direction internal coordinate)
        fixedGlobalMatterDualFullCauchy_coframeFirstJet_origin
    have evaluatedFunctionEquality :
        (fun point : BasePoint =>
          evaluation (FixedMatterDualActual.coframe point)) =
        (fun point : BasePoint =>
          FixedMatterDualActual.coframe point internal coordinate) := by
      funext point
      rfl
    have evaluatedZero :
        (fderiv ℝ
          (fun point : BasePoint =>
            evaluation (FixedMatterDualActual.coframe point)) 0)
            (coordinateDirection direction) =
          0 := by
      rw [evaluatedFunctionEquality]
      simpa [holonomicCoframeFirstJetAt,
        fieldDirectionalDerivative] using componentDerivativeZero
    rw [evaluatedDerivative.fderiv] at evaluatedZero
    change
      evaluation
          ((fderiv ℝ FixedMatterDualActual.coframe 0)
            (coordinateDirection direction)) =
        0 at evaluatedZero
    exact evaluatedZero
  apply composed.congr_deriv
  exact derivativeZero

/-- The fixed KIN-16 successor has zero coframe tangent along every canonical
coordinate axis at the common contact.  This public fixed-lineage seam is
consumed by later action operators whose principal depends on the live
coframe; it is not a generic regularity premise or a transported equation
receipt. -/
theorem fixedGlobalMatterDualFullCauchy_coframeCoordinateAxis_hasDerivAt_zero
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter : ℝ =>
        FixedMatterDualActual.coframe
          (parameter • coordinateDirection direction))
      0 0 := by
  simpa [fixedGlobalMatterDualCoordinateAxis] using
    fixedGlobalMatterDualFullCauchy_coframeAxis_hasDerivAt_zero direction

private def fixedGlobalMatterDualActualPointCoframeAxis
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    let point := fixedGlobalMatterDualCoordinateAxis direction parameter
    (point, FixedMatterDualActual.coframe point)

private def fixedGlobalMatterDualFrozenPointCoframeAxis
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    (fixedGlobalMatterDualCoordinateAxis direction parameter,
      (1 : LorentzianCoframe))

private theorem fixedGlobalMatterDualActualPointCoframeAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedGlobalMatterDualActualPointCoframeAxis direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedGlobalMatterDualCoordinateAxis_hasDerivAt direction).prodMk
      (fixedGlobalMatterDualFullCauchy_coframeAxis_hasDerivAt_zero
        direction)

private theorem fixedGlobalMatterDualFrozenPointCoframeAxis_hasDerivAt
    (direction : LorentzianIndex) :
    HasDerivAt (fixedGlobalMatterDualFrozenPointCoframeAxis direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedGlobalMatterDualCoordinateAxis_hasDerivAt direction).prodMk
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : LorentzianCoframe)))

theorem fixedGlobalMatterDualFullCauchy_matterMomentumDerivative_origin_eq_comparison
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          FixedMatterDualActual direction derivativeDirection)
        0 derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedGlobalMatterDualIdentityCoframeComparison
          direction derivativeDirection)
        0 derivativeDirection := by
  let outer :=
    fixedGlobalMatterDualMomentumPointCoframe
      direction derivativeDirection
  have outerDifferentiable : DifferentiableAt ℝ outer (0, 1) :=
    (fixedGlobalMatterDualMomentumPointCoframe_contDiffAt
      direction derivativeDirection).differentiableAt (by simp)
  have outerDerivative := outerDifferentiable.hasFDerivAt
  have actualAxisOrigin :
      fixedGlobalMatterDualActualPointCoframeAxis derivativeDirection 0 =
        (0, 1) := by
    simp [fixedGlobalMatterDualActualPointCoframeAxis,
      fixedGlobalMatterDualCoordinateAxis,
      fixedGlobalMatterDualFullCauchy_coframe_origin]
  have outerAtActual :
      HasFDerivAt outer (fderiv ℝ outer (0, 1))
        (fixedGlobalMatterDualActualPointCoframeAxis
          derivativeDirection 0) := by
    simpa only [actualAxisOrigin] using outerDerivative
  have generatedActualAxis :=
    outerAtActual.comp_hasDerivAt 0
      (fixedGlobalMatterDualActualPointCoframeAxis_hasDerivAt
        derivativeDirection)
  have frozenAxisOrigin :
      fixedGlobalMatterDualFrozenPointCoframeAxis derivativeDirection 0 =
        (0, 1) := by
    simp [fixedGlobalMatterDualFrozenPointCoframeAxis,
      fixedGlobalMatterDualCoordinateAxis]
  have outerAtFrozen :
      HasFDerivAt outer (fderiv ℝ outer (0, 1))
        (fixedGlobalMatterDualFrozenPointCoframeAxis
          derivativeDirection 0) := by
    simpa only [frozenAxisOrigin] using outerDerivative
  have generatedFrozenAxis :=
    outerAtFrozen.comp_hasDerivAt 0
      (fixedGlobalMatterDualFrozenPointCoframeAxis_hasDerivAt
        derivativeDirection)
  have actualMomentumEquality :=
    matterDifferentialMomentum_eq_pointCoframe_actualSection
      positiveSmoothUnifiedSource FixedMatterDualActual direction
      derivativeDirection
  have comparisonMomentumEquality :=
    matterDifferentialMomentum_eq_pointCoframe_actualSection
      positiveSmoothUnifiedSource
      fixedGlobalMatterDualIdentityCoframeComparison direction
      derivativeDirection
  change
    matterDifferentialMomentum positiveSmoothUnifiedSource
        (identityCoframeComparison FixedMatterDualActual) direction
          derivativeDirection =
      matterDifferentialMomentumPointCoframe positiveSmoothUnifiedSource
          (identityCoframeComparison FixedMatterDualActual) direction
          derivativeDirection ∘
        fun point =>
          (point,
            (identityCoframeComparison FixedMatterDualActual).coframe point)
    at comparisonMomentumEquality
  rw [matterDifferentialMomentumPointCoframe_identityCoframeComparison
    positiveSmoothUnifiedSource FixedMatterDualActual direction
    derivativeDirection] at comparisonMomentumEquality
  have coframeSmooth : ContDiff ℝ ∞ FixedMatterDualActual.coframe :=
    holonomicCoframe_contDiff FixedMatterDualActual
      fixedGlobalMatterDualFullCauchy_smooth
  have actualSectionDifferentiable : DifferentiableAt ℝ
      (fun point : BasePoint => (point, FixedMatterDualActual.coframe point))
      0 :=
    differentiableAt_id.prodMk
      ((coframeSmooth.differentiable (by simp)).differentiableAt)
  have outerAtActualSection : DifferentiableAt ℝ outer
      (0, FixedMatterDualActual.coframe 0) := by
    simpa only [fixedGlobalMatterDualFullCauchy_coframe_origin] using
      outerDifferentiable
  have actualMomentumDifferentiable : DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        FixedMatterDualActual direction derivativeDirection) 0 := by
    rw [actualMomentumEquality]
    exact outerAtActualSection.comp 0 actualSectionDifferentiable
  have comparisonMomentumDifferentiable : DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        fixedGlobalMatterDualIdentityCoframeComparison direction
        derivativeDirection) 0 := by
    change DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        (identityCoframeComparison FixedMatterDualActual) direction
        derivativeDirection) 0
    rw [comparisonMomentumEquality]
    have comparisonCoframeDifferentiable :
        DifferentiableAt ℝ
          (identityCoframeComparison FixedMatterDualActual).coframe 0 := by
      rw [identityCoframeComparison_coframe]
      exact
        (differentiableAt_const (c := (1 : LorentzianCoframe)) :
          DifferentiableAt ℝ
            (fun _ : BasePoint => (1 : LorentzianCoframe)) 0)
    exact outerDifferentiable.comp 0
      (differentiableAt_id.prodMk comparisonCoframeDifferentiable)
  have actualMomentumOuter :
      HasFDerivAt
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          FixedMatterDualActual direction derivativeDirection)
        (fderiv ℝ
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            FixedMatterDualActual direction derivativeDirection) 0)
        (fixedGlobalMatterDualCoordinateAxis derivativeDirection 0) := by
    simpa [fixedGlobalMatterDualCoordinateAxis] using
      actualMomentumDifferentiable.hasFDerivAt
  have actualCoordinateDerivative :=
    actualMomentumOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualCoordinateAxis_hasDerivAt derivativeDirection)
  have comparisonMomentumOuter :
      HasFDerivAt
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedGlobalMatterDualIdentityCoframeComparison direction
            derivativeDirection)
        (fderiv ℝ
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            fixedGlobalMatterDualIdentityCoframeComparison direction
              derivativeDirection) 0)
        (fixedGlobalMatterDualCoordinateAxis derivativeDirection 0) := by
    simpa [fixedGlobalMatterDualCoordinateAxis] using
      comparisonMomentumDifferentiable.hasFDerivAt
  have comparisonCoordinateDerivative :=
    comparisonMomentumOuter.comp_hasDerivAt 0
      (fixedGlobalMatterDualCoordinateAxis_hasDerivAt derivativeDirection)
  have actualAxisFunctionEquality :
      (matterDifferentialMomentum positiveSmoothUnifiedSource
          FixedMatterDualActual direction derivativeDirection) ∘
          fixedGlobalMatterDualCoordinateAxis derivativeDirection =
        outer ∘
          fixedGlobalMatterDualActualPointCoframeAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun actualMomentumEquality
        (fixedGlobalMatterDualCoordinateAxis
          derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedGlobalMatterDualMomentumPointCoframe,
      fixedGlobalMatterDualActualPointCoframeAxis] using read
  have comparisonAxisFunctionEquality :
      (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedGlobalMatterDualIdentityCoframeComparison
            direction derivativeDirection) ∘
          fixedGlobalMatterDualCoordinateAxis derivativeDirection =
        outer ∘
          fixedGlobalMatterDualFrozenPointCoframeAxis
            derivativeDirection := by
    funext parameter
    have read :=
      congrFun comparisonMomentumEquality
        (fixedGlobalMatterDualCoordinateAxis
          derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedGlobalMatterDualMomentumPointCoframe,
      fixedGlobalMatterDualIdentityCoframeComparison,
      identityCoframeComparison_coframe,
      fixedGlobalMatterDualFrozenPointCoframeAxis] using read
  have actualCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedGlobalMatterDualActualPointCoframeAxis derivativeDirection)
        (fieldDirectionalDerivative
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            FixedMatterDualActual direction derivativeDirection)
          0 derivativeDirection)
        0 := by
    rw [← actualAxisFunctionEquality]
    exact actualCoordinateDerivative
  have comparisonCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedGlobalMatterDualFrozenPointCoframeAxis derivativeDirection)
        (fieldDirectionalDerivative
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            fixedGlobalMatterDualIdentityCoframeComparison
            direction derivativeDirection)
          0 derivativeDirection)
        0 := by
    rw [← comparisonAxisFunctionEquality]
    exact comparisonCoordinateDerivative
  exact
    (actualCoordinateDerivative'.unique generatedActualAxis).trans
      (comparisonCoordinateDerivative'.unique generatedFrozenAxis).symm

theorem fixedGlobalMatterDualFullCauchy_matterMomentumDivergence_origin_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        FixedMatterDualActual direction 0 =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        fixedGlobalMatterDualIdentityCoframeComparison direction 0 := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    fixedGlobalMatterDualFullCauchy_matterMomentumDerivative_origin_eq_comparison
      direction derivativeDirection

private theorem fixedGlobalMatterDualFullCauchy_pointField_origin_eq_comparison :
    toContinuumPointField FixedMatterDualActual 0 =
      toContinuumPointField
        fixedGlobalMatterDualIdentityCoframeComparison 0 := by
  exact
    toContinuumPointField_identityCoframeComparison_eq_of_coframe_eq_one
      FixedMatterDualActual 0 fixedGlobalMatterDualFullCauchy_coframe_origin

theorem fixedGlobalMatterDualFullCauchy_matterAlgebraic_origin_eq_comparison
    (direction : MatterCoordinateCarrier) :
    matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        FixedMatterDualActual direction 0 =
      matterAlgebraicDirectionalCoefficient positiveSmoothUnifiedSource
        fixedGlobalMatterDualIdentityCoframeComparison direction 0 := by
  have variationEquality :
      holonomicMatterVariationAlgebraicDirection
          FixedMatterDualActual direction 0 =
        holonomicMatterVariationAlgebraicDirection
          fixedGlobalMatterDualIdentityCoframeComparison direction 0 := by
    rfl
  have vectorEquality :
      matterAlgebraicVariationVector positiveSmoothUnifiedSource
          FixedMatterDualActual direction 0 =
        matterAlgebraicVariationVector positiveSmoothUnifiedSource
          fixedGlobalMatterDualIdentityCoframeComparison direction 0 := by
    unfold matterAlgebraicVariationVector matterFieldVariationVector
    rw [fixedGlobalMatterDualFullCauchy_pointField_origin_eq_comparison,
      variationEquality]
  unfold matterAlgebraicDirectionalCoefficient generatedVolumeDensity
  rw [fixedGlobalMatterDualFullCauchy_pointField_origin_eq_comparison,
    vectorEquality]
  rfl

/-- The action-generated adjoint write satisfies the actual densitized
Euler--Lagrange equation at the common fixed P506/L0 contact.  This is a
same-output producer-soundness readout, not a second constructor or an
independent Cauchy constraint. -/
theorem fixedGlobalMatterDualFullCauchy_matterEuler_origin
    (direction : MatterCoordinateCarrier) :
    matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
        FixedMatterDualActual direction 0 =
      0 := by
  unfold matterEulerLagrangeDirectionalCoefficient
  rw [fixedGlobalMatterDualFullCauchy_matterAlgebraic_origin_eq_comparison,
    fixedGlobalMatterDualFullCauchy_matterMomentumDivergence_origin_eq_comparison]
  exact
    fixedGlobalMatterDualIdentityCoframeComparison_matterEuler_origin direction

/-- Fixed-lineage adjoint acceptance keeps both the generated action law and
its densitized Euler--Lagrange readout on the same final actual. -/
theorem fixedGlobalMatterDualFullCauchy_adjointAcceptance :
    HolonomicIdentityCoframeConjugateMatterTimeActionLaw
          FixedMatterDualActual 0
          (holonomicConjugateMatterDerivativeDual FixedMatterDualActual 0
            canonicalLorentzianTimeDirection) ∧
      ∀ direction : MatterCoordinateCarrier,
        matterEulerLagrangeDirectionalCoefficient positiveSmoothUnifiedSource
            FixedMatterDualActual direction 0 =
          0 :=
  ⟨fixedGlobalMatterDualFullCauchy_adjointActionLaw,
    fixedGlobalMatterDualFullCauchy_matterEuler_origin⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
