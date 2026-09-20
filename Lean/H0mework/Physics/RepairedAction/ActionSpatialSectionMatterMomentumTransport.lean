import H0mework.Physics.RepairedAction.ActionSpatialSectionMatterIdentityCoframeAcceptance

/-!
# Repaired spatial-section matter momentum transport

The fixed P506/L0 producer has already generated one repaired global section.
On its canonical slice, the KIN-16 coframe has identity value and zero complete
first jet.  This file uses that concrete jet to compare the actual Dirac-dual
matter momentum with a proof-only identity-coframe readout.

The comparison transports only a first-order calculation.  It is not a
successor, a response operator, or a residual-selected repair.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterMomentumTransport

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCoframeFirstJet
open StageNineCoframeLocalDifferentiability
open StageNineCoframeScalarMatterRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalMatterDualAdjointAcceptance
open StageNineDiracDualFormNativeMatterVariation
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterComparison
open StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterIdentityCoframeAcceptance
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineEnrichedProofFreeSource
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
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance repairedMatterMomentumCoordinateIndexFintype :
    Fintype MatterCoordinateIndex :=
  Fintype.ofFinite MatterCoordinateIndex

private abbrev ComparisonActual : StageNineHolonomicConfiguration :=
  fixedP506FormNativeRepairedSpatialMatterSmoothComparison

def fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison :
    StageNineHolonomicConfiguration :=
  identityCoframeComparison ComparisonActual

theorem
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_smooth :
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison.Smooth :=
  identityCoframeComparison_smooth ComparisonActual
    fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth

theorem
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_hasIdentityCoframe :
    HasIdentityCoframe
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison :=
  identityCoframeComparison_hasIdentityCoframe ComparisonActual

theorem
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_actionLaw_zeroSlice
    (space : StageNineSpatialPoint) :
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
      (canonicalCauchySlicePoint 0 space)
      (holonomicConjugateMatterDerivativeDual
        fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection) := by
  apply
    (identityCoframeComparison_diracDualTimeActionLaw_iff ComparisonActual
      (canonicalCauchySlicePoint 0 space) _).2
  change
    HolonomicDiracDualIdentityCoframeConjugateMatterTimeActionLaw
      ComparisonActual (canonicalCauchySlicePoint 0 space)
      (holonomicConjugateMatterDerivativeDual ComparisonActual
        (canonicalCauchySlicePoint 0 space)
        canonicalLorentzianTimeDirection)
  exact repairedMatterComparison_adjointActionLaw_zeroSlice space

theorem
    fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_matterEuler_zeroSlice
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    diracDualMatterEulerLagrangeDirectionalCoefficient
        positiveSmoothUnifiedSource
        fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
        direction (canonicalCauchySlicePoint 0 space) =
      0 := by
  exact
    holonomicDiracDualIdentityCoframeMatterEulerLagrange_eq_zero_of_actionLaw
      positiveSmoothUnifiedSource
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_smooth
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_hasIdentityCoframe
      (canonicalCauchySlicePoint 0 space)
      (fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison_actionLaw_zeroSlice
        space)
      direction

/-! ## Fixed-slice point--coframe calculus -/

private def fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    BasePoint × LorentzianCoframe → ℝ :=
  matterDifferentialMomentumPointCoframe positiveSmoothUnifiedSource
    ComparisonActual direction derivativeDirection

private theorem
    fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe_contDiffAt
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    ContDiffAt ℝ ∞
      (fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe
        direction derivativeDirection)
      (canonicalCauchySlicePoint 0 space, 1) := by
  exact
    matterDifferentialMomentumPointCoframe_contDiffAt
      positiveSmoothUnifiedSource ComparisonActual
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth
      (canonicalCauchySlicePoint 0 space) 1 (by norm_num)
      direction derivativeDirection

private def fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) : ℝ → BasePoint :=
  fun parameter =>
    canonicalSpatialContactTranslation space
      (parameter • coordinateDirection direction)

private theorem fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    fixedP506FormNativeRepairedSpatialMatterCoordinateAxis space direction 0 =
      canonicalCauchySlicePoint 0 space := by
  unfold fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
    canonicalSpatialContactTranslation
  simp

private theorem fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    HasDerivAt
      (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis space direction)
      (coordinateDirection direction) 0 := by
  have translation :
      HasFDerivAt (canonicalSpatialContactTranslation space)
        (ContinuousLinearMap.id ℝ BasePoint)
        ((0 : ℝ) • coordinateDirection direction) := by
    unfold canonicalSpatialContactTranslation
    fun_prop
  have line :
      HasDerivAt
        (fun parameter : ℝ =>
          parameter • coordinateDirection direction)
        (coordinateDirection direction) 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℝ) 0).smul_const
        (coordinateDirection direction)
  have composed := translation.comp_hasDerivAt 0 line
  change
    HasDerivAt
      (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis space direction)
      (coordinateDirection direction) 0 at composed
  exact composed

private theorem repairedMatterComparison_coframe_zeroSlice
    (space : StageNineSpatialPoint) :
    ComparisonActual.coframe (canonicalCauchySlicePoint 0 space) = 1 := by
  have jet := repairedMatterComparison_coframeFirstJet_zeroSlice space
  exact congrArg PointwiseLorentzianCoframeJet.coframe jet

private theorem repairedMatterComparison_coframeAxis_hasDerivAt_zero
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    HasDerivAt
      (fun parameter =>
        ComparisonActual.coframe
          (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
            space direction parameter))
      0 0 := by
  let point := canonicalCauchySlicePoint 0 space
  have coframeDifferentiable :
      DifferentiableAt ℝ ComparisonActual.coframe point :=
    ((holonomicCoframe_contDiff ComparisonActual
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth
      ).differentiable (by simp)).differentiableAt
  have coframeOuter :
      HasFDerivAt ComparisonActual.coframe
        (fderiv ℝ ComparisonActual.coframe point)
        (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
          space direction 0) := by
    rw [fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero]
    exact coframeDifferentiable.hasFDerivAt
  have composed :=
    coframeOuter.comp_hasDerivAt 0
      (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
        space direction)
  have derivativeZero :
      (fderiv ℝ ComparisonActual.coframe point)
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
          (fun candidate : BasePoint =>
            evaluation (ComparisonActual.coframe candidate))
          (evaluation.comp
            (fderiv ℝ ComparisonActual.coframe point)) point :=
      evaluation.hasFDerivAt.comp point coframeDifferentiable.hasFDerivAt
    have componentDerivativeZero :=
      congrArg
        (fun jet => jet.derivative direction internal coordinate)
        (repairedMatterComparison_coframeFirstJet_zeroSlice space)
    have evaluatedFunctionEquality :
        (fun candidate : BasePoint =>
          evaluation (ComparisonActual.coframe candidate)) =
        (fun candidate : BasePoint =>
          ComparisonActual.coframe candidate internal coordinate) := by
      funext candidate
      rfl
    have evaluatedZero :
        (fderiv ℝ
          (fun candidate : BasePoint =>
            evaluation (ComparisonActual.coframe candidate)) point)
            (coordinateDirection direction) =
          0 := by
      rw [evaluatedFunctionEquality]
      simpa [holonomicCoframeFirstJetAt, fieldDirectionalDerivative, point]
        using componentDerivativeZero
    rw [evaluatedDerivative.fderiv] at evaluatedZero
    change
      evaluation
          ((fderiv ℝ ComparisonActual.coframe point)
            (coordinateDirection direction)) =
        0 at evaluatedZero
    exact evaluatedZero
  apply composed.congr_deriv
  exact derivativeZero

private def fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    let point :=
      fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
        space direction parameter
    (point, ComparisonActual.coframe point)

private def fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    ℝ → BasePoint × LorentzianCoframe :=
  fun parameter =>
    (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
      space direction parameter, 1)

private theorem
    fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis_hasDerivAt
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    HasDerivAt
      (fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
        space direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
      space direction).prodMk
      (repairedMatterComparison_coframeAxis_hasDerivAt_zero space direction)

private theorem
    fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis_hasDerivAt
    (space : StageNineSpatialPoint)
    (direction : LorentzianIndex) :
    HasDerivAt
      (fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
        space direction)
      (coordinateDirection direction, 0) 0 := by
  exact
    (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
      space direction).prodMk
      (hasDerivAt_const (x := (0 : ℝ))
        (c := (1 : LorentzianCoframe)))

theorem
    fixedP506FormNativeRepairedSpatialMatterMomentumDerivative_zeroSlice_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier)
    (derivativeDirection : LorentzianIndex) :
    fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          ComparisonActual direction derivativeDirection)
        (canonicalCauchySlicePoint 0 space) derivativeDirection =
      fieldDirectionalDerivative
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
          direction derivativeDirection)
        (canonicalCauchySlicePoint 0 space) derivativeDirection := by
  let point := canonicalCauchySlicePoint 0 space
  let outer :=
    fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe
      direction derivativeDirection
  have outerDifferentiable : DifferentiableAt ℝ outer (point, 1) :=
    (fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe_contDiffAt
      space direction derivativeDirection).differentiableAt (by simp)
  have outerDerivative := outerDifferentiable.hasFDerivAt
  have actualAxisOrigin :
      fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
          space derivativeDirection 0 =
        (point, 1) := by
    simp only [
      fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis]
    rw [fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero,
      repairedMatterComparison_coframe_zeroSlice]
  have outerAtActual :
      HasFDerivAt outer (fderiv ℝ outer (point, 1))
        (fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
          space derivativeDirection 0) := by
    simpa only [actualAxisOrigin] using outerDerivative
  have generatedActualAxis :=
    outerAtActual.comp_hasDerivAt 0
      (fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis_hasDerivAt
        space derivativeDirection)
  have frozenAxisOrigin :
      fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
          space derivativeDirection 0 =
        (point, 1) := by
    simp only [
      fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis]
    rw [fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero]
  have outerAtFrozen :
      HasFDerivAt outer (fderiv ℝ outer (point, 1))
        (fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
          space derivativeDirection 0) := by
    simpa only [frozenAxisOrigin] using outerDerivative
  have generatedFrozenAxis :=
    outerAtFrozen.comp_hasDerivAt 0
      (fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis_hasDerivAt
        space derivativeDirection)
  have actualMomentumEquality :=
    matterDifferentialMomentum_eq_pointCoframe_actualSection
      positiveSmoothUnifiedSource ComparisonActual direction
      derivativeDirection
  have comparisonMomentumEquality :=
    matterDifferentialMomentum_eq_pointCoframe_actualSection
      positiveSmoothUnifiedSource
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
      direction derivativeDirection
  change
    matterDifferentialMomentum positiveSmoothUnifiedSource
        (identityCoframeComparison ComparisonActual) direction
          derivativeDirection =
      matterDifferentialMomentumPointCoframe positiveSmoothUnifiedSource
          (identityCoframeComparison ComparisonActual) direction
          derivativeDirection ∘
        fun candidate =>
          (candidate,
            (identityCoframeComparison ComparisonActual).coframe candidate)
    at comparisonMomentumEquality
  rw [matterDifferentialMomentumPointCoframe_identityCoframeComparison
    positiveSmoothUnifiedSource ComparisonActual direction
    derivativeDirection] at comparisonMomentumEquality
  have coframeSmooth : ContDiff ℝ ∞ ComparisonActual.coframe :=
    holonomicCoframe_contDiff ComparisonActual
      fixedP506FormNativeRepairedSpatialMatterSmoothComparison_smooth
  have actualSectionDifferentiable : DifferentiableAt ℝ
      (fun candidate : BasePoint =>
        (candidate, ComparisonActual.coframe candidate)) point :=
    differentiableAt_id.prodMk
      ((coframeSmooth.differentiable (by simp)).differentiableAt)
  have outerAtActualSection : DifferentiableAt ℝ outer
      (point, ComparisonActual.coframe point) := by
    rw [show ComparisonActual.coframe point = 1 by
      simpa [point] using repairedMatterComparison_coframe_zeroSlice space]
    exact outerDifferentiable
  have actualMomentumDifferentiable : DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        ComparisonActual direction derivativeDirection) point := by
    rw [actualMomentumEquality]
    exact outerAtActualSection.comp point actualSectionDifferentiable
  have comparisonMomentumDifferentiable : DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
        direction derivativeDirection) point := by
    change DifferentiableAt ℝ
      (matterDifferentialMomentum positiveSmoothUnifiedSource
        (identityCoframeComparison ComparisonActual) direction
        derivativeDirection) point
    rw [comparisonMomentumEquality]
    have comparisonCoframeDifferentiable :
        DifferentiableAt ℝ
          (identityCoframeComparison ComparisonActual).coframe point := by
      rw [identityCoframeComparison_coframe]
      exact
        (differentiableAt_const (c := (1 : LorentzianCoframe)) :
          DifferentiableAt ℝ
            (fun _ : BasePoint => (1 : LorentzianCoframe)) point)
    exact outerDifferentiable.comp point
      (differentiableAt_id.prodMk comparisonCoframeDifferentiable)
  have actualMomentumOuter :
      HasFDerivAt
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          ComparisonActual direction derivativeDirection)
        (fderiv ℝ
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            ComparisonActual direction derivativeDirection) point)
        (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
          space derivativeDirection 0) := by
    rw [fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero]
    exact actualMomentumDifferentiable.hasFDerivAt
  have actualCoordinateDerivative :=
    actualMomentumOuter.comp_hasDerivAt 0
      (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
        space derivativeDirection)
  have comparisonMomentumOuter :
      HasFDerivAt
        (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
          direction derivativeDirection)
        (fderiv ℝ
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
            direction derivativeDirection) point)
        (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
          space derivativeDirection 0) := by
    rw [fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_zero]
    exact comparisonMomentumDifferentiable.hasFDerivAt
  have comparisonCoordinateDerivative :=
    comparisonMomentumOuter.comp_hasDerivAt 0
      (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis_hasDerivAt
        space derivativeDirection)
  have actualAxisFunctionEquality :
      (matterDifferentialMomentum positiveSmoothUnifiedSource
          ComparisonActual direction derivativeDirection) ∘
          fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
            space derivativeDirection =
        outer ∘
          fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
            space derivativeDirection := by
    funext parameter
    have read :=
      congrFun actualMomentumEquality
        (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
          space derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe,
      fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis]
      using read
  have comparisonAxisFunctionEquality :
      (matterDifferentialMomentum positiveSmoothUnifiedSource
          fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
          direction derivativeDirection) ∘
          fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
            space derivativeDirection =
        outer ∘
          fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
            space derivativeDirection := by
    funext parameter
    have read :=
      congrFun comparisonMomentumEquality
        (fixedP506FormNativeRepairedSpatialMatterCoordinateAxis
          space derivativeDirection parameter)
    simpa only [Function.comp_apply, outer,
      fixedP506FormNativeRepairedSpatialMatterMomentumPointCoframe,
      fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison,
      identityCoframeComparison_coframe,
      fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis]
      using read
  have actualCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedP506FormNativeRepairedSpatialMatterActualPointCoframeAxis
            space derivativeDirection)
        (fieldDirectionalDerivative
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            ComparisonActual direction derivativeDirection)
          point derivativeDirection)
        0 := by
    rw [← actualAxisFunctionEquality]
    exact actualCoordinateDerivative
  have comparisonCoordinateDerivative' :
      HasDerivAt
        (outer ∘
          fixedP506FormNativeRepairedSpatialMatterFrozenPointCoframeAxis
            space derivativeDirection)
        (fieldDirectionalDerivative
          (matterDifferentialMomentum positiveSmoothUnifiedSource
            fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
            direction derivativeDirection)
          point derivativeDirection)
        0 := by
    rw [← comparisonAxisFunctionEquality]
    exact comparisonCoordinateDerivative
  exact
    (actualCoordinateDerivative'.unique generatedActualAxis).trans
      (comparisonCoordinateDerivative'.unique generatedFrozenAxis).symm

theorem
    fixedP506FormNativeRepairedSpatialMatterMomentumDivergence_zeroSlice_eq_comparison
    (space : StageNineSpatialPoint)
    (direction : MatterCoordinateCarrier) :
    matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        ComparisonActual direction (canonicalCauchySlicePoint 0 space) =
      matterDifferentialMomentumDivergence positiveSmoothUnifiedSource
        fixedP506FormNativeRepairedSpatialMatterIdentityCoframeComparison
        direction (canonicalCauchySlicePoint 0 space) := by
  unfold matterDifferentialMomentumDivergence
  apply Finset.sum_congr rfl
  intro derivativeDirection _
  exact
    fixedP506FormNativeRepairedSpatialMatterMomentumDerivative_zeroSlice_eq_comparison
      space direction derivativeDirection

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeRepairedConstitutiveJointActionSpatialSectionMatterMomentumTransport
