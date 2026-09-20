import H0mework.Physics.CartanAction.CartanP286CriticalPair
import H0mework.Physics.FinalJoint.FixedTimeAxisCoframe
import H0mework.Physics.FixedJoint.FixedP286RecenteredProducer
import H0mework.Physics.IdentityHessian.CartanECNormalFixedGlobalActual

/-!
# Four-dimensional canonical section Cartan restart

The fixed P506/L0 canonical P286 contact family already assembles one
four-dimensional holonomic section.  This module applies the authoritative
current-native Cartan/reaction write directly to that section.  The
constructor consumes only the fixed source and the generated current: no
domain witness, residual coordinate, zero receipt, or target field enters.

The section coframe is identified globally with the existing KIN-16
primitive diagonal, giving direct fixed-lineage regularity.  On the actual
determinant-nonzero point domain, the resulting common successor satisfies
the Lorentz zero fiber and typed spin--torsion equation, while its complete
P286 connection residual is preserved by the Cartan--P286 critical pair.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineCartanAffineConnectionActualization
open StageNineCartanTorsionThreeFormCoordinates
open StageNineCoframeFirstJet
open StageNineDiracDualFormNativeCartanConnectionActualization
open StageNineDiracDualFormNativeCartanP286CriticalPair
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeConstitutiveJointActionSpatialSectionOperator
open StageNineDiracDualFormNativeFixedP506FinalCommonActionWrite
open StageNineDiracDualFormNativeFixedP506FinalCommonTimeAxisCoframe
open StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionProducer
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalActual
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalFixedGlobalRegularity
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open StageNineFormNativeLorentzGeometricFirstVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 100000

private abbrev RecenteredSectionCurrent :
    StageNineHolonomicConfiguration :=
  fixedP506L0P286CanonicalRecenteredSectionActual

private abbrev PrimitiveDiagonalCurrent :
    StageNineHolonomicConfiguration :=
  positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual

/-! ## Fixed-lineage global coframe -/

/-- The canonical P286 section retains the one already generated KIN-16
coframe globally, not merely on one contact or one time slice. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionActual_coframe_eq_primitiveDiagonal :
    RecenteredSectionCurrent.coframe = PrimitiveDiagonalCurrent.coframe := by
  funext point
  let time := canonicalTimeProjection point
  let space := canonicalSpatialProjection point
  calc
    RecenteredSectionCurrent.coframe point =
        RecenteredSectionCurrent.coframe
          (canonicalCauchySlicePoint time space) := by
      rw [canonicalCauchySlicePoint_projections]
    _ = (fixedP506L0P286CanonicalRecenteredContactActual space).coframe
          (canonicalCauchySlicePoint time 0) :=
      fixedP506L0P286CanonicalRecenteredSectionActual_coframe_slice time space
    _ = (fixedP506L0FinalCommonActionActual space).coframe
          (canonicalCauchySlicePoint time 0) := by
      simp [fixedP506L0P286CanonicalRecenteredContactActual,
        fixedP506L0P286CanonicalRecenteredContactInput]
    _ = (fixedIdentityECHessianCartanECNormalContactActual space).coframe
          (canonicalCauchySlicePoint time 0) :=
      fixedP506L0FinalCommonActionActual_coframe_timeAxis_eq_contact space time
    _ = PrimitiveDiagonalCurrent.coframe
          (canonicalCauchySlicePoint time space) := by
      change
        (fixedIdentityECHessianCartanECNormalContactActual space).coframe
            (canonicalCauchySlicePoint time 0) =
          positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual.coframe
            (canonicalCauchySlicePoint time space)
      symm
      simpa only [
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
        ← fixedIdentityECHessianCartanECNormalContactActual_eq_generated]
        using
          primitiveDiagonalActual_coframe_slice positiveSmoothUnifiedSource
            positiveP506MatterCurrentFullSynchronizedCauchyState time space
    _ = PrimitiveDiagonalCurrent.coframe point := by
      rw [canonicalCauchySlicePoint_projections]

/-- Direct all-point regularity of the fixed section coframe.  No generic
regularity theory for arbitrary currents is introduced. -/
theorem fixedP506L0P286CanonicalRecenteredSectionActual_coframe_contDiff :
    ContDiff ℝ ∞ RecenteredSectionCurrent.coframe := by
  rw [
    fixedP506L0P286CanonicalRecenteredSectionActual_coframe_eq_primitiveDiagonal]
  apply contDiff_pi'
  intro internal
  apply contDiff_pi'
  intro coordinate
  exact
    positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_smooth.1
      internal coordinate

/-! ## Source/current-only four-dimensional successor -/

/-- One global successor generated by the same fixed source and the complete
canonical P286 section. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart
    positiveSmoothUnifiedSource RecenteredSectionCurrent

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_coframe :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe =
      RecenteredSectionCurrent.coframe :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gaugeConnection :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.gaugeConnection =
      RecenteredSectionCurrent.gaugeConnection :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gaugeAuxiliary :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.gaugeAuxiliary =
      RecenteredSectionCurrent.gaugeAuxiliary :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_scalar :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.scalar =
      RecenteredSectionCurrent.scalar :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_matter :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.matter =
      RecenteredSectionCurrent.matter :=
  rfl

@[simp] theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_conjugateMatter :
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.conjugateMatter =
      RecenteredSectionCurrent.conjugateMatter :=
  rfl

/-- The real readback domain of the generated successor.  It is derived
from the actual coframe and is not an input to the constructor. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain :
    Set BasePoint :=
  { point |
    Matrix.det
      (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
        point) ≠ 0 }

private theorem canonicalCauchySlicePoint_zero_zero :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

/-- The actual determinant domain is nonempty: it contains the generated
P506/L0 origin. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestart_zero_mem_nondegenerateDomain :
    0 ∈
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain := by
  change
    Matrix.det
        (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
          0) ≠ 0
  rw [
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_coframe,
    fixedP506L0P286CanonicalRecenteredSectionActual_coframe_eq_primitiveDiagonal]
  have originJet := fixedPrimitiveDiagonal_coframeFirstJet_zeroSlice 0
  have originCoframe :=
    congrArg PointwiseLorentzianCoframeJet.coframe originJet
  rw [canonicalCauchySlicePoint_zero_zero] at originCoframe
  change PrimitiveDiagonalCurrent.coframe 0 = 1 at originCoframe
  rw [originCoframe]
  norm_num

/-! ## Same-successor equations and whole-carrier readback -/

theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityMultiplierResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point
      ).gravityMultiplier = 0 := by
  change
    formNativeGravityMultiplierEulerResidual
        (toContinuumPointField
          fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point) =
      0
  apply (formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity _).2
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_simplicity
      positiveSmoothUnifiedSource RecenteredSectionCurrent point

theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityAuxiliaryResidual_zero
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point
      ).gravityAuxiliary = 0 := by
  have equation :=
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_auxiliaryEquation
      positiveSmoothUnifiedSource RecenteredSectionCurrent
  exact congrFun equation point

/-- The full Lorentz Euler three-form vanishes at every actual
nondegenerate point of the four-dimensional successor. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_lorentzEulerThreeForm_zero_at
    (point : BasePoint)
    (inDomain :
      point ∈
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain) :
    holonomicFormNativeLorentzEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point =
      0 := by
  apply
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_lorentzEulerThreeForm_zero_at_of_coframeContDiff
      positiveSmoothUnifiedSource RecenteredSectionCurrent
      fixedP506L0P286CanonicalRecenteredSectionActual_coframe_contDiff point
  change
    Matrix.det
        (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
          point) ≠ 0 at inDomain
  simpa only [
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_coframe] using
    inDomain

/-- The same point and same actual carry the typed spin--torsion readback. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_typedTorsionSpin_at
    (point : BasePoint)
    (inDomain :
      point ∈
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain) :
    cartanTorsionThreeForm
        (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
          point)
        (actualPointwiseCartanTorsionTwoForm
          (holonomicCoframeFirstJetAt
            fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
            point)
          (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.gravityConnection
            point)) =
      diracDualFormNativeActionSpinResponseAt positiveSmoothUnifiedSource
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point := by
  apply
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_typedTorsionSpinAt
      positiveSmoothUnifiedSource RecenteredSectionCurrent point
  change
    Matrix.det
        (fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual.coframe
          point) ≠ 0 at inDomain
  simpa only [
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_coframe] using
    inDomain

/-- The Cartan/reaction leg preserves the complete P286 connection residual
at every spacetime point of the global section. -/
theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_p286Residual_at
    (point : BasePoint) :
    (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point
      ).p286GaugeConnection =
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        RecenteredSectionCurrent point).p286GaugeConnection := by
  change
    holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point =
      holonomicFormNativeP286GaugeEulerThreeForm positiveSmoothUnifiedSource 0
        RecenteredSectionCurrent point
  unfold fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual
  exact
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart_p286EulerThreeForm
      positiveSmoothUnifiedSource RecenteredSectionCurrent point

/-- Whole-nine readout on the one four-dimensional successor.  The two
action-generated gravity algebraic coordinates and Lorentz coordinate are
zero; the P286 connection coordinate is the literally preserved residual of
the input section; all remaining coordinates stay on this same actual. -/
def fixedP506L0P286CanonicalRecenteredSectionCartanRestartPointwiseResidualReadout
    (point : BasePoint) :
    DiracDualFormNativePointwiseJointResidualCarrier :=
  { diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point with
    gravityMultiplier := 0
    gravityAuxiliary := 0
    lorentzConnection := 0
    p286GaugeConnection :=
      (diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        RecenteredSectionCurrent point).p286GaugeConnection }

theorem
    fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_pointwiseResidual_at
    (point : BasePoint)
    (inDomain :
      point ∈
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartNondegenerateDomain) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual point =
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartPointwiseResidualReadout
        point := by
  apply DiracDualFormNativePointwiseJointResidualCarrier.ext
  · exact
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityMultiplierResidual_zero
        point
  · exact
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_gravityAuxiliaryResidual_zero
        point
  · rfl
  · exact
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_lorentzEulerThreeForm_zero_at
        point inDomain
  · exact
      fixedP506L0P286CanonicalRecenteredSectionCartanRestartActual_p286Residual_at
        point
  · rfl
  · rfl
  · rfl
  · rfl

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506P286CanonicalRecenteredSectionCartanRestart
