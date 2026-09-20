import H0mework.Physics.GaugeSource.CenteredCompactEntropyDescent
import H0mework.Physics.GaugeSource.ReducedCompactVariation
import H0mework.Physics.GaugeSource.ReducedEntropySafeStep

/-!
# Centered reduced P286 entropy safe steps

Every spacetime center supplies the translated canonical material window from
the centered compact family.  This module runs that exact variation through
the generic reduced `A/F/B` quartic and its coefficient-computed safe step.
The resulting family is jointly conservative: all centered reduced nexts are
the canonical algebraic base exactly when that base satisfies the P286 master
rows.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286SourceNativeCenteredReducedEntropySafeStep

open ProofFreeRicherAnholonomicSource
open StageNineCompactSupportIntegrationByParts
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeClassicalWorldCandidateFamily
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeP286JointYangMillsOperation
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open StageNineP286JointYangMillsGradientFlow
open StageNineP286SourceNativeCenteredCompactEntropyDescent
open StageNineP286SourceNativeReducedCompactVariation
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineP286SourceNativeReducedEntropySafeStep
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance centeredReducedP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  StageNineP286SourceNativeReducedEntropyDescent.reducedEntropyP286ModuleFinite

local instance centeredReducedP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  StageNineP286SourceNativeReducedEntropyDescent.reducedEntropyP286CoordinateIndexFintype

local instance centeredReducedP286CoordinateIsTopologicalAddGroup :
    IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance

def p286CenteredReducedVariation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    CompactlySupportedSmoothVariation P286GaugeOneForm :=
  p286CenteredCompactNegativeGradientVariation source
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate) center

def p286CenteredReducedDefect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) : ℝ :=
  p286CenteredCompactActionDefect source
    (p286ReducedEntropyBase source current) center

def p286CenteredReducedFirstCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286ReducedCompactFirstCoefficient source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)

def p286CenteredReducedSecondCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286ReducedCompactSecondCoefficient source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)

def p286CenteredReducedThirdCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286ReducedCompactThirdCoefficient source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)

def p286CenteredReducedFourthCoefficient
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286ReducedCompactFourthCoefficient source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)

theorem p286CenteredReducedFirstCoefficient_eq_neg_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    p286CenteredReducedFirstCoefficient source current smooth nondegenerate
        center =
      -p286CenteredReducedDefect source current center := by
  change
    p286CenteredCompactNegativeGradientFirstCoefficient source
        (p286ReducedEntropyBase source current)
        (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
        (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
        center =
      -p286CenteredCompactActionDefect source
        (p286ReducedEntropyBase source current) center
  exact p286CenteredCompactNegativeGradientFirstCoefficient_eq_neg_defect
    source (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate) center

def p286CenteredReducedStepSize
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286QuarticNegativeDefectSafeStep
    (p286CenteredReducedDefect source current center)
    (p286CenteredReducedSecondCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedThirdCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedFourthCoefficient source current smooth nondegenerate
      center)

def p286CenteredReducedNext
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : StageNineHolonomicConfiguration :=
  p286ReducedCompactJointPath source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)
    (p286CenteredReducedStepSize source current smooth nondegenerate center)

theorem p286CenteredReducedNext_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    (p286CenteredReducedNext source current smooth nondegenerate center
      ).Nondegenerate := by
  exact formNativeP286GaugeConstitutiveReadout_nondegenerate source _
    (p286ReducedCompactRawPath_nondegenerate source current nondegenerate
      (p286CenteredReducedVariation source current smooth nondegenerate center)
      (p286CenteredReducedStepSize source current smooth nondegenerate center))

theorem p286CenteredReducedNext_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286CenteredReducedNext source current smooth nondegenerate center) := by
  exact formNativeP286GaugeConstitutiveReadout_auxiliaryPointwiseEquation source
    _
    (p286ReducedCompactRawPath_nondegenerate source current nondegenerate
      (p286CenteredReducedVariation source current smooth nondegenerate center)
      (p286CenteredReducedStepSize source current smooth nondegenerate center))

def p286CenteredReducedRelativeAction
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) : ℝ :=
  p286ReducedCompactRelativeAction source current
    (p286CenteredReducedVariation source current smooth nondegenerate center)
    (p286CenteredReducedStepSize source current smooth nondegenerate center)

theorem p286CenteredReducedRelativeAction_quartic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    p286CenteredReducedRelativeAction source current smooth nondegenerate
        center =
      p286CenteredReducedStepSize source current smooth nondegenerate center *
          p286CenteredReducedFirstCoefficient source current smooth
            nondegenerate center +
        p286CenteredReducedStepSize source current smooth nondegenerate
            center ^ 2 *
          p286CenteredReducedSecondCoefficient source current smooth
            nondegenerate center +
        p286CenteredReducedStepSize source current smooth nondegenerate
            center ^ 3 *
          p286CenteredReducedThirdCoefficient source current smooth
            nondegenerate center +
        p286CenteredReducedStepSize source current smooth nondegenerate
            center ^ 4 *
          p286CenteredReducedFourthCoefficient source current smooth
            nondegenerate center :=
  p286ReducedCompactRelativeAction_quartic source current smooth nondegenerate
    (p286CenteredReducedVariation source current smooth nondegenerate center)
    (p286CenteredReducedStepSize source current smooth nondegenerate center)

theorem p286CenteredReducedDefect_nonnegative
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (center : BasePoint) :
    0 ≤ p286CenteredReducedDefect source current center :=
  p286CenteredCompactActionDefect_nonnegative source
    (p286ReducedEntropyBase source current) center

theorem p286CenteredReducedDefect_pos_of_center_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (centerNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0
        (p286ReducedEntropyBase source current) center ≠ 0) :
    0 < p286CenteredReducedDefect source current center :=
  p286CenteredCompactActionDefect_pos_of_center_euler_ne_zero source
    (p286ReducedEntropyBase source current)
    (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
    (p286ReducedEntropyBase_nondegenerate source current nondegenerate) center
    centerNonzero

theorem p286CenteredReducedRelativeAction_nonpositive
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint) :
    p286CenteredReducedRelativeAction source current smooth nondegenerate
        center ≤ 0 := by
  rw [p286CenteredReducedRelativeAction_quartic,
    p286CenteredReducedFirstCoefficient_eq_neg_defect]
  exact p286QuarticNegativeDefectSafeStep_nonpositive
    (p286CenteredReducedDefect source current center)
    (p286CenteredReducedSecondCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedThirdCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedFourthCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedDefect_nonnegative source current center)

theorem p286CenteredReducedRelativeAction_strict
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (defectPositive : 0 < p286CenteredReducedDefect source current center) :
    p286CenteredReducedRelativeAction source current smooth nondegenerate
        center < 0 := by
  rw [p286CenteredReducedRelativeAction_quartic,
    p286CenteredReducedFirstCoefficient_eq_neg_defect]
  exact p286QuarticNegativeDefectSafeStep_strict
    (p286CenteredReducedDefect source current center)
    (p286CenteredReducedSecondCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedThirdCoefficient source current smooth nondegenerate
      center)
    (p286CenteredReducedFourthCoefficient source current smooth nondegenerate
      center) defectPositive

theorem p286CenteredReducedRelativeAction_strict_of_center_euler_ne_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (centerNonzero :
      holonomicFormNativeP286GaugeEulerThreeForm source 0
        (p286ReducedEntropyBase source current) center ≠ 0) :
    p286CenteredReducedRelativeAction source current smooth nondegenerate
        center < 0 :=
  p286CenteredReducedRelativeAction_strict source current smooth nondegenerate
    center
    (p286CenteredReducedDefect_pos_of_center_euler_ne_zero source current
      smooth nondegenerate center centerNonzero)

theorem p286CenteredReducedNext_ne_base_of_defect_pos
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (defectPositive : 0 < p286CenteredReducedDefect source current center) :
    p286CenteredReducedNext source current smooth nondegenerate center ≠
      p286ReducedEntropyBase source current := by
  intro nextEq
  have strict := p286CenteredReducedRelativeAction_strict source current smooth
    nondegenerate center defectPositive
  have relativeZero :
      p286CenteredReducedRelativeAction source current smooth nondegenerate
          center = 0 := by
    unfold p286CenteredReducedNext at nextEq
    unfold p286CenteredReducedRelativeAction
    unfold p286ReducedCompactRelativeAction
    rw [nextEq]
    simp
  exact (ne_of_lt strict) relativeZero

theorem p286CenteredReducedNext_eq_base_of_defect_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (center : BasePoint)
    (defectZero : p286CenteredReducedDefect source current center = 0) :
    p286CenteredReducedNext source current smooth nondegenerate center =
      p286ReducedEntropyBase source current := by
  have stepZero :
      p286CenteredReducedStepSize source current smooth nondegenerate center =
        0 := by
    simp [p286CenteredReducedStepSize,
      p286QuarticNegativeDefectSafeStep, defectZero]
  unfold p286CenteredReducedNext
  rw [stepZero]
  have baseFixed :
      p286ReducedEntropyBase source current =
        formNativeP286GaugeConstitutiveReadout source
          (p286ReducedEntropyBase source current) :=
    (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source
      (p286ReducedEntropyBase source current)
      (p286ReducedEntropyBase_nondegenerate source current nondegenerate)).1
      (p286ReducedEntropyBase_auxiliaryEquation source current nondegenerate)
  change
    formNativeP286GaugeConstitutiveReadout source
        (varyP286GaugeConnectionCoordinate
          (p286ReducedEntropyBase source current)
          (p286CenteredReducedVariation source current smooth nondegenerate
            center) 0) =
      p286ReducedEntropyBase source current
  rw [show varyP286GaugeConnectionCoordinate
      (p286ReducedEntropyBase source current)
      (p286CenteredReducedVariation source current smooth nondegenerate center)
      0 = p286ReducedEntropyBase source current by
    apply StageNineHolonomicConfiguration.ext <;> try rfl
    funext point direction
    apply p286CoordinateEquiv.injective
    change
      holonomicP286GaugeConnectionCoordinate
          (varyP286GaugeConnectionCoordinate
            (p286ReducedEntropyBase source current)
            (p286CenteredReducedVariation source current smooth nondegenerate
              center) 0) point direction =
        holonomicP286GaugeConnectionCoordinate
          (p286ReducedEntropyBase source current) point direction
    rw [holonomicP286GaugeConnectionCoordinate_vary]
    simp]
  exact baseFixed.symm

theorem p286CenteredReducedNext_all_eq_base_iff_masterEquations
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate) :
    (∀ center : BasePoint,
        p286CenteredReducedNext source current smooth nondegenerate center =
          p286ReducedEntropyBase source current) ↔
      FormNativeP286GaugeAuxiliaryPointwiseEquation source
          (p286ReducedEntropyBase source current) ∧
        FormNativeP286GaugeConnectionPointwiseEquation source
          (p286ReducedEntropyBase source current) := by
  constructor
  · intro allFixed
    have allDefectsZero : ∀ center : BasePoint,
        p286CenteredReducedDefect source current center = 0 := by
      intro center
      by_contra defectNonzero
      have defectPositive :
          0 < p286CenteredReducedDefect source current center :=
        lt_of_le_of_ne
          (p286CenteredReducedDefect_nonnegative source current center)
          (Ne.symm defectNonzero)
      exact
        (p286CenteredReducedNext_ne_base_of_defect_pos source current smooth
          nondegenerate center defectPositive) (allFixed center)
    exact
      ⟨p286ReducedEntropyBase_auxiliaryEquation source current nondegenerate,
        (p286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation
          source (p286ReducedEntropyBase source current)
          (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
          (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
          ).1 allDefectsZero⟩
  · rintro ⟨_auxiliary, connection⟩ center
    have defectZero : p286CenteredReducedDefect source current center = 0 :=
      (p286CenteredCompactActionDefect_all_zero_iff_connectionPointwiseEquation
        source (p286ReducedEntropyBase source current)
        (p286ReducedEntropyBase_smooth source current smooth nondegenerate)
        (p286ReducedEntropyBase_nondegenerate source current nondegenerate)
        ).2 connection center
    exact p286CenteredReducedNext_eq_base_of_defect_zero source current smooth
      nondegenerate center defectZero

/-! ## Exact root-owned SafeFinal specialization -/

private abbrev SafeSource : SmoothUnifiedSource := positiveSmoothUnifiedSource

private abbrev SafeFinal : StageNineHolonomicConfiguration :=
  SafeFinalClassicalWorldCandidateActual

private theorem safeFinalMasterEquations_iff_p286ResidualRows_zero :
    (FormNativeP286GaugeAuxiliaryPointwiseEquation SafeSource SafeFinal ∧
        FormNativeP286GaugeConnectionPointwiseEquation SafeSource SafeFinal) ↔
      ∀ point : BasePoint,
        (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeAuxiliary = 0 ∧
          (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeConnection = 0 :=
  (p286JointYangMillsEulerStep_eq_self_iff_masterEquations SafeSource SafeFinal
    safeFinalClassicalWorldCandidateActual_nondegenerate).symm.trans
      fixedP506L0CartanECConstraintCauchySafeFinalP286GlobalYangMillsEulerActual_eq_safeFinal_iff_p286ResidualRows_zero

/-- Exact total-lock specialization.  Comparing every generated reduced next
to the root-owned SafeFinal current recovers both authoritative P286 rows:
the comparison itself forces the algebraic base to be the same current, while
centered entropy rigidity forces the connection row. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredReducedNext_all_eq_safeFinal_iff_p286ResidualRows_zero :
    (∀ center : BasePoint,
        p286CenteredReducedNext SafeSource SafeFinal
            safeFinalClassicalWorldCandidateActual_smooth
            safeFinalClassicalWorldCandidateActual_nondegenerate center =
          SafeFinal) ↔
      ∀ point : BasePoint,
        (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeAuxiliary = 0 ∧
          (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeConnection = 0 := by
  constructor
  · intro allSafeFinal
    have nextAuxiliary :=
      p286CenteredReducedNext_auxiliaryPointwiseEquation SafeSource SafeFinal
        safeFinalClassicalWorldCandidateActual_smooth
        safeFinalClassicalWorldCandidateActual_nondegenerate 0
    rw [allSafeFinal 0] at nextAuxiliary
    have safeFinal_eq_base :
        SafeFinal = p286ReducedEntropyBase SafeSource SafeFinal :=
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
        SafeSource SafeFinal
        safeFinalClassicalWorldCandidateActual_nondegenerate).1 nextAuxiliary
    have allBase : ∀ center : BasePoint,
        p286CenteredReducedNext SafeSource SafeFinal
            safeFinalClassicalWorldCandidateActual_smooth
            safeFinalClassicalWorldCandidateActual_nondegenerate center =
          p286ReducedEntropyBase SafeSource SafeFinal := by
      intro center
      exact (allSafeFinal center).trans safeFinal_eq_base
    have masterBase :=
      (p286CenteredReducedNext_all_eq_base_iff_masterEquations SafeSource
        SafeFinal safeFinalClassicalWorldCandidateActual_smooth
        safeFinalClassicalWorldCandidateActual_nondegenerate).1 allBase
    have masterSafeFinal :
        FormNativeP286GaugeAuxiliaryPointwiseEquation SafeSource SafeFinal ∧
          FormNativeP286GaugeConnectionPointwiseEquation SafeSource
            SafeFinal := by
      rw [safeFinal_eq_base]
      exact masterBase
    exact safeFinalMasterEquations_iff_p286ResidualRows_zero.1 masterSafeFinal
  · intro residualRows
    have masterSafeFinal :
        FormNativeP286GaugeAuxiliaryPointwiseEquation SafeSource SafeFinal ∧
          FormNativeP286GaugeConnectionPointwiseEquation SafeSource
            SafeFinal :=
      safeFinalMasterEquations_iff_p286ResidualRows_zero.2 residualRows
    have safeFinal_eq_base :
        SafeFinal = p286ReducedEntropyBase SafeSource SafeFinal :=
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
        SafeSource SafeFinal
        safeFinalClassicalWorldCandidateActual_nondegenerate).1
        masterSafeFinal.1
    have masterBase :
        FormNativeP286GaugeAuxiliaryPointwiseEquation SafeSource
            (p286ReducedEntropyBase SafeSource SafeFinal) ∧
          FormNativeP286GaugeConnectionPointwiseEquation SafeSource
            (p286ReducedEntropyBase SafeSource SafeFinal) := by
      rw [← safeFinal_eq_base]
      exact masterSafeFinal
    have allBase :=
      (p286CenteredReducedNext_all_eq_base_iff_masterEquations SafeSource
        SafeFinal safeFinalClassicalWorldCandidateActual_smooth
        safeFinalClassicalWorldCandidateActual_nondegenerate).2 masterBase
    intro center
    exact (allBase center).trans safeFinal_eq_base.symm

/-- Factorized form exposing why the reduced-base comparison alone carries
only the connection normal form: equality of the algebraic base with the
root current is the exact auxiliary-row factor. -/
theorem
    fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredReducedBaseFactorization_iff_p286ResidualRows_zero :
    ((∀ center : BasePoint,
        p286CenteredReducedNext SafeSource SafeFinal
            safeFinalClassicalWorldCandidateActual_smooth
            safeFinalClassicalWorldCandidateActual_nondegenerate center =
          p286ReducedEntropyBase SafeSource SafeFinal) ∧
      p286ReducedEntropyBase SafeSource SafeFinal = SafeFinal) ↔
      ∀ point : BasePoint,
        (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeAuxiliary = 0 ∧
          (diracDualFormNativePointwiseJointResidual SafeSource SafeFinal point
            ).p286GaugeConnection = 0 := by
  constructor
  · rintro ⟨allBase, baseEq⟩
    apply
      fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredReducedNext_all_eq_safeFinal_iff_p286ResidualRows_zero.1
    intro center
    exact (allBase center).trans baseEq
  · intro rows
    have allSafeFinal :=
      fixedP506L0CartanECConstraintCauchySafeFinalP286CenteredReducedNext_all_eq_safeFinal_iff_p286ResidualRows_zero.2
        rows
    have nextAuxiliary :=
      p286CenteredReducedNext_auxiliaryPointwiseEquation SafeSource SafeFinal
        safeFinalClassicalWorldCandidateActual_smooth
        safeFinalClassicalWorldCandidateActual_nondegenerate 0
    rw [allSafeFinal 0] at nextAuxiliary
    have safeFinal_eq_base :
        SafeFinal = p286ReducedEntropyBase SafeSource SafeFinal :=
      (formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
        SafeSource SafeFinal
        safeFinalClassicalWorldCandidateActual_nondegenerate).1 nextAuxiliary
    refine ⟨?_, safeFinal_eq_base.symm⟩
    intro center
    exact (allSafeFinal center).trans safeFinal_eq_base

end
end StageNineP286SourceNativeCenteredReducedEntropySafeStep
end PhysicsCore
end SaturationMonoid
