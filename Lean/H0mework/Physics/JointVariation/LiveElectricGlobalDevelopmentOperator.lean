import H0mework.Physics.JointVariation.GlobalDevelopmentOperator
import H0mework.Physics.ConstrainedCauchy.FixedJointP286LiveElectricCauchyOperator

/-!
# Live-electric complete-joint global development operator

This module replaces the frozen-electric P286 temporal leg of the existing
complete-joint global composition by the source/current-only live-electric
Cauchy producer.  The dependency order remains

```text
current
  -> temporal matter/adjoint/scalar development
  -> canonical P286 connection and live algebraic auxiliary
  -> live-electric P286 Cauchy write
  -> current-native Cartan connection and gravity reaction
```

Every constructor consumes only the same `(source,current)`.  No residual,
support coordinate, target field, branch, or equation receipt is read back
into the write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator

open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineP286GaugeAuxiliaryVariation
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 100000

local instance liveElectricGlobalP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear
    p286AmbientLinear_injective

local instance liveElectricGlobalP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Source/current-only global composition -/

/-- Replace only the old frozen-electric temporal P286 leg by the
live-electric Cauchy producer. -/
def completeJointLiveElectricGlobalP286Current
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator source
    (completeJointGlobalP286AlgebraicCurrent source current)

/-- One branch-free common global actual with the existing Cartan/reaction
tail applied after the live-electric P286 write. -/
def
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCartanReactionCurrentRestart source
    (completeJointLiveElectricGlobalP286Current source current)

/-! ## Primitive-field preservation -/

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).matter =
      (completeJointGlobalP286AlgebraicCurrent source current).matter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).conjugateMatter =
      (completeJointGlobalP286AlgebraicCurrent source current
        ).conjugateMatter :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).scalar =
      (completeJointGlobalP286AlgebraicCurrent source current).scalar :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).coframe =
      (completeJointGlobalP286AlgebraicCurrent source current).coframe :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).gaugeConnection =
      (completeJointGlobalP286AlgebraicCurrent source current
        ).gaugeConnection :=
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter_eq_existing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).matter =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current).matter := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter]
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter_eq_existing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).conjugateMatter =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current).conjugateMatter := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter]
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar_eq_existing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).scalar =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current).scalar := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar]
  rfl

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).coframe =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current).coframe := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_coframe_eq_p286Algebraic]

@[simp] theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection_eq_existing
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
      source current).gaugeConnection =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        source current).gaugeConnection := by
  rw [
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection,
    sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeConnection_eq_p286Algebraic]

/-! ## Exact zero-slice auxiliary seam -/

/-- The final Cartan leg preserves the live-electric Cauchy boundary, which
is the literal algebraic current on the complete zero slice. -/
theorem
    sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (space : StageNineSpatialPoint) :
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
          source current)
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        (completeJointGlobalP286AlgebraicCurrent source current)
        (canonicalCauchySlicePoint 0 space) := by
  change
    holonomicP286GaugeAuxiliaryCoordinate
        (sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
          source (completeJointGlobalP286AlgebraicCurrent source current))
        (canonicalCauchySlicePoint 0 space) =
      _
  rw [
    sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator_zeroSlice,
    completeJointP286LiveElectricZeroSliceMagneticBase_coordinate]
  unfold completeJointP286LiveElectricZeroSliceMagneticBaseCoordinate
  rw [completeJointGlobalP286AlgebraicCurrent_zeroSliceAnchor]
  funext pair
  fin_cases pair <;>
    simp [p286ElectricProjection, p286MagneticProjection]

/-- At the registered spacetime origin, the live-electric P286 leg has the
same complete point field as its preceding algebraic action leg.  The only
non-definitional slot is the auxiliary two-form, paid by the exact Cauchy
boundary theorem above.  This is an occurrence readout, not an identification
of the two whole configurations. -/
theorem completeJointLiveElectricGlobalP286Current_pointField_origin_eq_algebraic
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    toContinuumPointField
        (completeJointLiveElectricGlobalP286Current source current) 0 =
      toContinuumPointField
        (completeJointGlobalP286AlgebraicCurrent source current) 0 := by
  apply StageNineContinuumPointField.ext <;> try rfl
  funext pair
  apply p286CoordinateEquiv.injective
  have boundary := congrFun
    (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
      source current (0 : StageNineSpatialPoint)) pair
  have origin :
      canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) =
        (0 : BasePoint) := by
    ext direction
    fin_cases direction <;>
      simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
        Fin.sum_univ_three]
  rw [origin] at boundary
  change
    p286CoordinateEquiv
        ((completeJointLiveElectricGlobalP286Current source current
          ).gaugeAuxiliary 0 pair) =
      p286CoordinateEquiv
        ((completeJointGlobalP286AlgebraicCurrent source current
          ).gaugeAuxiliary 0 pair) at boundary
  exact boundary

/-! ## Fixed P506/L0 specialization -/

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

def fixedP506L0CompleteJointLiveElectricAlgebraicCurrent :
    StageNineHolonomicConfiguration :=
  completeJointGlobalP286AlgebraicCurrent positiveSmoothUnifiedSource
    FixedInput

/-- The fixed P506/L0 lineage selects one live-electric common global
development without adding a target field or branch receipt. -/
def fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
    positiveSmoothUnifiedSource FixedInput

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_matter_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.matter =
      fixedP506L0CompleteJointGlobalDevelopmentActual.matter :=
  by
    change
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).matter =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).matter
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_matter_eq_existing
        positiveSmoothUnifiedSource FixedInput

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_conjugateMatter_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.conjugateMatter =
      fixedP506L0CompleteJointGlobalDevelopmentActual.conjugateMatter :=
  by
    change
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).conjugateMatter =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).conjugateMatter
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_conjugateMatter_eq_existing
        positiveSmoothUnifiedSource FixedInput

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_scalar_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.scalar =
      fixedP506L0CompleteJointGlobalDevelopmentActual.scalar :=
  by
    change
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).scalar =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).scalar
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_scalar_eq_existing
        positiveSmoothUnifiedSource FixedInput

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_coframe_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.coframe =
      fixedP506L0CompleteJointGlobalDevelopmentActual.coframe :=
  by
    change
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).coframe =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).coframe
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_coframe_eq_existing
        positiveSmoothUnifiedSource FixedInput

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeConnection_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeConnection =
      fixedP506L0CompleteJointGlobalDevelopmentActual.gaugeConnection :=
  by
    change
      (sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).gaugeConnection =
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator
        positiveSmoothUnifiedSource FixedInput).gaugeConnection
    exact
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeConnection_eq_existing
        positiveSmoothUnifiedSource FixedInput

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeAuxiliary_zeroSlice
    (space : StageNineSpatialPoint) :
      holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual
        (canonicalCauchySlicePoint 0 space) =
      holonomicP286GaugeAuxiliaryCoordinate
        fixedP506L0CompleteJointLiveElectricAlgebraicCurrent
        (canonicalCauchySlicePoint 0 space) :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
    positiveSmoothUnifiedSource FixedInput space

private theorem canonicalCauchySlicePoint_zero_zero_local :
    canonicalCauchySlicePoint 0 (0 : StageNineSpatialPoint) = 0 := by
  apply PiLp.ext
  intro direction
  fin_cases direction <;>
    simp [canonicalCauchySlicePoint, canonicalLorentzianTimeDirection,
      Fin.sum_univ_three]

theorem
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeAuxiliary_origin_eq_existing :
    fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual.gaugeAuxiliary
        0 =
      fixedP506L0CompleteJointGlobalDevelopmentActual.gaugeAuxiliary 0 := by
  funext pair
  apply p286CoordinateEquiv.injective
  have live :=
    congrFun
      (fixedP506L0CompleteJointLiveElectricGlobalDevelopmentActual_gaugeAuxiliary_zeroSlice
        0)
      pair
  have existing :=
    congrFun
      (sourceActionGeneratedDiracDualCompleteJointGlobalDevelopmentOperator_gaugeAuxiliary_zeroSlice
        positiveSmoothUnifiedSource FixedInput 0)
      pair
  rw [canonicalCauchySlicePoint_zero_zero_local] at live existing
  exact live.trans existing.symm

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
