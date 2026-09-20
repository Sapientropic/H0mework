import H0mework.Physics.Cauchy.CanonicalCauchyCoordinateProjection
import H0mework.Physics.IdentityHessian.CartanECNormalWholeSliceContactUpdate

/-!
# Repaired-root primitive diagonal actual

KIN-15 generates one repaired-action local actual at every spatial contact.
This module evaluates those generated germs on their local time axes and
assembles the nine primitive values into one four-dimensional holonomic
carrier.

The constructor consumes only `(source, current)`.  It accepts no residual,
target field, branch, overlap witness, smoothness receipt, stationary
configuration, or cohomology class.  Its exact responsibility is value-level
time-axis fidelity and, at time zero, primitive fidelity to the KIN-15
whole-slice current.

This raw diagonal is not yet a smooth spacetime solution.  In particular, it
does not identify local spatial or mixed jets with derivatives of the
assembled field, transport the contact Euler/torsion equations away from
their origins, produce a positive-time integral curve, or prove constraint
propagation.  `scalarVelocity` is derived by a four-dimensional Fréchet
derivative and is therefore deliberately outside the primitive fidelity
statement until joint spatial regularity is proved.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageEightProofFreeSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeIdentityECHessianCartanECNormalWholeSliceContactUpdate
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedCompleteP286CauchyPath
open StageNineSourceActionGeneratedP506MatterCurrentFullSynchronizedResponseLocalActualLift

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

private def generatedContact
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (point : BasePoint) : StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
    source current (canonicalSpatialProjection point)

private def generatedContactTimeAxisPoint (point : BasePoint) : BasePoint :=
  canonicalCauchySlicePoint (canonicalTimeProjection point) 0

/-- The source/current-only raw diagonal of the repaired contact family.
Every primitive field at a global point is read from the same generated
contact germ selected by that point's spatial coordinate. -/
def sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) : StageNineHolonomicConfiguration where
  coframe := fun point =>
    (generatedContact source current point).coframe
      (generatedContactTimeAxisPoint point)
  gravityConnection := fun point =>
    (generatedContact source current point).gravityConnection
      (generatedContactTimeAxisPoint point)
  gravityAuxiliary := fun point =>
    (generatedContact source current point).gravityAuxiliary
      (generatedContactTimeAxisPoint point)
  gravitySimplicityMultiplier := fun point =>
    (generatedContact source current point).gravitySimplicityMultiplier
      (generatedContactTimeAxisPoint point)
  gaugeConnection := fun point =>
    (generatedContact source current point).gaugeConnection
      (generatedContactTimeAxisPoint point)
  gaugeAuxiliary := fun point =>
    (generatedContact source current point).gaugeAuxiliary
      (generatedContactTimeAxisPoint point)
  scalar := fun point =>
    (generatedContact source current point).scalar
      (generatedContactTimeAxisPoint point)
  matter := fun point =>
    (generatedContact source current point).matter
      (generatedContactTimeAxisPoint point)
  conjugateMatter := fun point =>
    (generatedContact source current point).conjugateMatter
      (generatedContactTimeAxisPoint point)

@[simp] theorem primitiveDiagonalActual_coframe_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).coframe (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).coframe
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_gravityConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).gravityConnection (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravityConnection
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_gravityAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).gravityAuxiliary (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravityAuxiliary
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_multiplier_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_gaugeConnection_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).gaugeConnection (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gaugeConnection
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_gaugeAuxiliary_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).gaugeAuxiliary (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gaugeAuxiliary
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_scalar_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).scalar (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).scalar
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_matter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).matter (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).matter
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

@[simp] theorem primitiveDiagonalActual_conjugateMatter_slice
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState)
    (time : Real)
    (space : StageNineSpatialPoint) :
    (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
      source current).conjugateMatter
        (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).conjugateMatter
        (canonicalCauchySlicePoint time 0) := by
  simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual,
    generatedContact, generatedContactTimeAxisPoint]

/-! ## Exact value-level responsibility -/

/-- Exact responsibility of the raw diagonal: all nine primitive fields use
the matching generated contact and the same local time-axis point. -/
structure PrimitiveTimeAxisFidelity
    (candidate : StageNineHolonomicConfiguration)
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) : Prop where
  coframe : forall time space,
    candidate.coframe (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).coframe (canonicalCauchySlicePoint time 0)
  gravityConnection : forall time space,
    candidate.gravityConnection (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravityConnection
        (canonicalCauchySlicePoint time 0)
  gravityAuxiliary : forall time space,
    candidate.gravityAuxiliary (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravityAuxiliary
        (canonicalCauchySlicePoint time 0)
  multiplier : forall time space,
    candidate.gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time 0)
  gaugeConnection : forall time space,
    candidate.gaugeConnection (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gaugeConnection
        (canonicalCauchySlicePoint time 0)
  gaugeAuxiliary : forall time space,
    candidate.gaugeAuxiliary (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).gaugeAuxiliary
        (canonicalCauchySlicePoint time 0)
  scalar : forall time space,
    candidate.scalar (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).scalar (canonicalCauchySlicePoint time 0)
  matter : forall time space,
    candidate.matter (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).matter (canonicalCauchySlicePoint time 0)
  conjugateMatter : forall time space,
    candidate.conjugateMatter (canonicalCauchySlicePoint time space) =
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactActual
        source current space).conjugateMatter
        (canonicalCauchySlicePoint time 0)

theorem primitiveDiagonalActual_timeAxisFidelity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    PrimitiveTimeAxisFidelity
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        source current)
      source current where
  coframe := primitiveDiagonalActual_coframe_slice source current
  gravityConnection :=
    primitiveDiagonalActual_gravityConnection_slice source current
  gravityAuxiliary :=
    primitiveDiagonalActual_gravityAuxiliary_slice source current
  multiplier := primitiveDiagonalActual_multiplier_slice source current
  gaugeConnection :=
    primitiveDiagonalActual_gaugeConnection_slice source current
  gaugeAuxiliary :=
    primitiveDiagonalActual_gaugeAuxiliary_slice source current
  scalar := primitiveDiagonalActual_scalar_slice source current
  matter := primitiveDiagonalActual_matter_slice source current
  conjugateMatter :=
    primitiveDiagonalActual_conjugateMatter_slice source current

/-- Value-level fidelity of the nine primitive fields on one Cauchy slice.
The derived scalar velocity is intentionally absent. -/
structure PrimitiveCauchyValueFidelity
    (candidate : StageNineHolonomicConfiguration)
    (time : Real)
    (state : StageNineCauchyState) : Prop where
  coframe : forall space,
    candidate.coframe (canonicalCauchySlicePoint time space) =
      state.coframe space
  gravityConnection : forall space,
    candidate.gravityConnection (canonicalCauchySlicePoint time space) =
      state.gravityConnection space
  gravityAuxiliary : forall space,
    candidate.gravityAuxiliary (canonicalCauchySlicePoint time space) =
      state.gravityAuxiliary space
  multiplier : forall space,
    candidate.gravitySimplicityMultiplier
        (canonicalCauchySlicePoint time space) =
      state.gravitySimplicityMultiplier space
  gaugeConnection : forall space,
    candidate.gaugeConnection (canonicalCauchySlicePoint time space) =
      state.gaugeConnection space
  gaugeAuxiliary : forall space,
    candidate.gaugeAuxiliary (canonicalCauchySlicePoint time space) =
      state.gaugeAuxiliary space
  scalar : forall space,
    candidate.scalar (canonicalCauchySlicePoint time space) =
      state.scalar space
  matter : forall space,
    candidate.matter (canonicalCauchySlicePoint time space) =
      state.matter space
  conjugateMatter : forall space,
    candidate.conjugateMatter (canonicalCauchySlicePoint time space) =
      state.conjugateMatter space

/-- At time zero the single raw diagonal has exactly the nine primitive
values of the KIN-15 whole-slice current. -/
theorem primitiveDiagonalActual_initialPrimitiveFidelity
    (source : SmoothUnifiedSource)
    (current : StageNineCauchyState) :
    PrimitiveCauchyValueFidelity
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        source current)
      0
      (sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent
        source current) := by
  constructor <;> intro space <;>
    simp [sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalWholeSliceCurrent,
      sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalContactSlice,
      canonicalCauchyRestriction]

/-! ## Fixed exact-lineage checkpoint -/

def positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
    positiveSmoothUnifiedSource
    positiveP506MatterCurrentFullSynchronizedCauchyState

/-- No-premise fixed-source checkpoint.  H1 is absent by construction: it is
the automatic readout of the generated KIN occurrence ring, not a premise or
field of this actual. -/
theorem positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual_realizes :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference /\
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 /\
      PrimitiveTimeAxisFidelity
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState /\
      PrimitiveCauchyValueFidelity
        positiveP506DiracDualIdentityECHessianCartanECNormalPrimitiveDiagonalActual
        0
        positiveP506DiracDualIdentityECHessianCartanECNormalWholeSliceCurrent := by
  exact
    ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
      positiveSmoothUnifiedSource_generates_endpoint_eleven,
      primitiveDiagonalActual_timeAxisFidelity
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState,
      primitiveDiagonalActual_initialPrimitiveFidelity
        positiveSmoothUnifiedSource
        positiveP506MatterCurrentFullSynchronizedCauchyState⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeIdentityECHessianCartanECNormalPrimitiveDiagonalActual
