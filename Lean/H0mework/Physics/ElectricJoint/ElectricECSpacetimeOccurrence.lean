import H0mework.Physics.ElectricJoint.FixedOriginCoframeClosure
import H0mework.Physics.Recentering.HolonomicFullSpacetimeRecenterActionJetNaturality

/-!
# Live-electric Einstein--Cartan spacetime occurrences

The complete live-electric Einstein--Cartan operator already writes one
four-dimensional `StageNineHolonomicConfiguration` from one `(source,
current)`.  This module keeps that global actual authoritative and records a
dependent spacetime occurrence on it.

The occurrence exposes the exact action order

```text
current
  -> joint matter/adjoint/scalar temporal write
  -> P286 algebraic write
  -> P286 live-electric write
  -> Cartan/reaction write
  -> Einstein--Cartan write
```

Every before/after actual is computed from the same indexed source/current.
The matching contact is the canonical full-spacetime recentering of the
already generated final actual, not a point-indexed rerun used to manufacture
a second world.  Consequently the complete action-jet and residual bridges
are whole-carrier equalities on one dependent occurrence.  No residual,
support, seam, branch, target field, or zero-fiber receipt enters a write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionLiveElectricGlobalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointActionTemporalDevelopmentOperator
open StageNineDiracDualFormNativeCompleteJointP286LiveElectricCauchyOperator
open StageNineDiracDualFormNativeECFullCauchyLocalActualLift
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineDiracDualFormNativeP286CanonicalJointActionProducerCore
open StageNineDiracDualFormNativePointwiseActionJetCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterActionJetNaturality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

/-! ## Source-indexed action transition -/

/-- The five action-owned legs in their actual dependency order.  The first
leg is joint M/S because the authoritative temporal operator writes matter,
adjoint, and scalar from one occurrence-native profile. -/
inductive CompleteJointLiveElectricECWriteLeg where
  | matterScalar
  | p286Algebraic
  | p286LiveElectric
  | cartan
  | einsteinCartan
  deriving DecidableEq

/-- The native action operator assigned to one write leg.  This definition
does not select a branch: each leg is the already authoritative operator for
that carrier transition. -/
def completeJointLiveElectricECActionWrite
    (source : SmoothUnifiedSource)
    (leg : CompleteJointLiveElectricECWriteLeg)
    (before : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  match leg with
  | .matterScalar =>
      sourceActionGeneratedDiracDualCompleteJointTemporalDevelopmentOperator
        source before
  | .p286Algebraic =>
      diracDualFormNativeP286CanonicalGeneratedActual source before
  | .p286LiveElectric =>
      sourceActionGeneratedCompleteJointP286LiveElectricCauchyOperator
        source before
  | .cartan =>
      sourceActionGeneratedDiracDualCartanReactionCurrentRestart source before
  | .einsteinCartan =>
      sourceActionGeneratedDiracDualECFullCauchyLocalActualLift source before

/-! ## One dependent occurrence of one global write -/

/-- A spacetime occurrence is indexed by the exact source and current and
carries only its point.  All intermediate actuals below are canonical
projections of those indices, so a caller cannot supply an alternative
output, branch, or handoff receipt. -/
structure CompleteJointLiveElectricECSpacetimeOccurrence
    (_source : SmoothUnifiedSource)
    (_current : StageNineHolonomicConfiguration) where
  point : BasePoint

/-- Canonical source/current occurrence producer. -/
def sourceActionGeneratedCompleteJointLiveElectricECSpacetimeOccurrence
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    CompleteJointLiveElectricECSpacetimeOccurrence source current :=
  ⟨point⟩

namespace CompleteJointLiveElectricECSpacetimeOccurrence

/-- The before-actual of each native write leg. -/
def before
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    CompleteJointLiveElectricECWriteLeg → StageNineHolonomicConfiguration
  | .matterScalar => current
  | .p286Algebraic =>
      completeJointGlobalTemporalCurrent source current
  | .p286LiveElectric =>
      completeJointGlobalP286AlgebraicCurrent source current
  | .cartan =>
      completeJointLiveElectricGlobalP286Current source current
  | .einsteinCartan =>
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        source current

/-- The after-actual of each native write leg. -/
def after
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (_occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    CompleteJointLiveElectricECWriteLeg → StageNineHolonomicConfiguration
  | .matterScalar =>
      completeJointGlobalTemporalCurrent source current
  | .p286Algebraic =>
      completeJointGlobalP286AlgebraicCurrent source current
  | .p286LiveElectric =>
      completeJointLiveElectricGlobalP286Current source current
  | .cartan =>
      sourceActionGeneratedDiracDualCompleteJointLiveElectricGlobalDevelopmentOperator
        source current
  | .einsteinCartan =>
      sourceActionGeneratedDiracDualCompleteJointLiveElectricECGlobalDevelopmentOperator
        source current

/-- Every transition is exactly its source-owned action operator applied to
the occurrence's preceding actual. -/
theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    (leg : CompleteJointLiveElectricECWriteLeg) :
    occurrence.after leg =
      completeJointLiveElectricECActionWrite source leg
        (occurrence.before leg) := by
  cases leg <;>
    rfl

@[simp] theorem matterScalar_to_p286Algebraic_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    occurrence.after .matterScalar =
      occurrence.before .p286Algebraic :=
  rfl

@[simp] theorem p286Algebraic_to_p286LiveElectric_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    occurrence.after .p286Algebraic =
      occurrence.before .p286LiveElectric :=
  rfl

@[simp] theorem p286LiveElectric_to_cartan_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    occurrence.after .p286LiveElectric =
      occurrence.before .cartan :=
  rfl

@[simp] theorem cartan_to_einsteinCartan_handoff
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    occurrence.after .cartan =
      occurrence.before .einsteinCartan :=
  rfl

/-- The one final global actual of the occurrence. -/
abbrev finalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    StageNineHolonomicConfiguration :=
  occurrence.after .einsteinCartan

/-- Matching local contact obtained only by recentering the same final
actual at this occurrence. -/
def recenteredFinalActual
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration occurrence.finalActual occurrence.point

/-! ## Whole-carrier same-occurrence bridges -/

/-- The complete mother-action jet of the one final actual at the occurrence
is exactly its faithful recentered-origin read.  This is one whole-carrier
identity; no primitive or mixed-jet field is cast independently. -/
theorem generatedActionJet_eq_recenteredOrigin
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    generatedDiracDualFormNativePointwiseActionJet source
        occurrence.finalActual occurrence.point =
      generatedDiracDualFormNativePointwiseActionJet source
        occurrence.recenteredFinalActual 0 :=
  (generatedActionJet_fullyRecenter_origin_unconditional source
    occurrence.finalActual occurrence.point).symm

/-- The complete nine-channel residual is transported on that same dependent
occurrence.  It remains a readout and is never used to define a write. -/
theorem pointwiseJointResidual_eq_recenteredOrigin
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    diracDualFormNativePointwiseJointResidual source
        occurrence.finalActual occurrence.point =
      diracDualFormNativePointwiseJointResidual source
        occurrence.recenteredFinalActual 0 :=
  (pointwiseJointResidual_fullyRecenter_origin_unconditional source
    occurrence.finalActual occurrence.point).symm

end CompleteJointLiveElectricECSpacetimeOccurrence

/-! ## Fixed P506/L0 occurrence -/

private abbrev FixedInput : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

/-- Fixed-lineage occurrence of the source/current-only global write. -/
def fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence
    (point : BasePoint) :
    CompleteJointLiveElectricECSpacetimeOccurrence
      positiveSmoothUnifiedSource FixedInput :=
  sourceActionGeneratedCompleteJointLiveElectricECSpacetimeOccurrence
    positiveSmoothUnifiedSource FixedInput point

@[simp] theorem
    fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence_finalActual
    (point : BasePoint) :
    (fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point
      ).finalActual =
      fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual :=
  rfl

/-- The fixed final actual's complete action jet at every spacetime point is
the local-origin read of the same dependent occurrence. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopment_actionJet_eq_recenteredOrigin
    (point : BasePoint) :
    generatedDiracDualFormNativePointwiseActionJet
        positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual point =
      generatedDiracDualFormNativePointwiseActionJet
        positiveSmoothUnifiedSource
        ((fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point
          ).recenteredFinalActual) 0 := by
  exact
    (fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point
      ).generatedActionJet_eq_recenteredOrigin

/-- Fixed-lineage whole-residual counterpart of the same occurrence bridge.
It transports the nine-channel readout and does not manufacture a zero or a
successor. -/
theorem
    fixedP506L0CompleteJointLiveElectricECGlobalDevelopment_residual_eq_recenteredOrigin
    (point : BasePoint) :
    diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        fixedP506L0CompleteJointLiveElectricECGlobalDevelopmentActual point =
      diracDualFormNativePointwiseJointResidual positiveSmoothUnifiedSource
        ((fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point
          ).recenteredFinalActual) 0 := by
  exact
    (fixedP506L0CompleteJointLiveElectricECSpacetimeOccurrence point
      ).pointwiseJointResidual_eq_recenteredOrigin

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
