import H0mework.Physics.ElectricJoint.ElectricECSpacetimeOccurrence
import H0mework.Physics.ElectricJoint.ElectricECOccurrenceOperator
import H0mework.Physics.SynchronizedJoint.FixedLorentzGlobalActual
import H0mework.Realization.Reflexive.FieldProgression

/-!
# Fixed Lorentz-path current to a generated five-leg action step

The synchronized Lorentz-path occurrence has already generated one global
current.  At each physical point, the existing full-occurrence operator
canonically recenters that same current, runs the same five-leg mother action,
and takes all nine primitive origin values into one common global output.  This
module then applies the canonical P71/P80 time-step construction to that
already registered whole-field writer:

```text
Lorentz-path Final
  -> at every p: recenter the same current at p
  -> one five-leg M/S/A--P286--Cartan--EC occurrence
  -> assemble all nine origin outputs at p
  -> one common next section.
```

The action query reads the whole residual section, but its write is fixed
independently by the source/current-only five-leg compiler.  No residual,
support coordinate, target field, selector, branch, zero-fiber witness, or
completion payload enters that writer.  This is the local generated time edge
of P71/P80; it is not a claim of an ambient or indefinitely iterable flow.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessor

open ProofFreeRicherAnholonomicSource
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization
open StageNineDiracDualFormNativeCompleteJointActionFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceContactOperator
open StageNineDiracDualFormNativeCompleteJointLiveElectricECFullOccurrenceGlobalOperator
open StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual
open StageNineDiracDualFormNativeFixedP506CompleteJointLiveElectricOriginCoframeClosure
open StageNineDiracDualFormNativeFixedP506JointActionSectionResponse
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineHolonomicFullSpacetimeRecenterNaturality

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

private abbrev Source : SmoothUnifiedSource :=
  positiveSmoothUnifiedSource

private abbrev OriginalCurrent : StageNineHolonomicConfiguration :=
  FixedP506FormNativeJointActionSolvedSuccessor

private abbrev Current : StageNineHolonomicConfiguration :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathGlobalActual

/-- The exact earlier occurrence whose final output is the current consumed
by the five-leg mother-action event. -/
private abbrev PriorOccurrence :
    CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence
      Source OriginalCurrent :=
  fixedP506L0CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathOccurrence

/-- Exact current custody across the two generated occurrences. -/
theorem fixedP506L0LorentzPathFiveLegCurrent_eq_priorOccurrenceFinal :
    Current = PriorOccurrence.finalActual :=
  rfl

/-- The exact local current consumed at one physical occurrence.  It is the
canonical recentering of the same global Final, not an independently supplied
contact world. -/
private abbrev RecenteredCurrent (point : BasePoint) :
    StageNineHolonomicConfiguration :=
  fullyRecenterHolonomicConfiguration Current point

/-- Point-indexed five-leg action occurrence used by the whole-field compiler.
The outer point determines only the canonical recentering; the internal read
is fixed at its local origin before compilation. -/
def fixedP506L0LorentzPathFiveLegOccurrenceAt
    (point : BasePoint) :
    CompleteJointLiveElectricECSpacetimeOccurrence
      Source (RecenteredCurrent point) :=
  sourceActionGeneratedCompleteJointLiveElectricECSpacetimeOccurrence
    Source (RecenteredCurrent point) 0

/-- One common source/current-only output of all five native mother-action
occurrences, assembled on the complete spacetime carrier. -/
def fixedP506L0LorentzPathFiveLegSuccessor :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
    Source Current

@[simp] theorem fixedP506L0LorentzPathFiveLegOccurrence_before_matterScalar
    (point : BasePoint) :
    (fixedP506L0LorentzPathFiveLegOccurrenceAt point).before .matterScalar =
      RecenteredCurrent point :=
  rfl

/-- Every transition of the exact occurrence is the pre-registered native
action write on its exact preceding actual. -/
theorem fixedP506L0LorentzPathFiveLegOccurrence_after_eq_actionWrite
    (point : BasePoint)
    (leg : CompleteJointLiveElectricECWriteLeg) :
    (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after leg =
      completeJointLiveElectricECActionWrite Source leg
        ((fixedP506L0LorentzPathFiveLegOccurrenceAt point).before leg) :=
  (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after_eq_actionWrite leg

/-- The four handoffs fix the complete action history before the output is
read; no completed field is carried as an event payload. -/
theorem fixedP506L0LorentzPathFiveLegOccurrence_handoffs
    (point : BasePoint) :
    (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after .matterScalar =
        (fixedP506L0LorentzPathFiveLegOccurrenceAt point).before .p286Algebraic ∧
      (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after .p286Algebraic =
        (fixedP506L0LorentzPathFiveLegOccurrenceAt point).before .p286LiveElectric ∧
      (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after .p286LiveElectric =
        (fixedP506L0LorentzPathFiveLegOccurrenceAt point).before .cartan ∧
      (fixedP506L0LorentzPathFiveLegOccurrenceAt point).after .cartan =
        (fixedP506L0LorentzPathFiveLegOccurrenceAt point).before .einsteinCartan := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Each exact five-leg event compiles to the contact consumed at that point
by the one whole-field output. -/
@[simp] theorem fixedP506L0LorentzPathFiveLegOccurrence_finalActual
    (point : BasePoint) :
    (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual =
      completeJointLiveElectricECFullOccurrenceContact Source Current point :=
  rfl

/-- The global output's entire primitive inventory at one point is the local
origin inventory of the exact five-leg event at that same point.  This is the
compiler/assembly recognition seam; no completed target is carried by the
event. -/
theorem fixedP506L0LorentzPathFiveLegSuccessor_primitiveValues
    (point : BasePoint) :
    (((fixedP506L0LorentzPathFiveLegSuccessor.coframe point,
          fixedP506L0LorentzPathFiveLegSuccessor.gravityConnection point),
        (fixedP506L0LorentzPathFiveLegSuccessor.gravityAuxiliary point,
          fixedP506L0LorentzPathFiveLegSuccessor.gravitySimplicityMultiplier point)),
      ((fixedP506L0LorentzPathFiveLegSuccessor.gaugeConnection point,
          fixedP506L0LorentzPathFiveLegSuccessor.gaugeAuxiliary point),
        ((fixedP506L0LorentzPathFiveLegSuccessor.scalar point,
            fixedP506L0LorentzPathFiveLegSuccessor.matter point),
          fixedP506L0LorentzPathFiveLegSuccessor.conjugateMatter point))) =
    (((((fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.coframe 0,
          (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.gravityConnection 0),
        ((fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.gravityAuxiliary 0,
          (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.gravitySimplicityMultiplier 0)),
      (((fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.gaugeConnection 0,
          (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.gaugeAuxiliary 0),
        (((fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.scalar 0,
            (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.matter 0),
          (fixedP506L0LorentzPathFiveLegOccurrenceAt point).finalActual.conjugateMatter 0)))) :=
  rfl

/-- Source-indexed whole-residual read and five-leg native write.  The write
does not inspect the read, so the changed-read support cannot select the next
actual. -/
def fixedP506L0LorentzPathFiveLegActionQuery :
    ReflexiveQuery StageNineHolonomicConfiguration
      (BasePoint → DiracDualFormNativePointwiseJointResidualCarrier) where
  read := diracDualFormNativeJointResidualSection Source
  write :=
    sourceActionGeneratedDiracDualCompleteJointLiveElectricECFullOccurrenceGlobalOperator
      Source

/-- The canonical two-section development generated by the exact action
query at the Lorentz-path current. -/
def fixedP506L0LorentzPathFiveLegGeneratedTimeStep :=
  reflexiveQueryGeneratedTimeStep
    fixedP506L0LorentzPathFiveLegActionQuery Current

@[simp] theorem fixedP506L0LorentzPathFiveLegGeneratedTimeStep_now_eq_current :
    fixedP506L0LorentzPathFiveLegGeneratedTimeStep.field.stateAt
        fixedP506L0LorentzPathFiveLegGeneratedTimeStep.now =
      Current :=
  rfl

/-- P71/P80 now supplies the generated next-section semantics after the
physics-native writer has been fixed. -/
@[simp] theorem fixedP506L0LorentzPathFiveLegGeneratedTimeStep_next_eq_successor :
    fixedP506L0LorentzPathFiveLegGeneratedTimeStep.field.stateAt
        fixedP506L0LorentzPathFiveLegGeneratedTimeStep.next =
      fixedP506L0LorentzPathFiveLegSuccessor :=
  rfl

/-- The observation on the generated step is exactly the whole residual
readout of the same source. -/
theorem fixedP506L0LorentzPathFiveLegGeneratedTimeStep_observe_eq_residualSection
    (actual : StageNineHolonomicConfiguration) :
    fixedP506L0LorentzPathFiveLegGeneratedTimeStep.field.observe actual =
      diracDualFormNativeJointResidualSection Source actual :=
  rfl

/-- The successor stays on the same fixed P506/L0 source lineage. -/
theorem fixedP506L0LorentzPathFiveLegSuccessor_exactLineage :
    Source.stageEight.generatedP506L0Lineage =
      canonicalP506SourceAffineL0ObservableLineageReference :=
  fixedP506FormNativeJointActionSolvedSuccessor_exactLineage

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CompleteJointActionSpacetimeSectionCartanECSynchronizedLorentzPathFiveLegSuccessor
