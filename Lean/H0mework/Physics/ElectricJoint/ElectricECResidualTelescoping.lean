import H0mework.Physics.ElectricJoint.ElectricECSpacetimeOccurrence

/-!
# Telescoping changed reads on the complete live-electric EC action

The complete live-electric Einstein--Cartan action is already one dependent
five-leg write

```text
U0 --M/S/A--> U1 --P286 algebraic--> U2 --P286 live--> U3
   --Cartan--> U4 --EC--> U5.
```

This module does not construct another sector-local world.  It records the
exact algebraic form in which a reader settled by one native leg is compared
with its value on the final actual: the native read plus only the downstream
read-after-write deltas.

The delta is diagnostic.  It is never accepted by an action constructor and
does not define a correction.  If the generated downstream deltas cancel,
the native-leg settlement reaches the final actual directly.  Only a proved
nonzero total delta can demand a later joint action write.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping

open ProofFreeRicherAnholonomicSource
open StageNineDiracDualFormNativeCompleteJointLiveElectricECSpacetimeOccurrence
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction
open StageNineHolonomicField

noncomputable section

set_option autoImplicit false

/-- Read-after-write change of one additive observation.  Both endpoints are
already generated actuals; this definition is not a state update. -/
def completeJointLiveElectricECReadDelta
    {E : Type*}
    [AddGroup E]
    (read : StageNineHolonomicConfiguration → E)
    (before after : StageNineHolonomicConfiguration) : E :=
  read after - read before

namespace
  CompleteJointLiveElectricECSpacetimeOccurrence

/-- The final value of any additive reader is its value on the occurrence's
input current plus the five native action-leg changes.  This is an exact
dependency ledger on one source/current occurrence, not an iterative update
or a residual-driven constructor. -/
theorem read_final_eq_current_add_allActionDeltas
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    {E : Type*}
    [AddCommGroup E]
    (read : StageNineHolonomicConfiguration → E) :
    read occurrence.finalActual =
      read current +
        completeJointLiveElectricECReadDelta read current
          (occurrence.after .matterScalar) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .matterScalar)
          (occurrence.after .p286Algebraic) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286Algebraic)
          (occurrence.after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286LiveElectric)
          (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .cartan)
          occurrence.finalActual := by
  unfold completeJointLiveElectricECReadDelta
  abel

/-- Whole-nine-channel specialization of the exact five-leg telescope at the
dependent occurrence's own spacetime point. -/
theorem pointwiseJointResidual_final_eq_current_add_allActionDeltas
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current) :
    diracDualFormNativePointwiseJointResidual source occurrence.finalActual
        occurrence.point =
      diracDualFormNativePointwiseJointResidual source current
          occurrence.point +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual source actual
              occurrence.point)
          current (occurrence.after .matterScalar) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual source actual
              occurrence.point)
          (occurrence.after .matterScalar)
          (occurrence.after .p286Algebraic) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual source actual
              occurrence.point)
          (occurrence.after .p286Algebraic)
          (occurrence.after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual source actual
              occurrence.point)
          (occurrence.after .p286LiveElectric)
          (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta
          (fun actual =>
            diracDualFormNativePointwiseJointResidual source actual
              occurrence.point)
          (occurrence.after .cartan)
          occurrence.finalActual :=
  read_final_eq_current_add_allActionDeltas occurrence
    (fun actual =>
      diracDualFormNativePointwiseJointResidual source actual occurrence.point)

/-- A reader native to the first joint matter/scalar/adjoint leg reaches the
final actual by exactly the four downstream changed reads. -/
theorem read_final_eq_matterScalar_native_add_downstreamDeltas
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    {E : Type*}
    [AddCommGroup E]
    (read : StageNineHolonomicConfiguration → E) :
    read occurrence.finalActual =
      read (occurrence.after .matterScalar) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .matterScalar)
          (occurrence.after .p286Algebraic) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286Algebraic)
          (occurrence.after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286LiveElectric)
          (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .cartan)
          occurrence.finalActual := by
  unfold completeJointLiveElectricECReadDelta
  abel

/-- A reader native to the algebraic P286 leg has exactly the live-electric,
Cartan, and Einstein--Cartan suffix deltas. -/
theorem read_final_eq_p286Algebraic_native_add_downstreamDeltas
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    {E : Type*}
    [AddCommGroup E]
    (read : StageNineHolonomicConfiguration → E) :
    read occurrence.finalActual =
      read (occurrence.after .p286Algebraic) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286Algebraic)
          (occurrence.after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286LiveElectric)
          (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .cartan)
          occurrence.finalActual := by
  unfold completeJointLiveElectricECReadDelta
  abel

/-- A reader native to the live-electric P286 leg has exactly the Cartan and
Einstein--Cartan suffix deltas. -/
theorem read_final_eq_p286LiveElectric_native_add_downstreamDeltas
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    {E : Type*}
    [AddCommGroup E]
    (read : StageNineHolonomicConfiguration → E) :
    read occurrence.finalActual =
      read (occurrence.after .p286LiveElectric) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .p286LiveElectric)
          (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .cartan)
          occurrence.finalActual := by
  unfold completeJointLiveElectricECReadDelta
  abel

/-- A Cartan-native reader differs from its final value by exactly the last
Einstein--Cartan changed read. -/
theorem read_final_eq_cartan_native_add_einsteinCartanDelta
    {source : SmoothUnifiedSource}
    {current : StageNineHolonomicConfiguration}
    (occurrence :
      CompleteJointLiveElectricECSpacetimeOccurrence source current)
    {E : Type*}
    [AddCommGroup E]
    (read : StageNineHolonomicConfiguration → E) :
    read occurrence.finalActual =
      read (occurrence.after .cartan) +
        completeJointLiveElectricECReadDelta read
          (occurrence.after .cartan)
          occurrence.finalActual := by
  unfold completeJointLiveElectricECReadDelta
  abel

end
  CompleteJointLiveElectricECSpacetimeOccurrence

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCompleteJointLiveElectricECResidualTelescoping
