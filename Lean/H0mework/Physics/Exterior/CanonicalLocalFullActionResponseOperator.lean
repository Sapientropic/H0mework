import H0mework.Physics.GaugeAction.FullSynchronizedCompleteP286ActionResponseOperator
import H0mework.Physics.MatterJets.MatterActionTemporalFirstGermResponse
import H0mework.Physics.MatterJets.MatterActionCompleteFirstGermResponse

/-!
# Stage-9 canonical local full-action response operator

This dependency-light operator composes the already action-generated local
responses in their dependency order:

```text
(proof-free source, current actual)
→ full synchronized gravity / matter response
→ complete P286 action response
→ temporal primal-matter first-germ response
→ complete primal-matter first-germ response
→ one canonical local actual.
```

Its only inputs are the proof-free source and the current actual.  It accepts
no residual, endpoint, response coefficient, branch choice, event, scheduler,
stationarity receipt, or equation certificate.  The matter residuals are read
internally from the action and their principal responses are unique.

The two matter legs retain their exact faithful-zero-fiber laws below.  No
global zero-fiber theorem is claimed for the whole composition: the P286 leg
is only origin-faithful in general.  Likewise this local operator is not a
source-time flow or a global evolution law.  If a later layer consumes an
external source-owned event provenance, it must transport that provenance
around this operator; it may not infer an event or branch from current
support.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCanonicalLocalFullActionResponseOperator

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFullSynchronizedActionResponseOperator
open StageNineFullSynchronizedCompleteP286ActionResponseOperator
open StageNineHolonomicField
open StageNineMatterActionCompleteFirstGermResponse
open StageNineMatterActionTemporalFirstGermResponse

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 200000

/-! ## Dependency-ordered local actuals -/

/-- The gravity/matter synchronized actual followed by its complete P286
action response. -/
def canonicalLocalFullActionP286Actual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  fullSynchronizedCompleteP286ActionResponseOperator source current

/-- The canonical temporal matter response generated from the P286 actual. -/
def canonicalLocalFullActionTemporalMatterActual
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedMatterTemporalFirstGermActual source
    (canonicalLocalFullActionP286Actual source current)

/-- The complete branch-free local action response. -/
def canonicalLocalFullActionResponseOperator
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  actionGeneratedMatterCompleteFirstGermActual source
    (canonicalLocalFullActionTemporalMatterActual source current)

@[simp] theorem canonicalLocalFullActionP286Actual_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    canonicalLocalFullActionP286Actual source current =
      fullSynchronizedCompleteP286ActionResponseOperator source current :=
  rfl

@[simp] theorem canonicalLocalFullActionTemporalMatterActual_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    canonicalLocalFullActionTemporalMatterActual source current =
      actionGeneratedMatterTemporalFirstGermActual source
        (canonicalLocalFullActionP286Actual source current) :=
  rfl

@[simp] theorem canonicalLocalFullActionResponseOperator_apply
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    canonicalLocalFullActionResponseOperator source current =
      actionGeneratedMatterCompleteFirstGermActual source
        (canonicalLocalFullActionTemporalMatterActual source current) :=
  rfl

/-- The later P286 and matter-response legs retain the multiplier generated
by the full synchronized action response.  Exposing this projection avoids
re-elaborating the complete response graph at downstream contacts. -/
@[simp] theorem
    canonicalLocalFullActionResponseOperator_gravitySimplicityMultiplier
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    (canonicalLocalFullActionResponseOperator source current
        |>.gravitySimplicityMultiplier) =
      fun _ => fullSynchronizedActionGravityMultiplier source current :=
  rfl

/-! ## Faithful zero fibers of the two matter-response legs -/

/-- The temporal matter leg is the identity exactly on its action-residual
zero fiber.  This is a property of that leg, not a global fixed-point claim
for the complete operator. -/
theorem canonicalLocalFullActionTemporalMatterActual_eq_p286_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    canonicalLocalFullActionTemporalMatterActual source current =
          canonicalLocalFullActionP286Actual source current ↔
      matterTemporalDiracYukawaFirstGermResidual source
          (canonicalLocalFullActionP286Actual source current) =
        0 := by
  unfold canonicalLocalFullActionTemporalMatterActual
    actionGeneratedMatterTemporalFirstGermActual
  rw [installMatterTemporalFirstGermResponse_eq_iff,
    actionGeneratedMatterTemporalFirstGermAcceleration_eq_zero_iff]

/-- The complete matter leg is the identity exactly on its complete
four-direction action-residual zero fiber. -/
theorem canonicalLocalFullActionResponseOperator_eq_temporal_iff
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    canonicalLocalFullActionResponseOperator source current =
          canonicalLocalFullActionTemporalMatterActual source current ↔
      matterCompleteDiracYukawaFirstGermResidual source
          (canonicalLocalFullActionTemporalMatterActual source current) =
        0 := by
  unfold canonicalLocalFullActionResponseOperator
  exact actionGeneratedMatterCompleteFirstGermActual_eq_iff source
    (canonicalLocalFullActionTemporalMatterActual source current)

end

end
  SaturationMonoid.PhysicsCore.StageNineCanonicalLocalFullActionResponseOperator
