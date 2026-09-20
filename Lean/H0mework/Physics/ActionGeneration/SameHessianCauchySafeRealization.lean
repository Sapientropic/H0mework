import H0mework.Physics.Cauchy.CoframeHolonomicCauchySafeRealization
import H0mework.Physics.IdentityGerms.CoframeHessianLocalActualLift
import H0mework.Physics.Geometry.IIPlusRestriction

/-!
# Source-generated same-Hessian Cauchy-safe realization

The identity-EC source already generates one holonomic coframe Hessian from
an exact Cartan base.  This module turns the corresponding quadratic local
actual and its Cauchy-safe realization into one source/base-indexed native
occurrence:

```text
source + Cartan base
  -> generated Hessian
  -> quadratic local actual
  -> Cauchy-safe realization of that same Hessian
```

No Hessian, target configuration, regularity certificate, nondegeneracy
proof, branch, or completed equation is accepted by the public producer.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace PhysicsCore
namespace StageNineSourceActionGeneratedSameHessianCauchySafeRealization

open ProofFreeRicherAnholonomicSource
open StageNineCoframeHolonomicCauchySafeRealization
open StageNineDiracDualFormNativeIdentityECHolonomicCoframeHessianLocalActualLift
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineIIPlusRestriction

noncomputable section

/-- Re-realize the Hessian generated from the exact source/base pair in the
canonical Cauchy-safe coframe material, while retaining every non-coframe
field of the corresponding quadratic local actual. -/
def sourceActionGeneratedSameHessianCauchySafeRealizationWrite
    (source : SmoothUnifiedSource)
    (cartanBase : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  let hessian :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianIncrement
      source cartanBase
  let before :=
    sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
      source cartanBase
  { before with
    coframe := coframeHolonomicSecondJetCauchySafeRealization hessian
    gravityAuxiliary := fun point =>
      physicalIIPlusBivector
        (coframeHolonomicSecondJetCauchySafeRealization hessian point) }

/-- A sealed occurrence generates both its quadratic input and its
Cauchy-safe output from the same source/base Hessian. -/
inductive SameHessianCauchySafeRealizationOccurrence
    (_source : SmoothUnifiedSource)
    (_cartanBase : StageNineHolonomicConfiguration) where
  | generated

def sourceActionGeneratedSameHessianCauchySafeRealizationOccurrence
    (source : SmoothUnifiedSource)
    (cartanBase : StageNineHolonomicConfiguration) :
    SameHessianCauchySafeRealizationOccurrence source cartanBase :=
  .generated

namespace SameHessianCauchySafeRealizationOccurrence

/-- The source-generated quadratic local actual is the unique input of this
occurrence; a sibling configuration cannot be supplied. -/
def before
    {source : SmoothUnifiedSource}
    {cartanBase : StageNineHolonomicConfiguration}
    (_occurrence :
      SameHessianCauchySafeRealizationOccurrence source cartanBase) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedIdentityECHolonomicCoframeHessianLocalActualLift
    source cartanBase

/-- The output is computed by the same-Hessian Cauchy-safe writer from the
occurrence's own generated input. -/
def after
    {source : SmoothUnifiedSource}
    {cartanBase : StageNineHolonomicConfiguration}
    (_occurrence :
      SameHessianCauchySafeRealizationOccurrence source cartanBase) :
    StageNineHolonomicConfiguration :=
  sourceActionGeneratedSameHessianCauchySafeRealizationWrite
    source cartanBase

@[simp] theorem after_eq_actionWrite
    {source : SmoothUnifiedSource}
    {cartanBase : StageNineHolonomicConfiguration}
    (_occurrence :
      SameHessianCauchySafeRealizationOccurrence source cartanBase) :
    _occurrence.after =
      sourceActionGeneratedSameHessianCauchySafeRealizationWrite
        source cartanBase :=
  rfl

end SameHessianCauchySafeRealizationOccurrence

#print axioms SameHessianCauchySafeRealizationOccurrence.after_eq_actionWrite

end
end StageNineSourceActionGeneratedSameHessianCauchySafeRealization
end PhysicsCore
end SaturationMonoid
