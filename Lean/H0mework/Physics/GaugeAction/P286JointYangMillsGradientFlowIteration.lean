import H0mework.Physics.GaugeAction.P286JointYangMillsGradientFlowRegularity

/-!
# Canonical finite iteration of the joint P286 Yang--Mills flow

The source-native joint Euler step already computes its next connection from
the complete action gradient and then recomputes curvature and the
constitutive auxiliary.  This module performs that same step recursively:

```text
exact current
  -> canonical joint step
  -> canonical joint step
  -> ...
```

There is no scheduler, stopping branch, residual-selected step size, or
supplied future state.  A finite trace is only the first `fuel + 1` iterates;
`fuel = 0` means observation exhaustion, not a physical terminal.

The final pairing theorem is the exact infinitesimal defect identity.  It
does not assert convergence or finite-step action descent; those require a
separate source-generated entropy/descent theorem.
-/

namespace SaturationMonoid.PhysicsCore
namespace StageNineP286JointYangMillsGradientFlowIteration

open ProofFreeRicherAnholonomicSource
open StageNineEnrichedProofFreeSource
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeConstitutiveElimination
open StageNineFormNativeP286GaugeGeometricFirstVariation
open StageNineFormNativeP286GaugePointwiseEquation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineGlobalIntegratedAction
open StageNineHolonomicField
open StageNineP286CanonicalDiagonalActionPrincipal
open StageNineP286GaugeConnectionVariation
open StageNineP286JointYangMillsGradientFlow
open StageNineP286JointYangMillsGradientFlowRegularity
open StageNineTopologicalP286GaugeThreeFormDuality
open SU7MotherLieAlgebra

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 100000

local instance gradientFlowIterationP286ModuleFinite :
    Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective

local instance gradientFlowIterationP286CoordinateIndexFintype :
    Fintype P286CoordinateIndex :=
  Fintype.ofFinite P286CoordinateIndex

/-! ## Canonical iteration -/

/-- The unique `epoch`-fold iterate of the source-native joint step. -/
def p286JointYangMillsEulerIterate
    (source : SmoothUnifiedSource) :
    Nat → StageNineHolonomicConfiguration →
      StageNineHolonomicConfiguration
  | 0, current => current
  | epoch + 1, current =>
      p286JointYangMillsEulerStep source
        (p286JointYangMillsEulerIterate source epoch current)

@[simp] theorem p286JointYangMillsEulerIterate_zero
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration) :
    p286JointYangMillsEulerIterate source 0 current = current :=
  rfl

@[simp] theorem p286JointYangMillsEulerIterate_succ
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (epoch : Nat) :
    p286JointYangMillsEulerIterate source (epoch + 1) current =
      p286JointYangMillsEulerStep source
        (p286JointYangMillsEulerIterate source epoch current) :=
  rfl

theorem p286JointYangMillsEulerIterate_coframe
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (epoch : Nat) :
    (p286JointYangMillsEulerIterate source epoch current).coframe =
      current.coframe := by
  induction epoch with
  | zero => rfl
  | succ epoch inductionHypothesis =>
      rw [p286JointYangMillsEulerIterate_succ,
        p286JointYangMillsEulerStep_coframe, inductionHypothesis]

theorem p286JointYangMillsEulerIterate_nondegenerate
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (epoch : Nat) :
    (p286JointYangMillsEulerIterate source epoch current).Nondegenerate := by
  induction epoch with
  | zero => exact nondegenerate
  | succ epoch inductionHypothesis =>
      exact p286JointYangMillsEulerStep_nondegenerate source _
        inductionHypothesis

theorem p286JointYangMillsEulerIterate_smooth
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (epoch : Nat) :
    (p286JointYangMillsEulerIterate source epoch current).Smooth := by
  induction epoch with
  | zero => exact smooth
  | succ epoch inductionHypothesis =>
      exact p286JointYangMillsEulerStep_smooth source _ inductionHypothesis
        (p286JointYangMillsEulerIterate_nondegenerate source current
          nondegenerate epoch)

/-- Every positive iterate is on the exact algebraic auxiliary shell. -/
theorem p286JointYangMillsEulerIterate_succ_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (epoch : Nat) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286JointYangMillsEulerIterate source (epoch + 1) current) := by
  rw [p286JointYangMillsEulerIterate_succ]
  exact p286JointYangMillsEulerStep_auxiliaryPointwiseEquation source _
    (p286JointYangMillsEulerIterate_nondegenerate source current
      nondegenerate epoch)

/-! ## Finite observation trace -/

/-- The first `fuel + 1` canonical iterates, including the input current. -/
def p286JointYangMillsEulerTrace
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration) :
    Fin (fuel + 1) → StageNineHolonomicConfiguration :=
  fun epoch => p286JointYangMillsEulerIterate source epoch.val current

@[simp] theorem p286JointYangMillsEulerTrace_zero
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration) :
    p286JointYangMillsEulerTrace source fuel current 0 = current :=
  rfl

@[simp] theorem p286JointYangMillsEulerTrace_last
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration) :
    p286JointYangMillsEulerTrace source fuel current (Fin.last fuel) =
      p286JointYangMillsEulerIterate source fuel current :=
  rfl

theorem p286JointYangMillsEulerTrace_next
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration)
    (epoch : Fin fuel) :
    p286JointYangMillsEulerTrace source fuel current epoch.succ =
      p286JointYangMillsEulerStep source
        (p286JointYangMillsEulerTrace source fuel current epoch.castSucc) := by
  exact p286JointYangMillsEulerIterate_succ source current epoch.val

theorem p286JointYangMillsEulerTrace_nondegenerate
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (epoch : Fin (fuel + 1)) :
    (p286JointYangMillsEulerTrace source fuel current epoch).Nondegenerate :=
  p286JointYangMillsEulerIterate_nondegenerate source current nondegenerate
    epoch.val

theorem p286JointYangMillsEulerTrace_smooth
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration)
    (smooth : current.Smooth)
    (nondegenerate : current.Nondegenerate)
    (epoch : Fin (fuel + 1)) :
    (p286JointYangMillsEulerTrace source fuel current epoch).Smooth :=
  p286JointYangMillsEulerIterate_smooth source current smooth nondegenerate
    epoch.val

theorem p286JointYangMillsEulerTrace_next_auxiliaryPointwiseEquation
    (source : SmoothUnifiedSource)
    (fuel : Nat)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (epoch : Fin fuel) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source
      (p286JointYangMillsEulerTrace source fuel current epoch.succ) := by
  exact p286JointYangMillsEulerIterate_succ_auxiliaryPointwiseEquation source
    current nondegenerate epoch.val

/-! ## Fixed traces and the exact infinitesimal defect -/

theorem p286JointYangMillsEulerIterate_eq_self_of_masterEquations
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (nondegenerate : current.Nondegenerate)
    (master :
      FormNativeP286GaugeAuxiliaryPointwiseEquation source current ∧
        FormNativeP286GaugeConnectionPointwiseEquation source current)
    (epoch : Nat) :
    p286JointYangMillsEulerIterate source epoch current = current := by
  have fixed : p286JointYangMillsEulerStep source current = current :=
    (p286JointYangMillsEulerStep_eq_self_iff_masterEquations source current
      nondegenerate).2 master
  induction epoch with
  | zero => rfl
  | succ epoch inductionHypothesis =>
      rw [p286JointYangMillsEulerIterate_succ, inductionHypothesis, fixed]

/-- The action Euler covector evaluated on its canonical positive gradient is
exactly the finite nonnegative defect. -/
theorem p286JointYangMillsActionGradient_pairing_eq_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (p286JointYangMillsActionGradient source current point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
      p286JointYangMillsActionDefect source current point := by
  let gradient := p286JointYangMillsActionGradient source current point
  let euler :=
    holonomicFormNativeP286GaugeEulerThreeForm source 0 current point
  calc
    p286GaugeOneFormThreeFormWedgeCoefficient gradient euler =
        p286GaugeThreeFormWedgeLinearDual euler gradient := rfl
    _ = p286GaugeOneFormPairingEquiv gradient gradient := by
      unfold gradient p286JointYangMillsActionGradient
      rw [p286GaugeOneFormPairingEquiv.apply_symm_apply]
    _ = p286JointYangMillsActionDefect source current point := by
      rfl

/-- Therefore the installed negative-gradient direction pairs with the exact
negative defect.  This is the infinitesimal descent identity; a finite-step
action inequality is deliberately not inferred from it. -/
theorem p286JointYangMillsNegativeGradient_pairing_eq_neg_defect
    (source : SmoothUnifiedSource)
    (current : StageNineHolonomicConfiguration)
    (point : BasePoint) :
    p286GaugeOneFormThreeFormWedgeCoefficient
        (-p286JointYangMillsActionGradient source current point)
        (holonomicFormNativeP286GaugeEulerThreeForm source 0 current point) =
      -p286JointYangMillsActionDefect source current point := by
  rw [show -p286JointYangMillsActionGradient source current point =
      (-1 : ℝ) • p286JointYangMillsActionGradient source current point by
    exact (neg_one_smul ℝ _).symm]
  rw [p286GaugeOneFormThreeFormWedgeCoefficient_smul_left,
    p286JointYangMillsActionGradient_pairing_eq_defect]
  ring

end
end StageNineP286JointYangMillsGradientFlowIteration
end PhysicsCore
end SaturationMonoid
