import H0mework.Chemistry.LAlanineReentry.RuntimeReentryRuntimeRegression
import H0mework.Realization.Faces.ProjectionCoface

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def bondParentRuntime : LivingRuntimeState Reentry.Runtime.reentryRuntimeProcess :=
  Reentry.Runtime.reentryRuntimeAfterFirst

def bondParentResult : JointNext.Runtime.JointResult :=
  match Reentry.Runtime.reentryRuntimeFacade.readoutAt bondParentRuntime .readiness with
  | .inl ⟨_, result, _⟩ => result
  | .inr impossible => nomatch impossible

def bondParentPhysical :
    Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger :=
  match Reentry.Runtime.reentryRuntimeFacade.readoutAt bondParentRuntime .physical with
  | .inl ⟨_, physical⟩ => physical
  | .inr impossible => nomatch impossible

def bondParentHistory : Reentry.Runtime.ReentryHistory :=
  match Reentry.Runtime.reentryRuntimeFacade.readoutAt bondParentRuntime .history with
  | .inl ⟨_, history⟩ => history
  | .inr impossible => nomatch impossible

def bondParentFrame := bondParentPhysical.2.1
def bondParentLedger := bondParentPhysical.2.2
def bondParentFullState := bondParentResult.realized
def bondParentExactState := bondParentResult.held
def bondParentTime := bondParentResult.clock

theorem bondParent_installed :
    type_of% (Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .physical) ∧
    type_of% (Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .readiness) ∧
    type_of% (Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .history) ∧
    type_of% (Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .realization) :=
  ⟨Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .physical,
    Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .readiness,
    Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .history,
    Reentry.Runtime.reentryRuntimeFace_factorizes bondParentRuntime .realization⟩

theorem bondParent_actual :
    bondParentResult = Reentry.Runtime.generatedReentryAction.answer ∧
    bondParentFrame = Reentry.Source.stepReadout.nuclear.target ∧
    bondParentLedger = Reentry.Source.stepReadout.nuclear.targetLedger ∧
    bondParentFullState = Reentry.Source.targetRealized ∧
    bondParentHistory = Reentry.Runtime.reentrySourceHistory := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem bondParent_clock : bondParentTime = 3 * Propagation.Producer.nativeClockStep :=
  Reentry.Continuation.targetClock_exact

theorem bondParent_total_residual :
    bondParentFullState = bondParentExactState + bondParentResult.inheritedResidual + bondParentResult.newNumericalResidual ∧
    ‖bondParentResult.totalRealizationResidual‖ < (13 : ℝ) / 10 ^ 9 :=
  Reentry.Runtime.reentryRuntime_realization_account bondParentRuntime

theorem bondParent_nonzero_imaginary : ∃ i j, (bondParentFullState i j).im ≠ 0 :=
  Reentry.Producer.targetRealized_not_real_only

abbrev BondBase := Reentry.Runtime.reentryLivingRoot.toAuthoritativeRoot.source
abbrev BondLedger := BondBase.restructuringSource.toLedgerSource

/-- The bond target is read from the same event that generated the installed M3 state. -/
def bondPhysicalSourceEvent := Reentry.Runtime.reentryInitialGenerated.occurrence

theorem bondPhysicalTarget_commutes :
    Reentry.Runtime.reentryResponse Reentry.Runtime.reentryFirstSuccessor.targetCurrent = bondParentResult := rfl

end
end LAlanine40K2025.BondReadout.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
