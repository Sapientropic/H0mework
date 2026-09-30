import H0mework.Chemistry.LAlanineJointNext.RuntimeJointRuntimeRegression

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Reentry.Runtime

open _root_.SaturationMonoid.ResponsibilityLifecycle
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution
open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open JointNext.Runtime Propagation.Interface
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section

def reentryParentRuntime : LivingRuntimeState jointRuntimeProcess := jointRuntimeAfterFirst

def reentryParentResult : JointResult :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .readiness with
  | .inl ⟨_, result, _⟩ => result
  | .inr impossible => nomatch impossible

def reentryParentPhysical :
    Inertia.Interface.InertialStepReadout × Inertia.Interface.NuclearFrame × Energy.Interface.MolecularEnergyLedger :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .physical with
  | .inl ⟨_, physical⟩ => physical
  | .inr impossible => nomatch impossible

def reentryParentHeld : Matrix Basis Basis ℂ :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .held with
  | .inl ⟨_, current, _⟩ => current
  | .inr impossible => nomatch impossible

def reentryParentRealization :
    Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ × Matrix Basis Basis ℂ :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .realization with
  | .inl ⟨_, realization⟩ => realization
  | .inr impossible => nomatch impossible

def reentryParentTime : ℚ :=
  match jointRuntimeFacade.readoutAt reentryParentRuntime .clock with
  | .inl ⟨_, current, _⟩ => current
  | .inr impossible => nomatch impossible

def reentryParentFrame := reentryParentPhysical.2.1
def reentryParentLedger := reentryParentPhysical.2.2
def reentryParentMasses := reentryParentPhysical.1.masses
def reentryParentResidual := reentryParentRealization.2.2.2

theorem reentryParent_installed :
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .physical) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .held) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .realization) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .clock) ∧
    type_of% (jointRuntimeFace_factorizes reentryParentRuntime .readiness) :=
  ⟨jointRuntimeFace_factorizes reentryParentRuntime .physical,
    jointRuntimeFace_factorizes reentryParentRuntime .held,
    jointRuntimeFace_factorizes reentryParentRuntime .realization,
    jointRuntimeFace_factorizes reentryParentRuntime .clock,
    jointRuntimeFace_factorizes reentryParentRuntime .readiness⟩

theorem reentryParent_actual :
    reentryParentResult = jointSourceResult ∧
    reentryParentFrame = JointNext.Source.stepReadout.nuclear.target ∧
    reentryParentLedger = JointNext.Source.stepReadout.nuclear.targetLedger ∧
    reentryParentHeld = JointNext.Producer.exactTarget ∧
    reentryParentRealization.1 = JointNext.Source.targetRealized ∧
    reentryParentResidual = JointNext.Producer.totalRealizationResidual := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem reentryParent_residual :
    reentryParentRealization.1 - reentryParentHeld = reentryParentResidual := rfl

theorem reentryParent_error : ‖reentryParentResidual‖ < (1 : ℝ) / 10 ^ 8 :=
  (jointRuntime_realization_account reentryParentRuntime).2

theorem reentryParent_clock : reentryParentTime = 2 * Propagation.Producer.nativeClockStep :=
  jointRuntime_nextClock jointRuntimeSeed

theorem reentryParent_heldNorm : ‖reentryParentHeld‖ ≤ 10 := by
  change ‖JointNext.Producer.exactTarget‖ ≤ 10
  rw [JointNext.Producer.exactTarget_joint, StarAlgEquiv.norm_map]
  change ‖Unitary.conjStarAlgAut ℂ _ ElectronicFrame.Source.sourceUnitary
    ElectronicFrame.Producer.heldMatrix‖ ≤ 10
  rw [StarAlgEquiv.norm_map]
  exact ElectronicFrame.Producer.heldMatrix_norm_le_ten

theorem reentryParent_realizedNorm : ‖reentryParentRealization.1‖ < 11 := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub reentryParentRealization.1 reentryParentHeld 0
  simp only [sub_zero] at triangle
  rw [reentryParent_residual] at triangle
  linarith [reentryParent_heldNorm, reentryParent_error]

end
end LAlanine40K2025.Reentry.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
