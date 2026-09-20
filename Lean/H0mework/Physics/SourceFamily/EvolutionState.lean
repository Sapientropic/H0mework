import H0mework.Physics.SourceFamily.Acceptance
import H0mework.Physics.CartanReduction.P286Descent

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamilyEvolution

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation
open StageNineFormNativeP286GaugeYangMillsReadout
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineP286SourceNativeCenteredReducedEntropyIteration
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open Stage9C.Reduction SourceFamily

noncomputable section

abbrev State (sourceStep : ℕ) := P286CenteredReducedEntropyStateAt (sourceAt sourceStep)

/-- The constitutive writer prepares the complete generated family field.
Its source index fixes the actual auxiliary equation throughout iteration. -/
def initialState (sourceStep : ℕ) : State sourceStep :=
  p286CenteredReducedEntropyInitialState (sourceAt sourceStep) (fieldAt sourceStep)
    (accepted sourceStep).smooth (accepted sourceStep).nondegenerate

theorem initial_current (sourceStep : ℕ) :
    (initialState sourceStep).current = fieldAt sourceStep := by
  change p286ReducedEntropyBase (sourceAt sourceStep) (fieldAt sourceStep) = _
  exact ((formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout
    (sourceAt sourceStep) (fieldAt sourceStep) (field_nondegenerate sourceStep)).1
      (field_auxiliary_equation sourceStep)).symm

/-- The center is the same physical origin used by the original writer.
Neither this source-material index nor the iteration index relabels BasePoint. -/
def next (sourceStep : ℕ) : State sourceStep → State sourceStep := p286CartanStateNext 0

def stateAt (sourceStep : ℕ) : ℕ → State sourceStep
  | 0 => initialState sourceStep
  | epoch + 1 => next sourceStep (stateAt sourceStep epoch)

theorem state_zero (sourceStep : ℕ) : stateAt sourceStep 0 = initialState sourceStep := rfl

theorem state_succ (sourceStep epoch : ℕ) :
    stateAt sourceStep (epoch + 1) = next sourceStep (stateAt sourceStep epoch) := rfl

theorem whole_write (sourceStep epoch : ℕ) :
    (stateAt sourceStep (epoch + 1)).current =
      p286CartanNext (sourceAt sourceStep) (stateAt sourceStep epoch).current
        (stateAt sourceStep epoch).smooth (stateAt sourceStep epoch).nondegenerate 0 := rfl

theorem source_auxiliary (sourceStep epoch : ℕ) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation (sourceAt sourceStep)
      (stateAt sourceStep epoch).current := (stateAt sourceStep epoch).auxiliaryEquation

theorem state_ext {source : SmoothUnifiedSource}
    {first second : P286CenteredReducedEntropyStateAt source}
    (current : first.current = second.current) : first = second := by
  cases first
  cases second
  cases current
  rfl

theorem initial_original : initialState 0 = Stage9C.Revision.SpinPair.initialState := by
  apply state_ext
  rw [initial_current, field_zero, Runtime.configuration_eq]
  rfl

theorem next_original (state : State 0) :
    next 0 state = Stage9C.Revision.materialStateNext state := rfl

theorem state_original (epoch : ℕ) :
    stateAt 0 epoch = (Stage9C.Revision.materialStateNext^[epoch])
      Stage9C.Revision.SpinPair.initialState := by
  induction epoch with
  | zero => exact initial_original
  | succ epoch induction =>
      rw [state_succ, next_original, induction, Function.iterate_succ_apply']

theorem cartan_fixed (sourceStep epoch : ℕ) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart (sourceAt sourceStep)
      (stateAt sourceStep epoch).current = (stateAt sourceStep epoch).current := by
  cases epoch with
  | zero =>
      rw [state_zero, initial_current]
      exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent _ _
  | succ epoch => exact p286CartanStateNext_cartan_fixed 0 (stateAt sourceStep epoch)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.SourceFamilyEvolution
