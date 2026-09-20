import H0mework.Physics.SourceFormation.Consumer
import H0mework.Physics.SourceFamily.EvolutionState

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource StageNineHolonomicField
open StageNineDiracDualFormNativeJointResidualCarrier
open StageNineFormNativeGaugeAuxiliaryIntegratedVariation StageNineFormNativeGaugeAuxiliaryVariation
open StageNineFormNativeP286GaugeYangMillsReadout StageNineFormNativeP286GaugePointwiseEquation
open StageNineP286SourceNativeReducedEntropyDescent
open StageNineP286SourceNativeCenteredReducedEntropyIteration
open StageNineP286SourceNativeCenteredReducedEntropySafeStep
open StageNineDiracDualFormNativeCartanReactionCurrentRestart
open Stage9C.Reduction

noncomputable section

abbrev State (source : SmoothUnifiedSource) := P286CenteredReducedEntropyStateAt source

/-- The original constitutive preparation consumes the unconditional
whole-field realization, including sources with a zero vacuum amplitude. -/
def initialState (source : SmoothUnifiedSource) : State source :=
  p286CenteredReducedEntropyInitialState source (MotherFamilyOccurrence.materialField source)
    (ArbitrarySourceFormation.material_realization source).1
    (ArbitrarySourceFormation.material_realization source).2.1

private theorem material_pointwise_zero (source : SmoothUnifiedSource) (point : BasePoint) :
    OnDiracDualFormNativePointwiseJointZeroFiber source (MotherFamilyOccurrence.materialField source) point :=
  (diracDualFormNativeJointZeroFiber_iff_pointwise source _).1
    (ArbitrarySourceFormation.material_joint_zero source) point

theorem material_auxiliary_equation (source : SmoothUnifiedSource) :
    FormNativeP286GaugeAuxiliaryPointwiseEquation source (MotherFamilyOccurrence.materialField source) := by
  intro point
  exact (formNativeP286GaugeAuxiliaryEulerResidual_eq_zero_iff _ _).1
    ((onDiracDualFormNativePointwiseJointZeroFiber_iff_components _ _ _).1
      (material_pointwise_zero source point)).2.2.1

theorem material_connection_equation (source : SmoothUnifiedSource) :
    FormNativeP286GaugeConnectionPointwiseEquation source (MotherFamilyOccurrence.materialField source) := by
  apply (holonomicFormNativeP286GaugeEulerThreeForm_eq_zero_iff_pointwiseEquation _ _).1
  funext point
  exact ((onDiracDualFormNativePointwiseJointZeroFiber_iff_components _ _ _).1
    (material_pointwise_zero source point)).2.2.2.2.1

theorem initial_current (source : SmoothUnifiedSource) :
    (initialState source).current = MotherFamilyOccurrence.materialField source := by
  change p286ReducedEntropyBase source (MotherFamilyOccurrence.materialField source) = _
  exact ((formNativeP286GaugeAuxiliaryPointwiseEquation_iff_fixedReadout source _
    (ArbitrarySourceFormation.material_realization source).2.1).1
      (material_auxiliary_equation source)).symm

theorem initial_cartan_fixed (source : SmoothUnifiedSource) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source (initialState source).current =
      (initialState source).current := by
  rw [initial_current]
  exact sourceActionGeneratedDiracDualCartanReactionCurrentRestart_idempotent _ _

theorem initial_fixed (source : SmoothUnifiedSource) (center : BasePoint) :
    p286CartanStateNext center (initialState source) = initialState source := by
  apply SourceFamilyEvolution.state_ext
  change p286CartanNext source (initialState source).current (initialState source).smooth
    (initialState source).nondegenerate center = _
  rw [p286CartanNext_eq_reducedNext_of_cartan_fixed _ _ _ _ _ (initial_cartan_fixed source)]
  have reduced := (p286CenteredReducedNext_all_eq_base_iff_masterEquations source
    (initialState source).current (initialState source).smooth (initialState source).nondegenerate).2 (by
      rw [(initialState source).reducedBase_eq]
      refine ⟨(initialState source).auxiliaryEquation, ?_⟩
      rw [initial_current]
      exact material_connection_equation source) center
  exact reduced.trans (initialState source).reducedBase_eq

def next (source : SmoothUnifiedSource) (center : BasePoint) : State source → State source :=
  p286CartanStateNext center

def stateAt (source : SmoothUnifiedSource) (center : BasePoint) : ℕ → State source
  | 0 => initialState source
  | epoch + 1 => next source center (stateAt source center epoch)

theorem state_succ (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    stateAt source center (epoch + 1) = next source center (stateAt source center epoch) := rfl

theorem whole_write (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    (stateAt source center (epoch + 1)).current =
      p286CartanNext source (stateAt source center epoch).current
        (stateAt source center epoch).smooth (stateAt source center epoch).nondegenerate center := rfl

theorem state_fixed (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    stateAt source center epoch = initialState source := by
  induction epoch with
  | zero => rfl
  | succ epoch induction =>
      rw [state_succ, induction]
      exact initial_fixed source center

theorem whole_current (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    (stateAt source center epoch).current = MotherFamilyOccurrence.materialField source := by
  rw [state_fixed, initial_current]

theorem current_joint_zero (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    DiracDualFormNativeJointZeroFiber source (stateAt source center epoch).current := by
  rw [whole_current]
  exact ArbitrarySourceFormation.material_joint_zero source

theorem cartan_fixed (source : SmoothUnifiedSource) (center : BasePoint) (epoch : ℕ) :
    sourceActionGeneratedDiracDualCartanReactionCurrentRestart source (stateAt source center epoch).current =
      (stateAt source center epoch).current := by
  rw [state_fixed]
  exact initial_cartan_fixed source

theorem initial_family (sourceStep : ℕ) :
    initialState (SourceFamily.sourceAt sourceStep) = SourceFamilyEvolution.initialState sourceStep := by
  apply SourceFamilyEvolution.state_ext
  rw [initial_current, SourceFamilyEvolution.initial_current, MotherFamilyOccurrence.materialField_family]

theorem initial_original : initialState Runtime.source = Stage9C.Revision.SpinPair.initialState :=
  (initial_family 0).trans SourceFamilyEvolution.initial_original

theorem state_family (sourceStep epoch : ℕ) :
    stateAt (SourceFamily.sourceAt sourceStep) 0 epoch = SourceFamilyEvolution.stateAt sourceStep epoch := by
  induction epoch with
  | zero => exact initial_family sourceStep
  | succ epoch induction =>
      rw [state_succ, SourceFamilyEvolution.state_succ, induction]
      rfl

theorem state_original (epoch : ℕ) :
    stateAt Runtime.source 0 epoch = (Stage9C.Revision.materialStateNext^[epoch])
      Stage9C.Revision.SpinPair.initialState :=
  (state_family 0 epoch).trans (SourceFamilyEvolution.state_original epoch)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.GeneralSourceEvolution
