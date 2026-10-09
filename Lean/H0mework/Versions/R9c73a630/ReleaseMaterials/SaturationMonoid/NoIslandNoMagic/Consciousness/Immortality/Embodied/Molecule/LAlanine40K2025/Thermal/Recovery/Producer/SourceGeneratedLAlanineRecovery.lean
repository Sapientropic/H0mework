import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Dynamics.RememberedRefocusBound
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Source.SourceGeneratedReverseInteraction
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer.RecoveryThermodynamicLedger
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Runtime.LoadRuntimeStrictCost

/-! # The actual loaded joint generates a source-paid near-full controller recovery -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Producer

open Powered.Dynamics Load.Source Load.Producer Load.Recovery.Control
open Load.Producer.StrictThermal Load.Producer.RecoveryLedger
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator

noncomputable section

def recoveryReceivedState : LoadState :=
  Load.Runtime.loadCurrentState Load.Runtime.loadRuntimeAfterFirst.state.current

theorem recoveryReceived_actual : recoveryReceivedState = loadStateNext loadInitialState := rfl

def recoveryStep (current : LoadState) : LoadState :=
  localState current (minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
    (environmentUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
    (3 * Propagation.Producer.nativeClockStep)

def recoveryStateFirst : LoadState := recoveryStep recoveryReceivedState

def recoveryHamiltonian : Matrix PairController PairController ℂ :=
  totalHamiltonian Work.Drive.fieldBaseline 2 (-Powered.Source.sourceInteraction)

theorem recoveryHamiltonian_flow : Commute recoveryHamiltonian
    (minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)) : Matrix PairController PairController ℂ) :=
  observable_commutes_with_flow _ _ _ _ _ _ _ (Commute.refl _)

def recoveryWork (current : LoadState) : ℝ :=
  controlWork recoveryHamiltonian current (recoveryStep current)

theorem recoveryStep_joint (current : LoadState) :
    (recoveryStep current).joint = Load.Quantum.localConjugation
      (minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
      (environmentUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ))) current.joint :=
  localState_joint _ _ _ _

theorem recoveryStep_environmentEnergy (current : LoadState) :
    environmentEnergy (recoveryStep current).joint = environmentEnergy current.joint :=
  localState_environmentEnergy _ _ _ _ (environmentUnitary_commutes _)

theorem recoveryStep_entropy (current : LoadState) :
    loadEntropyProduction (recoveryStep current) = loadEntropyProduction current :=
  localState_entropy _ _ _ _ (environmentUnitary_commutes _)

theorem recoveryStep_gibbs (current : LoadState) :
    loadGibbsExcess (recoveryStep current) = loadGibbsExcess current :=
  localState_gibbs _ _ _ _ (environmentUnitary_commutes _)

theorem recoveryStep_pcEnergy (current : LoadState) :
    pcEnergy (recoveryStep current).joint = pcEnergy current.joint := by
  change Collision.energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (localState _ _ _ _).joint) = _
  rw [localState_pcMarginal]
  exact minimalPCUnitary_inclusive_energy _ _

theorem recoveryStep_recipient_paid (current : LoadState) :
    recipientEnergy (recoveryStep current) - recipientEnergy current =
      supplierDebit current (recoveryStep current) := by
  have balance := recoveryStep_pcEnergy current
  rw [pcEnergy_split, pcEnergy_split] at balance
  unfold supplierDebit
  linarith

theorem recoveryStep_workBalance (current : LoadState) :
    recoveryWork current = totalEnergy (recoveryStep current) - totalEnergy current :=
  localState_controlWork_balance _ _ _ _ _ recoveryHamiltonian_flow (environmentUnitary_commutes _)

theorem recoveryStep_netAccount (current : LoadState) :
    (loadBindingAccountedFreeEnergy (recoveryStep current) - loadBindingAccountedFreeEnergy current) +
      (loadEntropyProduction (recoveryStep current) - loadEntropyProduction current) = recoveryWork current :=
  localState_netAccount _ _ _ _ _ recoveryHamiltonian_flow (environmentUnitary_commutes _)

theorem recoveryStep_fullEnergyBalance (current : LoadState) :
    (pcEnergy (recoveryStep current).joint - pcEnergy current.joint) +
      (environmentEnergy (recoveryStep current).joint - environmentEnergy current.joint) +
      (boundaryEnergy (recoveryStep current).joint - boundaryEnergy current.joint) = recoveryWork current := by
  rw [recoveryStep_workBalance]
  simp only [totalEnergy, totalEnergy_split]
  ring

theorem recoveryStep_pcCapacity (current : LoadState) :
    Powered.Producer.poweredJointCapacity (pcRead (recoveryStep current)) =
      Powered.Producer.poweredJointCapacity (pcRead current) := by
  have balance := localState_pcCapacity_balance current
    (minimalPCUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
    (environmentUnitary (3 * (Propagation.Producer.nativeClockStep : ℝ)))
    (3 * Propagation.Producer.nativeClockStep)
  change Powered.Producer.poweredJointCapacity (pcRead (recoveryStep current)) -
    Powered.Producer.poweredJointCapacity (pcRead current) =
    pcEnergy (recoveryStep current).joint - pcEnergy current.joint at balance
  rw [recoveryStep_pcEnergy, sub_self] at balance
  exact sub_eq_zero.mp balance

theorem localConjugation_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    Function.Injective (Load.Quantum.localConjugation U V) := by
  intro A B same
  let action := Unitary.conjStarAlgAut ℂ (Matrix (ι × κ) (ι × κ) ℂ) (Load.Quantum.localUnitary U V)
  have equality : action A = action B := same
  exact action.injective equality

theorem recoveryStep_reflects_joint (left right : LoadState)
    (same : (recoveryStep left).joint = (recoveryStep right).joint) : left.joint = right.joint := by
  rw [recoveryStep_joint, recoveryStep_joint] at same
  exact localConjugation_injective _ _ same

theorem recoveryStep_clock (current : LoadState) :
    current.localClock < (recoveryStep current).localClock := by
  change current.localClock < current.localClock + 3 * Propagation.Producer.nativeClockStep
  exact lt_add_of_pos_right _ (mul_pos (by norm_num) Propagation.Producer.nativeClockStep_positive)

theorem localUnitary_star {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U : Matrix.unitaryGroup ι ℂ) (V : Matrix.unitaryGroup κ ℂ) :
    star (Load.Quantum.localUnitary U V) = Load.Quantum.localUnitary (star U) (star V) := by
  apply Subtype.ext
  simp only [Unitary.coe_star, Load.Quantum.localUnitary, Matrix.star_eq_conjTranspose,
    Matrix.kronecker, Matrix.conjTranspose_kronecker]

theorem localUnitary_mul {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (U U' : Matrix.unitaryGroup ι ℂ) (V V' : Matrix.unitaryGroup κ ℂ) :
    Load.Quantum.localUnitary U V * Load.Quantum.localUnitary U' V' =
      Load.Quantum.localUnitary (U * U') (V * V') := by
  apply Subtype.ext
  change Matrix.kronecker (U : Matrix ι ι ℂ) (V : Matrix κ κ ℂ) *
    Matrix.kronecker (U' : Matrix ι ι ℂ) (V' : Matrix κ κ ℂ) = _
  simp only [Matrix.kronecker, ← Matrix.mul_kronecker_mul]
  rfl

theorem referenceUnitary_local : Load.Recovery.recoveryUnitary =
    Load.Quantum.localUnitary
      (flowUnitary Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
        Work.Drive.fieldBaseline_hermitian Powered.Source.sourceInteraction_hermitian
        (-(3 * (Propagation.Producer.nativeClockStep : ℝ))))
      (environmentUnitary (-(Propagation.Producer.nativeClockStep : ℝ))) := by
  rw [Load.Recovery.recoveryUnitary, Load.Recovery.reverseBareUnitary_actual,
    source_barePCE_factor, Load.Recovery.parentLift, localUnitary_star,
    localUnitary_mul, star_one, one_mul]
  unfold loadParentUnitary
  rw [← flowUnitary_neg, ← flowUnitary_add]
  congr 2
  ring

theorem reference_pc : systemReduce Load.Recovery.recoveryNext.joint =
    Powered.Producer.sourceAdvance (-(3 * (Propagation.Producer.nativeClockStep : ℝ)))
      (systemReduce recoveryReceivedState.joint) := by
  rw [Load.Recovery.recoveryNext_actual, referenceUnitary_local]
  change systemReduce (Load.Quantum.localConjugation _ _ Load.Recovery.recoveryCurrent.joint) = _
  rw [Load.Quantum.systemReduce_local_conjugation]
  rfl

theorem recoveryStateFirst_controller_bound :
    2 - 25 * (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 8 ≤ recipientEnergy recoveryStateFirst := by
  have physical : recipientEnergy recoveryStateFirst =
      controllerEnergy 2 (systemReduce Load.Recovery.recoveryNext.joint) := by
    change controllerEnergy 2 (systemReduce (localState _ _ _ _).joint) = _
    rw [localState_pcMarginal, reference_pc]
    exact minimalPCUnitary_controller_energy _ _
  rw [physical]
  exact Load.Recovery.recoveryNext_controller_bound

theorem recoveryStateFirst_capacity_bound :
    2 - 25 * (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 ≤
      Powered.Producer.poweredControllerCapacity (pcRead recoveryStateFirst) := by
  let rho := Powered.Producer.poweredController (pcRead recoveryStateFirst)
  have positive := Powered.Producer.poweredController_positive (pcRead recoveryStateFirst)
  have normalized : rho.trace = 1 :=
    (controllerReduce_trace _).trans (pcRead recoveryStateFirst).normalized
  have bound := Load.Recovery.qubitFlip_capacity rho positive normalized
  change 2 * recipientEnergy recoveryStateFirst - 2 ≤
    Powered.Producer.poweredControllerCapacity (pcRead recoveryStateFirst) at bound
  linarith [recoveryStateFirst_controller_bound]

theorem recoveryStateFirst_strictCost :
    0 < loadGibbsExcess recoveryStateFirst ∧ 0 < loadEntropyProduction recoveryStateFirst := by
  change 0 < loadGibbsExcess (recoveryStep recoveryReceivedState) ∧
    0 < loadEntropyProduction (recoveryStep recoveryReceivedState)
  rw [recoveryStep_gibbs, recoveryStep_entropy, recoveryReceived_actual]
  exact ⟨loadFirst_strictGibbsCost, loadFirst_strictEntropyCost⟩

theorem recoveryStateFirst_hotEnvironment :
    (Propagation.Producer.nativeClockStep : ℝ) ^ 2 / 4 <
      environmentEnergy recoveryStateFirst.joint - environmentEnergy loadInitialState.joint := by
  change _ < environmentEnergy (recoveryStep recoveryReceivedState).joint - _
  rw [recoveryStep_environmentEnergy, recoveryReceived_actual]
  exact loadFirst_strictHeat

theorem recoveryStateFirst_next_received :
    (loadStateNext recoveryStateFirst).joint =
      loadAdvance (Propagation.Producer.nativeClockStep : ℝ) recoveryStateFirst.joint :=
  loadStateNext_joint _

theorem sourceGeneratedRecovery :
    type_of% recoveryReceived_actual ∧
    type_of% (recoveryStep_joint recoveryReceivedState) ∧
    type_of% recoveryStateFirst_controller_bound ∧
    type_of% recoveryStateFirst_capacity_bound ∧
    type_of% (recoveryStep_recipient_paid recoveryReceivedState) ∧
    type_of% (recoveryStep_workBalance recoveryReceivedState) ∧
    type_of% (recoveryStep_netAccount recoveryReceivedState) ∧
    type_of% (recoveryStep_pcCapacity recoveryReceivedState) ∧
    type_of% recoveryStateFirst_strictCost ∧
    type_of% recoveryStateFirst_hotEnvironment ∧
    type_of% recoveryStateFirst_next_received :=
  ⟨recoveryReceived_actual, recoveryStep_joint _, recoveryStateFirst_controller_bound,
    recoveryStateFirst_capacity_bound, recoveryStep_recipient_paid _, recoveryStep_workBalance _,
    recoveryStep_netAccount _, recoveryStep_pcCapacity _, recoveryStateFirst_strictCost,
    recoveryStateFirst_hotEnvironment, recoveryStateFirst_next_received⟩

end
end LAlanine40K2025.Thermal.Recovery.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
