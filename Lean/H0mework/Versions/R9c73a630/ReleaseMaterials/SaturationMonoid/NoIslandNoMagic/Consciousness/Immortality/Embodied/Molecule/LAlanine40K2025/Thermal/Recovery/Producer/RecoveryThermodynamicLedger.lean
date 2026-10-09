import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Producer.SourceGeneratedLAlanineStrictThermalCost
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Quantum.PartialTraceCovariance

/-! # Local recovery consumers retain the actual PCE memory and account for control work

The source supplies both local unitaries and elapsed time. Their action is appended to
the existing origin action; both marginals, spectra and energy accounts read that same joint.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Load.Producer.RecoveryLedger

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Load.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Powered.Dynamics
open scoped Matrix ComplexOrder

noncomputable section

private theorem gibbsJoint_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty κ]
    (rho : Matrix ι ι ℂ) (energies : κ → ℝ) (beta : ℝ)
    (U V : Matrix.unitaryGroup (ι × κ) ℂ) :
    Load.Quantum.unitaryGibbsJoint rho energies beta (U * V) =
      Thermal.Quantum.conjugation U (Load.Quantum.unitaryGibbsJoint rho energies beta V) := by
  change Unitary.conjStarAlgAut ℂ _ (U * V)
      (Matrix.kronecker rho (Load.Quantum.gibbsEnvironment energies beta)) =
    Unitary.conjStarAlgAut ℂ _ U (Unitary.conjStarAlgAut ℂ _ V
      (Matrix.kronecker rho (Load.Quantum.gibbsEnvironment energies beta)))
  exact Unitary.conjStarAlgAut_mul_apply _ _ _

def localState (current : LoadState) (U : Matrix.unitaryGroup PairController ℂ)
    (V : Matrix.unitaryGroup (Fin 2) ℂ) (elapsed : ℚ) : LoadState :=
  ⟨current.localClock + elapsed, Load.Quantum.localUnitary U V * current.action⟩

variable (current : LoadState) (U : Matrix.unitaryGroup PairController ℂ)
  (V : Matrix.unitaryGroup (Fin 2) ℂ) (elapsed : ℚ)

theorem localState_joint : (localState current U V elapsed).joint =
    Load.Quantum.localConjugation U V current.joint := by
  exact gibbsJoint_mul loadParentCurrent.joint environmentEnergies 1
    (Load.Quantum.localUnitary U V) current.action

theorem localState_pcMarginal : systemReduce (localState current U V elapsed).joint =
    Thermal.Quantum.conjugation U (systemReduce current.joint) := by
  rw [localState_joint]
  exact Load.Quantum.systemReduce_local_conjugation U V current.joint

theorem localState_environmentMarginal : controllerReduce (localState current U V elapsed).joint =
    Thermal.Quantum.conjugation V (controllerReduce current.joint) := by
  rw [localState_joint]
  exact Load.Quantum.controllerReduce_local_conjugation U V current.joint

theorem localState_charpoly : (localState current U V elapsed).joint.charpoly = current.joint.charpoly := by
  rw [localState_joint]
  exact Work.Capacity.conjugated_charpoly current.joint (Load.Quantum.localUnitary U V)

theorem localState_spectrum :
    (localState current U V elapsed).positive.isHermitian.eigenvalues =
      current.positive.isHermitian.eigenvalues :=
  ((localState current U V elapsed).positive.isHermitian.eigenvalues_eq_eigenvalues_iff
    current.positive.isHermitian).mpr (localState_charpoly current U V elapsed)

theorem localState_pcEntropy : loadPCEntropy (localState current U V elapsed) = loadPCEntropy current := by
  unfold loadPCEntropy
  apply Thermal.Quantum.spectralEntropy_eq_of_charpoly
  rw [localState_pcMarginal]
  exact Work.Capacity.conjugated_charpoly _ U

def environmentEntropy (state : LoadState) : ℝ :=
  Thermal.Quantum.spectralEntropy (controllerReduce state.joint)
    (controllerReduce_posSemidef _ state.positive) ((controllerReduce_trace _).trans state.normalized)

theorem localState_environmentEntropy :
    environmentEntropy (localState current U V elapsed) = environmentEntropy current := by
  simp only [environmentEntropy, localState_environmentMarginal]
  exact Thermal.Quantum.spectralEntropy_unitary_conjugation (controllerReduce current.joint)
    (controllerReduce_posSemidef _ current.positive) ((controllerReduce_trace _).trans current.normalized) V

private theorem gibbs_energy_read (state : LoadState) :
    loadGibbsExcess state =
      environmentEnergy state.joint - Population.meanEnergy environmentEnergies environmentPMF -
        (environmentEntropy state - Population.entropy environmentPMF) := by
  simp only [loadGibbsExcess, Load.Quantum.environmentGibbsExcess,
    Load.Quantum.environmentEnergyChange, one_mul, environmentEntropy,
    environmentEnergy, controllerEnergy, environmentHamiltonian_eq]
  rfl

theorem localState_gibbsBalance :
    loadGibbsExcess (localState current U V elapsed) - loadGibbsExcess current =
      environmentEnergy (localState current U V elapsed).joint - environmentEnergy current.joint := by
  rw [gibbs_energy_read, gibbs_energy_read, localState_environmentEntropy]
  ring

theorem localState_entropyBalance :
    loadEntropyProduction (localState current U V elapsed) - loadEntropyProduction current =
      environmentEnergy (localState current U V elapsed).joint - environmentEnergy current.joint := by
  rw [loadEntropy_energyRead, loadEntropy_energyRead, localState_pcEntropy]
  ring

theorem localState_mutualInformation :
    loadMutualInformation (localState current U V elapsed) = loadMutualInformation current := by
  have entropy := localState_entropyBalance current U V elapsed
  have gibbs := localState_gibbsBalance current U V elapsed
  rw [loadEntropy_disposition, loadEntropy_disposition] at entropy
  linarith

private theorem commuting_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H rho : Matrix ι ι ℂ) (W : Matrix.unitaryGroup ι ℂ) (commutes : Commute H (W : Matrix ι ι ℂ)) :
    Collision.energy H (Thermal.Quantum.conjugation W rho) = Collision.energy H rho := by
  have stationary : Unitary.conjStarAlgAut ℂ _ W H = H := by
    rw [Unitary.conjStarAlgAut_apply, ← commutes.eq, Matrix.mul_assoc,
      Unitary.mul_star_self_of_mem W.property, Matrix.mul_one]
  have same := Work.Capacity.energy_unitary_conjugation H rho W
  rw [stationary] at same
  exact same

theorem localState_environmentEnergy
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    environmentEnergy (localState current U V elapsed).joint = environmentEnergy current.joint := by
  change Collision.energy (controllerHamiltonian 2) (controllerReduce (localState current U V elapsed).joint) =
    Collision.energy (controllerHamiltonian 2) (controllerReduce current.joint)
  rw [localState_environmentMarginal]
  exact commuting_energy _ _ V environmentFlow

theorem localState_gibbs
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    loadGibbsExcess (localState current U V elapsed) = loadGibbsExcess current := by
  have balance := localState_gibbsBalance current U V elapsed
  rw [localState_environmentEnergy current U V elapsed environmentFlow, sub_self] at balance
  exact sub_eq_zero.mp balance

theorem localState_entropy
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    loadEntropyProduction (localState current U V elapsed) = loadEntropyProduction current := by
  have balance := localState_entropyBalance current U V elapsed
  rw [localState_environmentEnergy current U V elapsed environmentFlow, sub_self] at balance
  exact sub_eq_zero.mp balance

omit current in
/-- Recovery preserves the strict entropy already generated by the actual first load action. -/
theorem recovered_first_strictEntropy
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    0 < loadEntropyProduction (localState (loadStateNext loadInitialState) U V elapsed) := by
  rw [localState_entropy _ U V elapsed environmentFlow]
  exact loadFirst_strictEntropyCost

/-- The existing powered capacity consumers read the actual PC marginal. -/
def pcRead (state : LoadState) : Powered.Producer.PoweredState where
  localClock := state.localClock
  joint := systemReduce state.joint
  positive := systemReduce_posSemidef _ state.positive
  normalized := (systemReduce_trace _).trans state.normalized

def pairEnergy (state : LoadState) : ℝ := Powered.Producer.poweredPairEnergy (pcRead state)

def recipientEnergy (state : LoadState) : ℝ := Powered.Producer.poweredControllerEnergy (pcRead state)

def pcInteractionEnergy (state : LoadState) : ℝ :=
  Collision.energy Powered.Source.sourceInteraction (pcRead state).joint

def totalEnergy (state : LoadState) : ℝ := Collision.energy loadTotalHamiltonian state.joint

def supplierDebit (before after : LoadState) : ℝ :=
  pairEnergy before + pcInteractionEnergy before - (pairEnergy after + pcInteractionEnergy after)

theorem pcEnergy_split (state : LoadState) :
    pcEnergy state.joint = pairEnergy state + recipientEnergy state + pcInteractionEnergy state :=
  Load.Source.totalEnergy_split_generic Work.Drive.fieldBaseline 2 Powered.Source.sourceInteraction
    (pcRead state).joint

theorem localState_pcEnergy
    (pcFlow : Commute Powered.Producer.poweredTotalHamiltonian (U : Matrix PairController PairController ℂ)) :
    pcEnergy (localState current U V elapsed).joint = pcEnergy current.joint := by
  change Collision.energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (localState current U V elapsed).joint) =
      Collision.energy Powered.Producer.poweredTotalHamiltonian (systemReduce current.joint)
  rw [localState_pcMarginal]
  exact commuting_energy _ _ U pcFlow

/-- C gains are charged to the held pair and the original PC interaction when Hpc is preserved. -/
theorem localState_recipient_paid
    (pcFlow : Commute Powered.Producer.poweredTotalHamiltonian (U : Matrix PairController PairController ℂ)) :
    recipientEnergy (localState current U V elapsed) - recipientEnergy current =
      supplierDebit current (localState current U V elapsed) := by
  have conserved := localState_pcEnergy current U V elapsed pcFlow
  rw [pcEnergy_split, pcEnergy_split] at conserved
  unfold supplierDebit
  linarith

def controlSwitchInWork (K : Matrix PairController PairController ℂ) (state : LoadState) : ℝ :=
  Collision.energy (bareHamiltonian K 2) state.joint - totalEnergy state

def controlSwitchOutWork (K : Matrix PairController PairController ℂ) (state : LoadState) : ℝ :=
  totalEnergy state - Collision.energy (bareHamiltonian K 2) state.joint

def controlWork (K : Matrix PairController PairController ℂ) (before after : LoadState) : ℝ :=
  controlSwitchInWork K before + controlSwitchOutWork K after

theorem localState_dwellEnergy (K : Matrix PairController PairController ℂ)
    (pcControl : Commute K (U : Matrix PairController PairController ℂ))
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    Collision.energy (bareHamiltonian K 2) (localState current U V elapsed).joint =
      Collision.energy (bareHamiltonian K 2) current.joint := by
  rw [bareEnergy_split, bareEnergy_split]
  change Collision.energy K (systemReduce (localState current U V elapsed).joint) +
      environmentEnergy (localState current U V elapsed).joint =
    Collision.energy K (systemReduce current.joint) + environmentEnergy current.joint
  rw [localState_pcMarginal, commuting_energy K _ U pcControl,
    localState_environmentEnergy current U V elapsed environmentFlow]

/-- The two actual Hamiltonian switches pay the complete total-energy change. -/
theorem localState_controlWork_balance (K : Matrix PairController PairController ℂ)
    (pcControl : Commute K (U : Matrix PairController PairController ℂ))
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    controlWork K current (localState current U V elapsed) =
      totalEnergy (localState current U V elapsed) - totalEnergy current := by
  unfold controlWork controlSwitchInWork controlSwitchOutWork
  rw [localState_dwellEnergy current U V elapsed K pcControl environmentFlow]
  ring

/-- The complete recovery protocol accounts for binding free energy and the cumulative entropy. -/
theorem localState_netAccount (K : Matrix PairController PairController ℂ)
    (pcControl : Commute K (U : Matrix PairController PairController ℂ))
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    (loadBindingAccountedFreeEnergy (localState current U V elapsed) - loadBindingAccountedFreeEnergy current) +
      (loadEntropyProduction (localState current U V elapsed) - loadEntropyProduction current) =
      controlWork K current (localState current U V elapsed) := by
  rw [localState_controlWork_balance current U V elapsed K pcControl environmentFlow]
  unfold totalEnergy loadBindingAccountedFreeEnergy loadPCFreeEnergy
  rw [loadEntropy_energyRead, loadEntropy_energyRead, Load.Source.totalEnergy_split,
    Load.Source.totalEnergy_split]
  ring

/-- Boundary work remains in the same recipient/supplier account throughout the control protocol. -/
theorem localState_control_recipient_ledger (K : Matrix PairController PairController ℂ)
    (pcControl : Commute K (U : Matrix PairController PairController ℂ))
    (environmentFlow : Commute (controllerHamiltonian 2) (V : Matrix (Fin 2) (Fin 2) ℂ)) :
    recipientEnergy (localState current U V elapsed) - recipientEnergy current =
      supplierDebit current (localState current U V elapsed) +
        controlWork K current (localState current U V elapsed) -
        (boundaryEnergy (localState current U V elapsed).joint - boundaryEnergy current.joint) := by
  rw [localState_controlWork_balance current U V elapsed K pcControl environmentFlow]
  unfold totalEnergy supplierDebit
  rw [Load.Source.totalEnergy_split, Load.Source.totalEnergy_split,
    localState_environmentEnergy current U V elapsed environmentFlow, pcEnergy_split, pcEnergy_split]
  ring

theorem localState_recipientCapacity_balance :
    (Powered.Producer.poweredControllerCapacity (pcRead (localState current U V elapsed)) -
      Powered.Producer.poweredControllerCapacity (pcRead current)) +
    (Powered.Producer.poweredControllerPassiveEnergy (pcRead (localState current U V elapsed)) -
      Powered.Producer.poweredControllerPassiveEnergy (pcRead current)) =
      recipientEnergy (localState current U V elapsed) - recipientEnergy current := by
  unfold Powered.Producer.poweredControllerCapacity Powered.Producer.poweredControllerPassiveEnergy
    Work.Capacity.ergotropy recipientEnergy Powered.Producer.poweredControllerEnergy
    Powered.Producer.poweredController controllerEnergy
  ring

theorem localState_pairCapacity_balance :
    (Powered.Producer.poweredPairCapacity (pcRead (localState current U V elapsed)) -
      Powered.Producer.poweredPairCapacity (pcRead current)) +
    (Powered.Producer.poweredPairPassiveEnergy (pcRead (localState current U V elapsed)) -
      Powered.Producer.poweredPairPassiveEnergy (pcRead current)) =
      pairEnergy (localState current U V elapsed) - pairEnergy current := by
  unfold Powered.Producer.poweredPairCapacity Powered.Producer.poweredPairPassiveEnergy
    Work.Drive.fieldCapacity Work.Capacity.ergotropy pairEnergy Powered.Producer.poweredPairEnergy
    Powered.Producer.poweredPair systemEnergy
  ring

theorem localState_pcPassiveEnergy :
    Work.Capacity.passiveEnergy Powered.Producer.poweredTotalHamiltonian
      (pcRead (localState current U V elapsed)).joint Powered.Producer.poweredTotalHamiltonian_hermitian
      (pcRead (localState current U V elapsed)).positive.isHermitian =
    Work.Capacity.passiveEnergy Powered.Producer.poweredTotalHamiltonian
      (pcRead current).joint Powered.Producer.poweredTotalHamiltonian_hermitian
      (pcRead current).positive.isHermitian := by
  apply Work.Capacity.passiveEnergy_eq_of_charpoly
  change (systemReduce (localState current U V elapsed).joint).charpoly = (systemReduce current.joint).charpoly
  rw [localState_pcMarginal]
  exact Work.Capacity.conjugated_charpoly _ U

theorem localState_pcCapacity_balance :
    Powered.Producer.poweredJointCapacity (pcRead (localState current U V elapsed)) -
      Powered.Producer.poweredJointCapacity (pcRead current) =
      pcEnergy (localState current U V elapsed).joint - pcEnergy current.joint := by
  unfold Powered.Producer.poweredJointCapacity Work.Capacity.ergotropy
  rw [localState_pcPassiveEnergy]
  change (pcEnergy (localState current U V elapsed).joint - _) - (pcEnergy current.joint - _) = _
  ring

/-- Redistributing the held PC resource does not replenish its whole-Hpc unitary work capacity. -/
theorem localState_pcCapacity
    (pcFlow : Commute Powered.Producer.poweredTotalHamiltonian (U : Matrix PairController PairController ℂ)) :
    Powered.Producer.poweredJointCapacity (pcRead (localState current U V elapsed)) =
      Powered.Producer.poweredJointCapacity (pcRead current) := by
  have balance := localState_pcCapacity_balance current U V elapsed
  rw [localState_pcEnergy current U V elapsed pcFlow, sub_self] at balance
  exact sub_eq_zero.mp balance

end

end LAlanine40K2025.Thermal.Load.Producer.RecoveryLedger
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
