import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Exchange
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Source

/-! # Exact direction coordinates of the two actual feedback pulses

The six-q conditional pair generates the energy gap and exchange coherence. Their trigonometric
combination is exactly the seven-to-eight-q signed transfer. The two-pulse transfer and the
nine-q retained donor differ from their six-q values by less than the actual conditional mass.
This source readout does not assume a positive transfer or prepare another reservoir.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction

open Collision Resource Load.Producer.StrictThermal Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

-- The inherited PC-R-E-pointer carrier requires a deeper kernel normalization stack.
set_option maxRecDepth 4096

/-- The actual six-q conditional PC-R pair, with its original unnormalized weight. -/
def sourcePair : JointMatrix Load.Source.PairController :=
  Powered.Dynamics.systemReduce (suppliedBlock receivedState)

/-- Donor energy minus PC energy in that same pair. -/
def sourceGap : ℝ :=
  energy Powered.Producer.poweredTotalHamiltonian (bathReduce sourcePair) -
    energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair)

/-- The independent coherence contraction of that same pair. -/
def sourceCoherence : ℝ := coherence Powered.Producer.poweredTotalHamiltonian sourcePair
def sourceMass : ℝ := sourcePair.trace.re

theorem native_pair_add (s t : ℝ) (rho : JointMatrix Load.Source.PairController) :
    Quantum.conjugation (Native.pairFlow (s + t)) rho =
      Quantum.conjugation (Native.pairFlow s) (Quantum.conjugation (Native.pairFlow t) rho) := by
  have raw := Dynamics.pairAdvance_add Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian Native.sourceCoupling s t rho
  simp only [Dynamics.pairAdvance_eq_unitary Powered.Producer.poweredTotalHamiltonian
    Powered.Producer.poweredTotalHamiltonian_hermitian] at raw
  simp only [Quantum.conjugation_apply, Native.pairFlow]
  exact raw

theorem native_pc_exchange (time : ℝ) (rho : JointMatrix Load.Source.PairController) :
    energy Powered.Producer.poweredTotalHamiltonian
      (systemReduce (Quantum.conjugation (Native.pairFlow time) rho)) =
    energy Powered.Producer.poweredTotalHamiltonian
      (systemReduce (Quantum.conjugation
        (Exchange.exchangeUnitary (Native.sourceCoupling * time)) rho)) := by
  rw [Native.pairFlow_factor]
  change energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (Unitary.conjStarAlgAut ℂ _
      (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) *
        Exchange.exchangeUnitary (Native.sourceCoupling * time)) rho)) = _
  rw [Unitary.conjStarAlgAut_mul_apply]
  change energy Powered.Producer.poweredTotalHamiltonian
    (systemReduce (Quantum.localConjugation (Native.freePCUnitary time) (Native.freePCUnitary time)
      (Quantum.conjugation (Exchange.exchangeUnitary (Native.sourceCoupling * time)) rho))) = _
  rw [Quantum.systemReduce_local_conjugation, Native.freePC_energy]

theorem seven_pair : Powered.Dynamics.systemReduce (suppliedBlock received) =
    Quantum.conjugation (Native.pairFlow (nativeClockStep : ℝ)) sourcePair := by
  change Powered.Dynamics.systemReduce (suppliedBlock (respondNext receivedState)) = _
  rw [suppliedBlock_next, supply_pair]
  rfl

theorem eight_pair : Powered.Dynamics.systemReduce (suppliedBlock supplied) =
    Quantum.conjugation (Native.pairFlow (2 * (nativeClockStep : ℝ))) sourcePair := by
  change Powered.Dynamics.systemReduce
    (suppliedBlock (respondNext (respondNext receivedState))) = _
  rw [suppliedBlock_next, supply_pair, suppliedBlock_next, supply_pair, ← native_pair_add]
  rw [← two_mul]
  rfl

theorem energy_at_seven : pcEnergyOf (suppliedBlock received) =
    Real.sin (nativeClockStep : ℝ) ^ 2 *
      energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair) +
    Real.cos (nativeClockStep : ℝ) ^ 2 *
      energy Powered.Producer.poweredTotalHamiltonian (bathReduce sourcePair) +
    (Real.sin (nativeClockStep : ℝ) * Real.cos (nativeClockStep : ℝ)) * sourceCoherence := by
  unfold pcEnergyOf pcMatrixOf
  rw [seven_pair, native_pc_exchange, Native.sourceCoupling_clock, exchange_energy,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub]
  rfl

theorem energy_at_eight_exchange : pcEnergyOf (suppliedBlock supplied) =
    energy Powered.Producer.poweredTotalHamiltonian
      (systemReduce (Quantum.conjugation
        (Exchange.exchangeUnitary (Real.pi - 2 * (nativeClockStep : ℝ))) sourcePair)) := by
  unfold pcEnergyOf pcMatrixOf
  rw [eight_pair, native_pc_exchange]
  have angle : Native.sourceCoupling * (2 * (nativeClockStep : ℝ)) =
      Real.pi - 2 * (nativeClockStep : ℝ) := by
    calc
      _ = 2 * (Native.sourceCoupling * (nativeClockStep : ℝ)) := by ring
      _ = _ := by rw [Native.sourceCoupling_clock]; ring
  rw [angle]

theorem first_transfer_exact : supplyTransfer receivedState =
    Real.cos (nativeClockStep : ℝ) ^ 2 * sourceGap +
      (Real.sin (nativeClockStep : ℝ) * Real.cos (nativeClockStep : ℝ)) * sourceCoherence := by
  change pcEnergyOf (suppliedBlock received) -
    energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair) = _
  rw [energy_at_seven]
  have circle : Real.sin (nativeClockStep : ℝ) ^ 2 =
      1 - Real.cos (nativeClockStep : ℝ) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (nativeClockStep : ℝ)]
  rw [circle]
  unfold sourceGap
  ring

theorem two_transfers_exact : supplyTransfer receivedState + supplyTransfer received =
    Real.sin (2 * (nativeClockStep : ℝ)) ^ 2 * sourceGap -
      (Real.sin (2 * (nativeClockStep : ℝ)) * Real.cos (2 * (nativeClockStep : ℝ))) *
        sourceCoherence := by
  change (pcEnergyOf (suppliedBlock received) -
      energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair)) +
    (pcEnergyOf (suppliedBlock supplied) - pcEnergyOf (suppliedBlock received)) = _
  rw [energy_at_eight_exchange, exchange_energy, Real.cos_pi_sub, Real.sin_pi_sub]
  have circle : Real.cos (2 * (nativeClockStep : ℝ)) ^ 2 =
      1 - Real.sin (2 * (nativeClockStep : ℝ)) ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq (2 * (nativeClockStep : ℝ))]
  rw [neg_sq, circle]
  unfold sourceGap sourceCoherence
  ring

theorem source_pair_positive : sourcePair.PosSemidef :=
  Powered.Dynamics.systemReduce_posSemidef _ (suppliedBlock_positive receivedState)

theorem source_mass_exact : sourceMass = (suppliedBlock receivedState).trace.re :=
  congrArg Complex.re (Powered.Dynamics.systemReduce_trace _)

theorem source_mass_strict : 0 < sourceMass ∧ sourceMass < 1 := by
  rw [source_mass_exact]
  exact received_mass_strict

theorem two_transfers_small : |supplyTransfer receivedState + supplyTransfer received| ≤
    8 * ‖Powered.Producer.poweredTotalHamiltonian‖ * (nativeClockStep : ℝ) * sourceMass := by
  have bound := near_pi_energy_error Powered.Producer.poweredTotalHamiltonian sourcePair
    source_pair_positive (2 * (nativeClockStep : ℝ))
  rw [← energy_at_eight_exchange] at bound
  have telescope : supplyTransfer receivedState + supplyTransfer received =
      pcEnergyOf (suppliedBlock supplied) -
        energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair) := by
    change (pcEnergyOf (suppliedBlock received) -
      energy Powered.Producer.poweredTotalHamiltonian (systemReduce sourcePair)) +
      (pcEnergyOf (suppliedBlock supplied) - pcEnergyOf (suppliedBlock received)) = _
    ring
  rw [telescope]
  convert bound using 1
  rw [abs_of_pos (mul_pos (by norm_num) nativeClock_small.1)]
  unfold sourceMass
  ring

/-- Source-only scalar whose strict sign decides the actual second transfer. -/
def secondDirection : ℝ :=
  (Real.sin (2 * (nativeClockStep : ℝ)) ^ 2 - Real.cos (nativeClockStep : ℝ) ^ 2) * sourceGap -
    (Real.sin (2 * (nativeClockStep : ℝ)) * Real.cos (2 * (nativeClockStep : ℝ)) +
      Real.sin (nativeClockStep : ℝ) * Real.cos (nativeClockStep : ℝ)) * sourceCoherence

theorem second_transfer_exact : supplyTransfer received = secondDirection := by
  unfold secondDirection
  linear_combination two_transfers_exact - first_transfer_exact

def returnBudget : ℝ := 1944 * (nativeClockStep : ℝ) * sourceMass

theorem two_transfers_source_bound :
    |supplyTransfer receivedState + supplyTransfer received| ≤ returnBudget := by
  refine two_transfers_small.trans ?_
  calc
    _ ≤ 8 * 243 * (nativeClockStep : ℝ) * sourceMass := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left poweredTotalHamiltonian_norm_le (by norm_num))
          nativeClock_small.1.le) source_mass_strict.1.le
    _ = returnBudget := by unfold returnBudget; ring

theorem return_budget_lt_mass : returnBudget < sourceMass := by
  have small : 1944 * (nativeClockStep : ℝ) < 1 := by
    rw [nativeClockStep_exact]
    norm_num
  simpa only [returnBudget, one_mul] using
    mul_lt_mul_of_pos_right small source_mass_strict.1

theorem second_transfer_interval :
    -supplyTransfer receivedState - returnBudget ≤ supplyTransfer received ∧
      supplyTransfer received ≤ -supplyTransfer receivedState + returnBudget := by
  exact ⟨by linarith [(abs_le.mp two_transfers_source_bound).1],
    by linarith [(abs_le.mp two_transfers_source_bound).2]⟩

theorem executed_remaining_return :
    |donorRemainingOf (suppliedBlock executed) -
      donorRemainingOf (suppliedBlock receivedState)| ≤ returnBudget := by
  have paid := two_responses_paid
  have difference : donorRemainingOf (suppliedBlock executed) -
      donorRemainingOf (suppliedBlock receivedState) =
      -(supplyTransfer receivedState + supplyTransfer received) := by linarith
  rw [difference, abs_neg]
  exact two_transfers_source_bound

theorem nontrivial_positive_first_forces_negative_second
    (first : sourceMass ≤ supplyTransfer receivedState) : supplyTransfer received < 0 := by
  linarith [second_transfer_interval.2, return_budget_lt_mass]

theorem nontrivial_negative_first_forces_positive_second
    (first : supplyTransfer receivedState ≤ -sourceMass) : 0 < supplyTransfer received := by
  linarith [second_transfer_interval.1, return_budget_lt_mass]

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
