import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ProjectedProbability
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ChargedVacancyAlgebra
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Source.SourceGeneratedReverseInteraction

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.ChargedVacancy

open Collision Powered.Dynamics ProjectedOrbit ProjectedProbability VacancyAlgebra
open Load.Producer.StrictThermal Load.Producer.HeatProbability Propagation.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

theorem sourceInteraction_time_small :
    (3 * (nativeClockStep : ℝ)) * ‖Powered.Source.sourceInteraction‖ ≤ 1 / 2 := by
  have bound := mul_le_mul_of_nonneg_left sourceInteraction_norm_le
    Load.Recovery.Control.recovery_duration_positive.le
  have exactTime : 3 * (nativeClockStep : ℝ) * 160 < 1 / 2 := by norm_num [nativeClockStep_exact]
  linarith

theorem source_interaction_vacancy_strict : 9 * (nativeClockStep : ℝ) ^ 2 <
    energy (Q 0) (Unitary.conjStarAlgAut ℂ (ControllerJoint Load.Source.Pair)
      (interactionUnitary (ι := Load.Source.Pair) Powered.Source.sourceInteraction
        Powered.Source.sourceInteraction_hermitian (3 * (nativeClockStep : ℝ)))
      (chargedInput Powered.Producer.sourceReceivedPair)) := by
  have support := Q_charged_support Powered.Producer.sourceReceivedPair
  have bound := projected_probability_lower Powered.Source.sourceInteraction
    Powered.Source.sourceInteraction_hermitian (Q 0) (Q 1)
    (chargedInput Powered.Producer.sourceReceivedPair)
    (show (Q (ι := Load.Source.Pair) 0).IsHermitian from Q_star 0)
    (show (Q (ι := Load.Source.Pair) 1).IsHermitian from Q_star 1)
    (Q_sq 0) (Q_norm 0) Q_disjoint (Q_receives_interaction Thermal.Source.energyHamiltonian)
    (chargedInput_positive _ Powered.Producer.sourceParentState.positive)
    support.1 support.2 (3 * (nativeClockStep : ℝ))
    Load.Recovery.Control.recovery_duration_positive.le sourceInteraction_time_small
  change (3 * (nativeClockStep : ℝ)) ^ 2 / 4 *
    energy ((Powered.Source.interaction Thermal.Source.energyHamiltonian)ᴴ *
      Powered.Source.interaction Thermal.Source.energyHamiltonian) (chargedInput _) ≤ _ at bound
  rw [interaction_charged_moment] at bound
  have factorPositive : 0 < (3 * (nativeClockStep : ℝ)) ^ 2 / 4 :=
    div_pos (sq_pos_of_pos Load.Recovery.Control.recovery_duration_positive) (by norm_num)
  have strict := mul_lt_mul_of_pos_left SourceMoment.source_received_moment_gt_four factorPositive
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem resonant_forward_factorization (H : Matrix ι ι ℂ) (gap : ℝ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H gap) V) (t : ℝ) :
    flowUnitary H gap V hH hV t =
      flowUnitary H gap 0 hH Matrix.isHermitian_zero t * interactionUnitary V hV t := by
  apply Subtype.ext
  change (flowUnitary H gap V hH hV t : ControllerJoint ι) =
    (flowUnitary H gap 0 hH Matrix.isHermitian_zero t : ControllerJoint ι) *
      (interactionUnitary V hV t : ControllerJoint ι)
  simp only [interactionUnitary, flowUnitary_matrix_exp]
  rw [interactionHamiltonian V]
  simp only [totalHamiltonian, add_zero, smul_add]
  exact Matrix.exp_add_of_commute _ _
    ((resonance.smul_left (-Complex.I)).smul_right (-Complex.I) |>.smul_left t |>.smul_right t)

theorem resonant_controller_energy (H : Matrix ι ι ℂ) (V : ControllerJoint ι)
    (hH : H.IsHermitian) (hV : V.IsHermitian)
    (resonance : Commute (bareHamiltonian H 2) V) (t : ℝ) (rho : ControllerJoint ι) :
    controllerEnergy 2 (coupledNext H 2 V hH hV t rho) =
      controllerEnergy 2 (Unitary.conjStarAlgAut ℂ (ControllerJoint ι)
        (interactionUnitary (ι := ι) V hV t) rho) := by
  rw [coupledNext, resonant_forward_factorization H 2 V hH hV resonance t,
    Unitary.conjStarAlgAut_mul_apply]
  exact Load.Recovery.Control.bare_controller_energy H hH t _

theorem source_threeTick_controller_deficit :
    controllerEnergy 2 (Powered.Producer.sourceAdvance (3 * (nativeClockStep : ℝ))
      (chargedInput Powered.Producer.sourceReceivedPair)) < 2 - 18 * (nativeClockStep : ℝ) ^ 2 := by
  rw [Powered.Producer.sourceAdvance, resonant_controller_energy _ _ _ _ Powered.Producer.sourceResonance]
  let U : Matrix.unitaryGroup (Load.Source.Pair × Fin 2) ℂ :=
    interactionUnitary (ι := Load.Source.Pair) Powered.Source.sourceInteraction
      Powered.Source.sourceInteraction_hermitian (3 * (nativeClockStep : ℝ))
  have trace : (Unitary.conjStarAlgAut ℂ (ControllerJoint Load.Source.Pair) U
      (chargedInput Powered.Producer.sourceReceivedPair)).trace = 1 := by
    rw [Unitary.conjStarAlgAut_apply]
    exact (Thermal.Quantum.unitary_conjugate_trace (chargedInput Powered.Producer.sourceReceivedPair) U).trans
      (chargedInput_trace _ Powered.Producer.sourceParentState.normalized)
  have complement := empty_probability
    (Unitary.conjStarAlgAut ℂ (ControllerJoint Load.Source.Pair)
      U (chargedInput Powered.Producer.sourceReceivedPair)) trace
  linarith [source_interaction_vacancy_strict]

end
end LAlanine40K2025.Thermal.Recovery.ChargedVacancy
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
