import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Producer.SourceChargedVacancy
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Refill.Dynamics.ProbabilityComparison
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer.SourceGeneratedLAlanineRecovery

set_option autoImplicit false
set_option maxRecDepth 4096

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.StrictRefill

open Collision Powered.Dynamics Load.Source Load.Producer Load.Producer.StrictThermal
open Load.Producer.HeatProbability Load.Producer.RecoveryLedger Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Producer
open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def vacancy : LoadedJoint := Matrix.kronecker (Q (ι := Pair) 0) (1 : Matrix (Fin 2) (Fin 2) ℂ)

theorem vacancy_hermitian : vacancy.IsHermitian := by
  change vacancyᴴ = vacancy
  rw [vacancy, Matrix.kronecker, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  rw [← Matrix.star_eq_conjTranspose, Q_star]

theorem vacancy_idempotent : vacancy * vacancy = vacancy := by
  simp only [vacancy, Matrix.kronecker, ← Matrix.mul_kronecker_mul, Q_sq, one_mul]

theorem vacancy_contractive : ‖vacancy‖ ≤ 1 :=
  (NonUnitalStarAlgHom.norm_apply_le (tensorLeft (κ := Fin 2)) (Q (ι := Pair) 0)).trans (Q_norm 0)

theorem vacancy_read (joint : LoadedJoint) : energy vacancy joint = energy (Q 0) (systemReduce joint) :=
  Load.Recovery.left_energy (Q 0) joint

theorem preparation_positive : Load.Recovery.preparationJoint.PosSemidef :=
  (chargedInput_positive _ Powered.Producer.sourceParentState.positive).kronecker environmentState_positive

theorem preparation_normalized : Load.Recovery.preparationJoint.trace = 1 := by
  rw [Load.Recovery.preparationJoint, Matrix.kronecker, Matrix.trace_kronecker,
    chargedInput_trace Powered.Producer.sourceReceivedPair Powered.Producer.sourceParentState.normalized,
    environmentState_trace, one_mul]

def referenceForward : Matrix.unitaryGroup (PairController × Fin 2) ℂ := star Load.Recovery.recoveryUnitary

theorem reference_forward_pc :
    systemReduce (Unitary.conjStarAlgAut ℂ LoadedJoint referenceForward Load.Recovery.preparationJoint) =
      Powered.Producer.sourceAdvance (3 * (nativeClockStep : ℝ))
        (chargedInput Powered.Producer.sourceReceivedPair) := by
  rw [referenceForward, referenceUnitary_local, localUnitary_star]
  change systemReduce (Load.Quantum.localConjugation _ _ Load.Recovery.preparationJoint) = _
  rw [Load.Quantum.systemReduce_local_conjugation, Load.Recovery.preparationJoint,
    Powered.Dynamics.systemReduce_tensor (chargedInput Powered.Producer.sourceReceivedPair) environmentState,
    environmentState_trace, one_smul]
  rw [← flowUnitary_neg, neg_neg]
  rfl

theorem received_from_reference : recoveryReceivedState.joint =
    Unitary.conjStarAlgAut ℂ LoadedJoint (referenceForward * Load.Recovery.recoveryErrorUnitary)
      Load.Recovery.preparationJoint := by
  calc
    _ = Unitary.conjStarAlgAut ℂ LoadedJoint referenceForward Load.Recovery.recoveryNext.joint := by
      rw [Load.Recovery.recoveryNext_actual, ← Unitary.conjStarAlgAut_mul_apply]
      simp only [referenceForward, Unitary.star_mul_self, Unitary.conjStarAlgAut_apply,
        OneMemClass.coe_one, star_one, one_mul, mul_one]
      rfl
    _ = _ := by
      rw [Load.Recovery.recoveryNext_from_preparation, ← Unitary.conjStarAlgAut_mul_apply]

theorem reference_forward_vacancy : 9 * (nativeClockStep : ℝ) ^ 2 <
    energy vacancy (Unitary.conjStarAlgAut ℂ LoadedJoint referenceForward Load.Recovery.preparationJoint) := by
  rw [vacancy_read, reference_forward_pc]
  have normalized := Powered.Producer.sourceAdvance_trace (3 * (nativeClockStep : ℝ))
    (chargedInput Powered.Producer.sourceReceivedPair)
  have complement := VacancyAlgebra.empty_probability
    (Powered.Producer.sourceAdvance (3 * (nativeClockStep : ℝ)) (chargedInput Powered.Producer.sourceReceivedPair))
    (normalized.trans (chargedInput_trace _ Powered.Producer.sourceParentState.normalized))
  linarith [ChargedVacancy.source_threeTick_controller_deficit]

theorem received_controller_deficit : recipientEnergy recoveryReceivedState <
    2 - 47 * (nativeClockStep : ℝ) ^ 2 / 8 := by
  have bound := ProbabilityComparison.unitary_error_lower vacancy Load.Recovery.preparationJoint
    preparation_positive preparation_normalized vacancy_hermitian vacancy_idempotent vacancy_contractive
    referenceForward Load.Recovery.recoveryErrorUnitary (5 * (nativeClockStep : ℝ) / 4)
    (div_nonneg (mul_nonneg (by norm_num) nativeClock_small.1.le) (by norm_num))
    Load.Recovery.recoveryError_norm
  rw [← received_from_reference] at bound
  have complement := VacancyAlgebra.empty_probability (systemReduce recoveryReceivedState.joint)
    ((Powered.Dynamics.systemReduce_trace _).trans recoveryReceivedState.normalized)
  rw [← vacancy_read] at complement
  change 2 * energy vacancy recoveryReceivedState.joint + recipientEnergy recoveryReceivedState = 2 at complement
  linarith [reference_forward_vacancy]

theorem source_generated_strict_refill :
    11 * (nativeClockStep : ℝ) ^ 2 / 4 <
      recipientEnergy recoveryStateFirst - recipientEnergy recoveryReceivedState := by
  linarith [received_controller_deficit, recoveryStateFirst_controller_bound]

theorem source_generated_strict_supplier_debit :
    11 * (nativeClockStep : ℝ) ^ 2 / 4 < supplierDebit recoveryReceivedState recoveryStateFirst := by
  change 11 * (nativeClockStep : ℝ) ^ 2 / 4 < supplierDebit recoveryReceivedState (recoveryStep recoveryReceivedState)
  rw [← recoveryStep_recipient_paid recoveryReceivedState]
  exact source_generated_strict_refill

theorem recoveryStep_interactionEnergy (current : LoadState) :
    pcInteractionEnergy (recoveryStep current) = pcInteractionEnergy current := by
  change energy Powered.Source.sourceInteraction (systemReduce (localState _ _ _ _).joint) =
    energy Powered.Source.sourceInteraction (systemReduce current.joint)
  rw [localState_pcMarginal]
  exact Load.Recovery.Control.minimalPCUnitary_interaction_energy _ _

theorem source_generated_strict_pair_debit :
    11 * (nativeClockStep : ℝ) ^ 2 / 4 < pairEnergy recoveryReceivedState - pairEnergy recoveryStateFirst := by
  have debit := source_generated_strict_supplier_debit
  change 11 * (nativeClockStep : ℝ) ^ 2 / 4 <
    pairEnergy recoveryReceivedState + pcInteractionEnergy recoveryReceivedState -
      (pairEnergy recoveryStateFirst + pcInteractionEnergy (recoveryStep recoveryReceivedState)) at debit
  rw [recoveryStep_interactionEnergy] at debit
  linarith

theorem source_refill_pair_balance :
    recipientEnergy recoveryStateFirst - recipientEnergy recoveryReceivedState =
      pairEnergy recoveryReceivedState - pairEnergy recoveryStateFirst := by
  have balance := recoveryStep_recipient_paid recoveryReceivedState
  unfold supplierDebit at balance
  rw [recoveryStep_interactionEnergy] at balance
  simpa only [recoveryStateFirst, add_sub_add_right_eq_sub] using balance

theorem strictRefillLower_positive : 0 < 11 * (nativeClockStep : ℝ) ^ 2 / 4 := by
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos nativeClock_small.1)) (by norm_num)

theorem sourceGeneratedStrictRefill : type_of% source_generated_strict_refill ∧
    type_of% source_generated_strict_supplier_debit ∧ type_of% source_generated_strict_pair_debit ∧
    type_of% source_refill_pair_balance ∧ type_of% strictRefillLower_positive ∧
    pcInteractionEnergy recoveryStateFirst = pcInteractionEnergy recoveryReceivedState :=
  ⟨source_generated_strict_refill, source_generated_strict_supplier_debit, source_generated_strict_pair_debit,
    source_refill_pair_balance, strictRefillLower_positive, recoveryStep_interactionEnergy recoveryReceivedState⟩

end
end LAlanine40K2025.Thermal.Recovery.StrictRefill
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
