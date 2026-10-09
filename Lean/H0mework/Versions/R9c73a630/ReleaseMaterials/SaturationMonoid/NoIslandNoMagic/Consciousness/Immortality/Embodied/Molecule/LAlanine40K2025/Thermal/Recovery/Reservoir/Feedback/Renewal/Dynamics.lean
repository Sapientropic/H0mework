import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Producer.SourceGeneratedFeedbackResources

/-! # Retained donor payment through a further feedback pulse and actual load

The conditional donor block pays its own signed transfer. The subsequent load consumes the full
generated joint and transports the donor matrix while preserving its remaining energy.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal

open Resource Propagation.Producer
noncomputable section

/-- The actual PC transfer on the pointer-selected supply branch. -/
def supplyTransfer (current : Live.State) : ℝ :=
  pcEnergyOf (suppliedBlock (respondNext current)) - pcEnergyOf (suppliedBlock current)

theorem response_remaining_debit (current : Live.State) :
    donorRemainingOf (suppliedBlock (respondNext current)) + supplyTransfer current =
      donorRemainingOf (suppliedBlock current) := by
  have mass : (suppliedBlock (respondNext current)).trace.re =
      (suppliedBlock current).trace.re := by
    rw [suppliedBlock_mass, suppliedBlock_mass, respondNext_one]
  have balance := supply_branch_paid current
  dsimp only [donorRemainingOf, supplyTransfer]
  rw [mass]
  linarith

theorem response_paid_from_remaining (current : Live.State) :
    supplyTransfer current ≤ donorRemainingOf (suppliedBlock current) := by
  linarith [response_remaining_debit current, (remaining_range (respondNext current)).1]

theorem load_supplied_block (current : Live.State) :
    suppliedBlock (Live.loadNext current) =
      Quantum.conjugation (Current.loadPulse (nativeClockStep : ℝ)) (suppliedBlock current) := by
  unfold suppliedBlock
  rw [Live.loadNext_joint]
  change (Quantum.conjugation (blockUnitary (Current.loadPulse (nativeClockStep : ℝ))
    (freePhase (nativeClockStep : ℝ) • Current.loadPulse (nativeClockStep : ℝ)))
      current.joint).toBlocks₂₂ = _
  rw [controlled_block_right]
  exact unitPhase_conjugation _ _ _

theorem load_remaining (current : Live.State) :
    donorRemainingOf (suppliedBlock (Live.loadNext current)) =
      donorRemainingOf (suppliedBlock current) := by
  rw [load_supplied_block]
  simp only [donorRemainingOf, load_donor_energy, Quantum.conjugation_trace]

theorem load_donor_material (current : Live.State) :
    donorMatrixOf (bodyRead (Live.loadNext current).joint) =
      Quantum.conjugation (Native.freePCUnitary (nativeClockStep : ℝ))
        (donorMatrixOf (bodyRead current.joint)) := by
  rw [Live.loadNext_body, load_donor]

theorem load_donor_total (current : Live.State) :
    donorEnergyOf (bodyRead (Live.loadNext current).joint) =
      donorEnergyOf (bodyRead current.joint) := by
  rw [Live.loadNext_body, load_donor_energy]

theorem load_execution_account (current : Live.State) :
    (pcEnergyOf (bodyRead (Live.loadNext current).joint) - pcEnergyOf (bodyRead current.joint)) +
      (environmentEnergyOf (bodyRead (Live.loadNext current).joint) -
        environmentEnergyOf (bodyRead current.joint)) +
      (boundaryEnergyOf (bodyRead (Live.loadNext current).joint) -
        boundaryEnergyOf (bodyRead current.joint)) = 0 := by
  rw [Live.loadNext_body]
  exact load_pce_energy_balance _ _

/-- Execution spends the generated PC state; the donor remainder is the post-supply remainder. -/
theorem execution_remaining_debit (current : Live.State) :
    donorRemainingOf (suppliedBlock (Live.loadNext (respondNext current))) +
      supplyTransfer current = donorRemainingOf (suppliedBlock current) := by
  rw [load_remaining]
  exact response_remaining_debit current

theorem response_joint_injective (left right : Live.State)
    (same : (respondNext left).joint = (respondNext right).joint) :
    left.joint = right.joint := by
  rw [respondNext_joint, respondNext_joint] at same
  exact (Unitary.conjStarAlgAut ℂ PointerJoint (feedbackPulse (nativeClockStep : ℝ))).injective same

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
