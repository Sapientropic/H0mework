import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedBondRenewal.Dyadic

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondRenewal
noncomputable section
open CPS1Deformation CPS1PositivePulse CPS1AddressedTransfer CPS1AddressedBondResponse
variable {frame : CPS1Recycling.Frame}

def trajectory (initial : ActiveMaterial frame) : Nat → ActiveMaterial frame :=
  Nat.rec initial (fun _ previous => advance previous)

theorem trajectory_zero (initial : ActiveMaterial frame) : trajectory initial 0 = initial := rfl

theorem trajectory_succ (initial : ActiveMaterial frame) (depth : Nat) :
    trajectory initial (depth+1) = advance (trajectory initial depth) := rfl

theorem trajectory_actual (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).material.pulse? (renewingTime (trajectory initial depth)) =
      .ok ((trajectory initial (depth+1)).material,(renewingResponse (trajectory initial depth)).2) :=
  advance_actual (trajectory initial depth)

theorem trajectory_signed (initial : ActiveMaterial frame) (depth : Nat) :
    0 < responseFlux (trajectory initial depth).material (trajectory initial depth).site.phosphate.nuclear 0 *
      transferredPopulation (trajectory initial depth).material (trajectory initial depth).site.phosphate.nuclear
        (renewingTime (trajectory initial depth)) := advance_signed_electronic (trajectory initial depth)

theorem trajectory_active (initial : ActiveMaterial frame) (depth : Nat) :
    responseFlux (trajectory initial depth).material (trajectory initial depth).site.phosphate.nuclear 0 ≠ 0 :=
  (trajectory initial depth).active

theorem trajectory_source_site (initial : ActiveMaterial frame) (depth : Nat) :
    selectBridge? (trajectory initial depth).material.reference = some (trajectory initial depth).site :=
  (trajectory initial depth).sourceSite

theorem trajectory_paid (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).material.energy+(trajectory initial depth).material.reserve =
      initial.material.energy+initial.material.reserve := by
  induction depth with
  | zero => rfl
  | succ depth previous =>
    exact (advance_paid (trajectory initial depth)).2.2.trans previous

theorem trajectory_same_reference (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).material.reference = initial.material.reference := by
  induction depth with
  | zero => rfl
  | succ depth previous => exact (advance_source (trajectory initial depth)).trans previous

theorem trajectory_same_component (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).site.phosphate.component = initial.site.phosphate.component := by
  induction depth with
  | zero => rfl
  | succ depth previous => exact previous

theorem trajectory_same_atom_slot (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).site.phosphate.atomSlot = initial.site.phosphate.atomSlot := by
  induction depth with
  | zero => rfl
  | succ depth previous => exact previous

theorem trajectory_signed_distance (initial : ActiveMaterial frame) (depth : Nat) :
    0 < (distancePolynomial (trajectory initial depth).material (trajectory initial depth).site).coefficient
      (trajectory initial depth).degree *
      (squaredDistance ((trajectory initial depth).material.movedPositions (renewingTime (trajectory initial depth)))
        (trajectory initial depth).site-
        squaredDistance (trajectory initial depth).material.positions (trajectory initial depth).site) :=
  advance_signed_distance (trajectory initial depth)

theorem trajectory_nonzero_velocity (initial : ActiveMaterial frame) (depth : Nat) :
    relativeVelocity (trajectory initial (depth+1)).material (trajectory initial (depth+1)).site ≠ 0 :=
  advance_nonzero_velocity (trajectory initial depth)

theorem trajectory_driven (initial : ActiveMaterial frame) (depth : Nat) :
    (distancePolynomial (trajectory initial depth).material (trajectory initial depth).site).leading? =
      some (trajectory initial depth).degree := (trajectory initial depth).drive

theorem trajectory_same_oxygen_slot (initial : ActiveMaterial frame) (depth : Nat) :
    (trajectory initial depth).site.oxygenAtomSlot = initial.site.oxygenAtomSlot := by
  induction depth with
  | zero => rfl
  | succ depth previous => exact previous

def elapsed (initial : ActiveMaterial frame) : Nat → ℝ :=
  Nat.rec 0 (fun depth previous => previous+renewingTime (trajectory initial depth))

theorem elapsed_strict (initial : ActiveMaterial frame) (depth : Nat) :
    elapsed initial depth < elapsed initial (depth+1) := by
  exact lt_add_of_pos_right _ (dyadic_time_positive _)

end
end CPS1AddressedBondRenewal
