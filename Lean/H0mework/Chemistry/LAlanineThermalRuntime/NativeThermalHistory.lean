import H0mework.Chemistry.LAlanineThermalRuntime.GeneratedThermalCollision

/-!
# One registered collision, carried by the existing source clock

The gate recognizes the positive integer clock orbit after the collision.
A time threshold would give off-lattice currents a collision they never visited.
The root clock records the write; it is not a measured interaction duration.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Runtime

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Dynamics
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Propagation.Producer
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Preparation
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Source
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Collision

noncomputable section

def collisionClockIndex (time : ℚ) : ℚ :=
  (time - collisionCurrentTime) / nativeClockStep

/-- Decidable membership, not a stored sequence of future states. -/
def HoldsCollision (time : ℚ) : Prop :=
  (collisionClockIndex time).den = 1 ∧ 0 < collisionClockIndex time

instance (time : ℚ) : Decidable (HoldsCollision time) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem collisionClockIndex_next (time : ℚ) :
    collisionClockIndex (time + nativeClockStep) = collisionClockIndex time + 1 := by
  unfold collisionClockIndex
  field_simp [ne_of_gt nativeClockStep_positive]
  ring

theorem collisionClockIndex_eq_zero (time : ℚ) :
    collisionClockIndex time = 0 ↔ time = collisionCurrentTime := by
  simp [collisionClockIndex, ne_of_gt nativeClockStep_positive, sub_eq_zero]

theorem holdsCollision_next (time : ℚ) :
    HoldsCollision (time + nativeClockStep) ↔
      time = collisionCurrentTime ∨ HoldsCollision time := by
  unfold HoldsCollision
  rw [collisionClockIndex_next]
  simp only [Rat.add_ofNat_den]
  constructor
  · rintro ⟨hd, hp⟩
    have he := Rat.coe_int_num_of_den_eq_one hd
    have hn : (-1 : ℤ) < (collisionClockIndex time).num := by
      have hq : (-1 : ℚ) < ((collisionClockIndex time).num : ℚ) := by linarith
      exact_mod_cast hq
    have hn0 : 0 ≤ (collisionClockIndex time).num := by omega
    rcases eq_or_lt_of_le hn0 with hz | hpos
    · left
      apply (collisionClockIndex_eq_zero time).mp
      simpa [← hz] using he.symm
    · right
      refine ⟨hd, ?_⟩
      rw [← he]
      exact_mod_cast hpos
  · rintro (rfl | ⟨hd, hp⟩)
    · norm_num [collisionClockIndex]
    · exact ⟨hd, by linarith⟩

theorem collision_not_already_held : ¬ HoldsCollision collisionCurrentTime := by
  simp [HoldsCollision, collisionClockIndex]

theorem collision_next_held : HoldsCollision (collisionCurrentTime + nativeClockStep) :=
  (holdsCollision_next _).mpr (Or.inl rfl)

theorem offLattice_not_held :
    ¬ HoldsCollision (collisionCurrentTime + nativeClockStep / 2) := by
  have hi : collisionClockIndex (collisionCurrentTime + nativeClockStep / 2) = 1 / 2 := by
    unfold collisionClockIndex
    field_simp [ne_of_gt nativeClockStep_positive]
    ring
  norm_num [HoldsCollision, hi]

theorem offLattice_next_not_held :
    ¬ HoldsCollision ((collisionCurrentTime + nativeClockStep / 2) + nativeClockStep) := by
  rw [holdsCollision_next]
  refine not_or.mpr ⟨?_, offLattice_not_held⟩
  have hp := nativeClockStep_positive
  intro he
  linarith

/-- All material states and their local coupling source travel together. -/
structure ThermalCollisionMaterial : Type where
  occurrenceTime : ℚ
  electronicArtifact : String
  receivedDensity : ElectronicOperator
  preparedSystem : Matrix Basis Basis ℂ
  preparedBath : Matrix Basis Basis ℂ
  inverseTemperature : ℝ
  exchangeCosine : ℝ
  exchangeSine : ℝ
  joint : JointMatrix Basis
  system : Matrix Basis Basis ℂ
  bath : Matrix Basis Basis ℂ

/-- Positive preparation is an explicit operation on the received row density. -/
def collideCurrent (current : ElectronicOperator) : ThermalCollisionMaterial :=
  let prepared := energyCoordinates (normalizedGram (matrixOperatorEquiv.symm current))
  let joint := jointNext prepared bathCurrent exchangeCosine exchangeSine
  { occurrenceTime := collisionCurrentTime
    electronicArtifact := sourceArtifactSha256
    receivedDensity := current
    preparedSystem := prepared
    preparedBath := bathCurrent
    inverseTemperature := inverseTemperature
    exchangeCosine := exchangeCosine
    exchangeSine := exchangeSine
    joint := joint
    system := systemReduce joint
    bath := bathReduce joint }

def sourceCollisionMaterial : ThermalCollisionMaterial :=
  collideCurrent (densityEvolution electronicSource (collisionCurrentTime : ℝ))

theorem sourceCollisionMaterial_preparation :
    sourceCollisionMaterial.preparedSystem = systemCurrent := rfl

theorem sourceCollisionMaterial_joint :
    sourceCollisionMaterial.joint = Producer.generatedJoint := rfl

theorem sourceCollisionMaterial_system :
    sourceCollisionMaterial.system = Producer.generatedSystem := rfl

theorem sourceCollisionMaterial_bath :
    sourceCollisionMaterial.bath = Producer.generatedBath := rfl

def collisionHistoryAt (time : ℚ) : Option ThermalCollisionMaterial :=
  if HoldsCollision time then some sourceCollisionMaterial else none

/-- Only the registered occurrence prepares an ancilla; every other step copies history. -/
def collisionHistoryUpdate (time : ℚ) (current : ElectronicOperator)
    (history : Option ThermalCollisionMaterial) : Option ThermalCollisionMaterial :=
  if time = collisionCurrentTime then some (collideCurrent current) else history

theorem collisionHistoryAt_current : collisionHistoryAt collisionCurrentTime = none := by
  simp [collisionHistoryAt, collision_not_already_held]

theorem collisionHistoryUpdate_carries (time : ℚ) (current : ElectronicOperator)
    (history : Option ThermalCollisionMaterial) (inactive : time ≠ collisionCurrentTime) :
    collisionHistoryUpdate time current history = history := by
  simp [collisionHistoryUpdate, inactive]

theorem collisionHistoryAt_receives_update (time : ℚ) (current : ElectronicOperator)
    (currentExact : current = densityEvolution electronicSource (time : ℝ))
    (history : Option ThermalCollisionMaterial) (historyExact : history = collisionHistoryAt time) :
    collisionHistoryAt (time + nativeClockStep) = collisionHistoryUpdate time current history := by
  subst history
  by_cases active : time = collisionCurrentTime
  · subst time
    simp [collisionHistoryAt, collision_next_held, collisionHistoryUpdate,
      currentExact, sourceCollisionMaterial]
  · have hgate : HoldsCollision (time + nativeClockStep) ↔ HoldsCollision time := by
      simp [holdsCollision_next, active]
    simp [collisionHistoryAt, collisionHistoryUpdate, active, hgate]

theorem collisionHistory_no_reset_afterward (current : ElectronicOperator)
    (history : Option ThermalCollisionMaterial) :
    collisionHistoryUpdate (collisionCurrentTime + nativeClockStep) current history = history := by
  apply collisionHistoryUpdate_carries
  have hp := nativeClockStep_positive
  intro he
  linarith

end

end LAlanine40K2025.Thermal.Runtime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
