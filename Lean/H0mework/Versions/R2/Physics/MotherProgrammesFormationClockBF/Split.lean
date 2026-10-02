import H0mework.Versions.R2.Physics.MotherProgrammesFormationClockBF.Action
import H0mework.Versions.R2.Physics.MotherProgrammesFormationClockBF.Coordinates

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFSplit

open StageNineHolonomicField StageNineP286ActionCauchySplit
open ClockBF ClockBFCoordinates

noncomputable section

theorem configuration_eq_displace (u b : ℝ) :
    clockBFConfiguration u b = displace (u, b) Runtime.configuration := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  · funext point row column
    by_cases time : column = 0
    · subst column
      simp [clockBFConfiguration, displace, clockDirection, canonicalLorentzianTimeDirection]
      ring
    · simp [clockBFConfiguration, displace, clockDirection, canonicalLorentzianTimeDirection, time]
  · funext point
    simp [clockBFConfiguration, displace, add_smul]

/-- The hidden shift is computed by the original action, not supplied as an
inverse or source-identification certificate. -/
def hiddenShift : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun pair := (pair.1, pair.2 - generatedB pair.1)
  invFun pair := (pair.1, pair.2 + generatedB pair.1)
  left_inv pair := by simp
  right_inv pair := by simp

/-- Complete fields retain their generated remainder through the nonlinear
coordinate change; no field outside these two directions is discarded. -/
def wholeSplit : StageNineHolonomicConfiguration ≃ ((ℝ × ℝ) × Remainder) :=
  wholeEquiv.trans (hiddenShift.prodCongr (Equiv.refl Remainder))

theorem source_coordinates (u b : ℝ) :
    wholeSplit (clockBFConfiguration u b) =
      ((u, b - generatedB u), ⟨Runtime.configuration, read_original⟩) := by
  rw [configuration_eq_displace]
  apply Prod.ext
  · change hiddenShift (read (displace (u, b) Runtime.configuration)) = (u, b - generatedB u)
    rw [source_displacement_read]
    rfl
  · apply Subtype.ext
    exact source_displacement_remainder (u, b)

theorem source_recovered (u b : ℝ) :
    wholeSplit.symm ((u, b - generatedB u), ⟨Runtime.configuration, read_original⟩) =
      clockBFConfiguration u b := by
  rw [← source_coordinates]
  exact wholeSplit.symm_apply_apply _

/-- The exact full local density is consumed on the two generated coordinates.
The same representation retains the complete field needed by later writers. -/
theorem action_in_generated_coordinates (u b : ℝ) (positive : 0 < 1 + u) :
    let encoded := wholeSplit (clockBFConfiguration u b)
    clockBFAction u b = effectiveClockAction encoded.1.1 +
      responseScale * (1 + encoded.1.1) * encoded.1.2^2 := by
  simp only [source_coordinates]
  exact action_elimination u b positive

theorem generated_hidden_zero (u : ℝ) :
    wholeSplit (clockBFConfiguration u (generatedB u)) =
      ((u, 0), ⟨Runtime.configuration, read_original⟩) := by
  rw [source_coordinates]
  simp

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFSplit
