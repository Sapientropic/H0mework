import H0mework.Versions.R2.Physics.MotherProgrammesFormationClockBF.Material

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFCoordinates

open StageNineHolonomicField ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open ClockBFMaterial

noncomputable section

def clockDirection (point : BasePoint) : LorentzianCoframe :=
  fun row column => if column = 0 then Runtime.configuration.coframe point row column else 0

def read (current : StageNineHolonomicConfiguration) : ℝ × ℝ :=
  (current.coframe 0 0 0 / origin.coframe 0 0 - 1,
    auxiliaryRead (current.gaugeAuxiliary 0) / auxiliaryRead origin.gaugeAuxiliary - 1)

private theorem clock_nonzero : origin.coframe 0 0 ≠ 0 := by
  rw [origin_coframe]
  exact ne_of_gt lapse_pos

private theorem auxiliary_nonzero : auxiliaryRead origin.gaugeAuxiliary ≠ 0 :=
  ne_of_gt origin_auxiliary_read_pos

/-- Displacement along two directions computed from the original full field.
Every other field, including the independent dual, is retained. -/
def displace (delta : ℝ × ℝ) (current : StageNineHolonomicConfiguration) :
    StageNineHolonomicConfiguration :=
  { current with
    coframe := fun point => current.coframe point + delta.1 • clockDirection point
    gaugeAuxiliary := fun point =>
      current.gaugeAuxiliary point + delta.2 • Runtime.configuration.gaugeAuxiliary point }

theorem displace_zero (current : StageNineHolonomicConfiguration) : displace 0 current = current := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  · funext point
    simp [displace]
  · funext point
    simp [displace]

theorem displace_add (first second : ℝ × ℝ) (current : StageNineHolonomicConfiguration) :
    displace first (displace second current) = displace (first + second) current := by
  apply StageNineHolonomicConfiguration.ext <;> try rfl
  · funext point
    simp only [displace, Prod.fst_add]
    module
  · funext point
    simp only [displace, Prod.snd_add]
    module

theorem read_displace (delta : ℝ × ℝ) (current : StageNineHolonomicConfiguration) :
    read (displace delta current) = read current + delta := by
  apply Prod.ext
  · change (current.coframe 0 0 0 + delta.1 * origin.coframe 0 0) /
        origin.coframe 0 0 - 1 = current.coframe 0 0 0 / origin.coframe 0 0 - 1 + delta.1
    field_simp [clock_nonzero]
    ring
  · change auxiliaryRead (current.gaugeAuxiliary 0 + delta.2 • origin.gaugeAuxiliary) /
        auxiliaryRead origin.gaugeAuxiliary - 1 =
      auxiliaryRead (current.gaugeAuxiliary 0) / auxiliaryRead origin.gaugeAuxiliary - 1 + delta.2
    rw [map_add, map_smul]
    change (auxiliaryRead (current.gaugeAuxiliary 0) +
        delta.2 * auxiliaryRead origin.gaugeAuxiliary) / auxiliaryRead origin.gaugeAuxiliary - 1 = _
    field_simp [auxiliary_nonzero]
    ring

theorem read_original : read Runtime.configuration = 0 := by
  change (origin.coframe 0 0 / origin.coframe 0 0 - 1,
    auxiliaryRead origin.gaugeAuxiliary / auxiliaryRead origin.gaugeAuxiliary - 1) = (0, 0)
  simp [clock_nonzero, auxiliary_nonzero]

def remainder (current : StageNineHolonomicConfiguration) : StageNineHolonomicConfiguration :=
  displace (-read current) current

theorem remainder_zero (current : StageNineHolonomicConfiguration) : read (remainder current) = 0 := by
  rw [remainder, read_displace, add_neg_cancel]

def Remainder := { current : StageNineHolonomicConfiguration // read current = 0 }

/-- The remainder is calculated from the represented field itself, never
supplied as external recovery data. -/
def wholeEquiv : StageNineHolonomicConfiguration ≃ ((ℝ × ℝ) × Remainder) where
  toFun current := (read current, ⟨remainder current, remainder_zero current⟩)
  invFun coordinates := displace coordinates.1 coordinates.2.val
  left_inv current := by
    change displace (read current) (displace (-read current) current) = current
    rw [displace_add, add_neg_cancel, displace_zero]
  right_inv coordinates := by
    rcases coordinates with ⟨delta, rest⟩
    apply Prod.ext
    · change read (displace delta rest.val) = delta
      rw [read_displace, rest.property, zero_add]
    · apply Subtype.ext
      change displace (-read (displace delta rest.val)) (displace delta rest.val) = rest.val
      rw [read_displace, rest.property, zero_add, displace_add, neg_add_cancel, displace_zero]

theorem source_displacement_read (delta : ℝ × ℝ) :
    read (displace delta Runtime.configuration) = delta := by
  rw [read_displace, read_original, zero_add]

theorem source_displacement_remainder (delta : ℝ × ℝ) :
    remainder (displace delta Runtime.configuration) = Runtime.configuration := by
  rw [remainder, source_displacement_read, displace_add, neg_add_cancel, displace_zero]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.ClockBFCoordinates
