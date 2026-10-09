import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.MatrixFirst
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.MatrixF1Complete
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.MatrixF2Complete
import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ChecksIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeMatrix

open SourceGaussianModel SourceSignedEvaluator IntervalParameterMap TrueTubeSource

theorem all_first_fields (f : Field) (x : Point) (inside : InRectangle (box f) x) :
    FieldHolds (recordedField f) x := by
  fin_cases f
  · exact actual_initial_field x inside
  · exact F1.actual_field x inside
  · exact F2.actual_field x inside

theorem actual_first_tube (d : Direction) (x : Point)
    (inside : InRectangle (tubeBox d 0) x) :
    FieldHolds (recordedField (firstTubeField d)) x :=
  all_first_fields (firstTubeField d) x ((TrueTubeChecks.first_tube_field_eq d).symm ▸ inside)

theorem actual_initial_at (d : Direction) (x : Point)
    (inside : InRectangle (initialBox d 0) x) : FieldHolds (recordedField 0) x :=
  actual_initial_field x ((TrueTubeChecks.initial_field_eq d).symm ▸ inside)

noncomputable def rectangleCentre (f : Field) : Point := fun axis =>
  (((box f axis).1 + (box f axis).2) / 2 : ℚ)

theorem box_ordered (f : Field) (axis : Fin 3) : (box f axis).1 ≤ (box f axis).2 := by
  fin_cases f <;> fin_cases axis <;> decide +kernel

theorem centre_inside (f : Field) : InRectangle (box f) (rectangleCentre f) := by
  intro axis
  have h : ((box f axis).1 : ℝ) ≤ ((box f axis).2 : ℝ) :=
    Rat.cast_le.mpr (box_ordered f axis)
  change ((box f axis).1 : ℝ) ≤ (((box f axis).1 + (box f axis).2) / 2 : ℚ) ∧
    ((((box f axis).1 + (box f axis).2) / 2 : ℚ) : ℝ) ≤ (box f axis).2
  push_cast
  constructor <;> linarith

theorem source_gradient_third_positive (f : Field) (x : Point)
    (inside : InRectangle (box f) x) : 0 < ContinuousGradient.sourceGradient x 2 := by
  have lower : 0 < ((recordedField f).gradient 2).1 := by fin_cases f <;> decide +kernel
  exact lt_of_lt_of_le (Rat.cast_pos.mpr lower) ((all_first_fields f x inside).1 2).1

theorem sourceGeneratedInitialTubeFields :
    (∀ f x, InRectangle (box f) x → FieldHolds (recordedField f) x) ∧
    (∀ d x, InRectangle (initialBox d 0) x → FieldHolds (recordedField 0) x) ∧
    (∀ d x, InRectangle (tubeBox d 0) x → FieldHolds (recordedField (firstTubeField d)) x) ∧
    (∀ f, InRectangle (box f) (rectangleCentre f)) ∧
    (∀ f x, InRectangle (box f) x → 0 < ContinuousGradient.sourceGradient x 2) :=
  ⟨all_first_fields, actual_initial_at, actual_first_tube, centre_inside, source_gradient_third_positive⟩

end LAlanine40K2025.BasinRefinement.TrueTubeMatrix
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
