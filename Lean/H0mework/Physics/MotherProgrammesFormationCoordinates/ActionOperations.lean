import H0mework.Physics.MotherProgrammesFormationCoordinates.Completion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open UniformSpace

noncomputable section

def rationalAdd (count : ℕ) (first last : RationalCarrier count) : RationalCarrier count :=
  fromRational count (first.1 + last.1)

def rationalNeg (count : ℕ) (value : RationalCarrier count) : RationalCarrier count :=
  fromRational count (-value.1)

theorem rationalAdd_uniform (count : ℕ) : UniformContinuous₂ (rationalAdd count) := by
  exact ((uniformContinuous_subtype_val.comp uniformContinuous_fst).add
    (uniformContinuous_subtype_val.comp uniformContinuous_snd)).subtype_mk _

theorem rationalNeg_uniform (count : ℕ) : UniformContinuous (rationalNeg count) := by
  exact uniformContinuous_subtype_val.neg.subtype_mk _

/-- The operations extend the finite source-range operations themselves. -/
def completedAdd (count : ℕ) : Completed count → Completed count → Completed count :=
  Completion.map₂ (rationalAdd count)

def completedNeg (count : ℕ) : Completed count → Completed count :=
  Completion.map (rationalNeg count)

theorem completedAdd_coe (count : ℕ) (first last : RationalCarrier count) :
    completedAdd count first last = (rationalAdd count first last : Completed count) :=
  Completion.map₂_coe_coe first last _ (rationalAdd_uniform count)

theorem completedNeg_coe (count : ℕ) (value : RationalCarrier count) :
    completedNeg count value = (rationalNeg count value : Completed count) :=
  Completion.map_coe (rationalNeg_uniform count) value

theorem coordinates_add (count : ℕ) (first last : Completed count) :
    coordinates count (completedAdd count first last) =
      coordinates count first + coordinates count last := by
  refine Completion.induction_on₂ first last ?_ ?_
  · exact isClosed_eq ((coordinates_isometry count).continuous.comp
      (Completion.continuous_map₂ continuous_fst continuous_snd))
      (((coordinates_isometry count).continuous.comp continuous_fst).add
        ((coordinates_isometry count).continuous.comp continuous_snd))
  · intro first last
    rw [completedAdd_coe, coordinates_coe, coordinates_coe, coordinates_coe]
    funext slot
    exact Rat.cast_add _ _

theorem coordinates_neg (count : ℕ) (value : Completed count) :
    coordinates count (completedNeg count value) = -coordinates count value := by
  refine Completion.induction_on value ?_ ?_
  · exact isClosed_eq ((coordinates_isometry count).continuous.comp Completion.continuous_map)
      (coordinates_isometry count).continuous.neg
  · intro value
    rw [completedNeg_coe, coordinates_coe, coordinates_coe]
    funext slot
    exact Rat.cast_neg _

def completedSub (count : ℕ) (last first : Completed count) : Completed count :=
  completedAdd count last (completedNeg count first)

theorem coordinates_sub (count : ℕ) (last first : Completed count) :
    coordinates count (completedSub count last first) =
      coordinates count last - coordinates count first := by
  rw [completedSub, coordinates_add, coordinates_neg, sub_eq_add_neg]

theorem completed_event_recovered (count : ℕ) (first last : Completed count) :
    completedAdd count first (completedSub count last first) = last ∧
      completedSub count (completedAdd count first last) first = last := by
  constructor <;> apply (coordinates_isometry count).injective
  · rw [coordinates_add, coordinates_sub]
    abel
  · rw [coordinates_sub, coordinates_add]
    abel

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
