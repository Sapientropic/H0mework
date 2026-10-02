import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.Rational
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion

open UniformSpace

noncomputable section

abbrev Completed (count : ℕ) := Completion (RationalCarrier count)

/-- The extension is determined by the fixed rational source embedding. -/
def coordinates (count : ℕ) : Completed count → Fin count → ℝ :=
  Completion.extension (realEmbedding count)

theorem coordinates_coe (count : ℕ) (value : RationalCarrier count) :
    coordinates count (value : Completed count) = realEmbedding count value :=
  Completion.extension_coe (embedding_isometry count).uniformContinuous value

theorem coordinates_isometry (count : ℕ) : Isometry (coordinates count) :=
  (embedding_isometry count).completion_extension

theorem coordinates_surjective (count : ℕ) : Function.Surjective (coordinates count) := by
  have contained : Set.range (realEmbedding count) ⊆ Set.range (coordinates count) := by
    rintro _ ⟨value, rfl⟩
    exact ⟨(value : Completed count), coordinates_coe count value⟩
  have closed : IsClosed (Set.range (coordinates count)) :=
    (coordinates_isometry count).isClosedEmbedding.isClosed_range
  intro value
  exact (closure_minimal contained closed) (embedding_dense count value)

def realEquiv (count : ℕ) : Completed count ≃ᵢ (Fin count → ℝ) where
  toEquiv := Equiv.ofBijective (coordinates count)
    ⟨(coordinates_isometry count).injective, coordinates_surjective count⟩
  isometry_toFun := coordinates_isometry count

theorem realEquiv_coe (count : ℕ) (value : RationalCarrier count) :
    realEquiv count (value : Completed count) = realEmbedding count value :=
  coordinates_coe count value

theorem extension_unique (count : ℕ) (candidate : Completed count → Fin count → ℝ)
    (continuous : Continuous candidate)
    (agrees : ∀ value : RationalCarrier count,
      candidate (value : Completed count) = realEmbedding count value) :
    candidate = coordinates count :=
  Completion.ext continuous (coordinates_isometry count).continuous
    (fun value => (agrees value).trans (coordinates_coe count value).symm)

theorem realEquiv_unique (count : ℕ) (candidate : Completed count ≃ᵢ (Fin count → ℝ))
    (agrees : ∀ value : RationalCarrier count,
      candidate (value : Completed count) = realEmbedding count value) :
    candidate = realEquiv count := by
  apply DFunLike.ext
  exact congrFun (extension_unique count candidate candidate.continuous agrees)

theorem finite_native_read (count : ℕ) (visit : MotherFamilyOccurrence.MotherVisit) (slot : Fin count) :
    realEquiv count (fromVisit count visit : Completed count) slot =
      RationalSourceFormation.sourceTrace
        (StageEightDiscreteFormation.sourceAtVisit (sample count visit slot)) := by
  rw [realEquiv_coe]
  exact actual_trace count visit slot

theorem visits_dense (count : ℕ) :
    DenseRange (fun visit => (fromVisit count visit : Completed count)) := by
  have onto : Function.Surjective (fromVisit count) := by
    rintro ⟨values, visit, same⟩
    exact ⟨visit, Subtype.ext same⟩
  have ranges : Set.range (fun visit => (fromVisit count visit : Completed count)) =
      Set.range (fun value : RationalCarrier count => (value : Completed count)) := by
    ext value
    constructor
    · rintro ⟨visit, rfl⟩
      exact ⟨fromVisit count visit, rfl⟩
    · rintro ⟨rational, rfl⟩
      obtain ⟨visit, rfl⟩ := onto rational
      exact ⟨visit, rfl⟩
  rw [DenseRange, ranges]
  exact Completion.denseRange_coe

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCoordinateCompletion
