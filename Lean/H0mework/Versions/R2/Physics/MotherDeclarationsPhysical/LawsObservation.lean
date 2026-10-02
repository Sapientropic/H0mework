import H0mework.Versions.R2.Physics.MotherDeclarationsPhysical.CurrentFormation

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws

open StageNineCanonicalCauchyState CurrentMaterial MotherStreamLaws

noncomputable section

abbrev Current := StageNineCauchyState × ℝ
abbrev Input := Current × Stream
abbrev Observation := (Channel × StageNineSpatialPoint) ⊕ ℕ

def observeInput : Observation → Input → ℝ
  | .inl (channel, point), input => observe input.1.1 input.1.2 channel point
  | .inr index, input => input.2 index

theorem current_observation_injective :
    Function.Injective (fun current : Current => observe current.1 current.2) := by
  intro first last same
  dsimp only at same
  obtain ⟨law, reads, recovered⟩ := MotherRawCurrent.every_current first
  apply recovered.symm.trans
  apply Prod.ext
  · exact MotherRawCurrent.initial_recovered law last.1 last.2 (reads.trans same)
  · change MotherRawCurrent.readReal law .clock 0 = last.2
    rw [reads, same]
    rfl

theorem observations_injective : Function.Injective (fun input => fun observation => observeInput observation input) := by
  intro first last same
  apply Prod.ext
  · apply current_observation_injective
    funext channel point
    exact congrFun same (.inl (channel, point))
  · funext index
    exact congrFun same (.inr index)

theorem separates {first last : Input} (different : first ≠ last) :
    ∃ observation : Observation, observeInput observation first ≠ observeInput observation last := by
  classical
  by_contra noObservation
  push Not at noObservation
  exact different (observations_injective (funext noObservation))

theorem finite_coordinates (K : Set Input) (finite : K.Finite) :
    ∃ n : ℕ, ∃ observations : Fin n → Observation,
      K.InjOn (fun input => fun index => observeInput (observations index) input) := by
  classical
  let : Fintype K := finite.fintype
  have chooseObservation (pair : K × K) : ∃ observation : Observation,
      pair.1.val ≠ pair.2.val → observeInput observation pair.1.val ≠ observeInput observation pair.2.val := by
    by_cases different : pair.1.val ≠ pair.2.val
    · obtain ⟨observation, separates⟩ := separates different
      exact ⟨observation, fun _ => separates⟩
    · exact ⟨.inr 0, fun contradiction => False.elim (different contradiction)⟩
  choose observation separatesPair using chooseObservation
  let positions := Fintype.equivFin (K × K)
  refine ⟨Fintype.card (K × K), fun index => observation (positions.symm index), ?_⟩
  intro first firstIn last lastIn same
  by_contra different
  let pair : K × K := (⟨first, firstIn⟩, ⟨last, lastIn⟩)
  have agrees := congrFun same (positions pair)
  dsimp only at agrees
  rw [positions.symm_apply_apply] at agrees
  exact separatesPair pair different agrees

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalLaws
