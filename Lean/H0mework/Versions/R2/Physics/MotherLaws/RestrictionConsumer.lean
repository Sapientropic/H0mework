import H0mework.Versions.R2.Physics.MotherLaws.RestrictionExtension
import Mathlib.Logic.Equiv.Nat

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedRestrictions

open MotherStreamLaws Topology

noncomputable section

universe u

def pairStream (first last : Stream) : Stream :=
  fun address => Sum.elim first last (Equiv.natSumNatEquivNat.symm address)

def firstStream (value : Stream) : Stream :=
  fun index => value (Equiv.natSumNatEquivNat (Sum.inl index))

def lastStream (value : Stream) : Stream :=
  fun index => value (Equiv.natSumNatEquivNat (Sum.inr index))

theorem first_pair (first last : Stream) : firstStream (pairStream first last) = first := by
  funext index
  simp only [firstStream, pairStream, Equiv.symm_apply_apply, Sum.elim_inl]

theorem last_pair (first last : Stream) : lastStream (pairStream first last) = last := by
  funext index
  simp only [lastStream, pairStream, Equiv.symm_apply_apply, Sum.elim_inr]

theorem pairStream_continuous : Continuous (fun pair : Stream × Stream => pairStream pair.1 pair.2) := by
  apply continuous_pi
  intro address
  unfold pairStream
  cases Equiv.natSumNatEquivNat.symm address with
  | inl index => exact (continuous_apply index).comp continuous_fst
  | inr index => exact (continuous_apply index).comp continuous_snd

/-- The same generated law output retains the entire input key and actual
map value. Coincident output values cannot identify distinct input events. -/
theorem exists_keyed_law {X : Type u} [TopologicalSpace X]
    (embedding : X → Stream) (closed : IsClosedEmbedding embedding) (actual : C(X, Stream)) :
    ∃ law : Law,
      (∀ input : X,
        firstStream (eval law (embedding input)) = embedding input ∧
        lastStream (eval law (embedding input)) = actual input) ∧
      Function.Injective (fun input : X => eval law (embedding input)) := by
  let joint : C(X, Stream) :=
    ⟨fun input => pairStream (embedding input) (actual input),
      pairStream_continuous.comp (closed.continuous.prodMk actual.continuous)⟩
  obtain ⟨law, generated⟩ := exists_law_on_closed_embedding embedding closed joint
  have recovered (input : X) :
      firstStream (eval law (embedding input)) = embedding input ∧
      lastStream (eval law (embedding input)) = actual input := by
    rw [generated]
    exact ⟨first_pair _ _, last_pair _ _⟩
  refine ⟨law, recovered, ?_⟩
  intro first last same
  apply closed.injective
  exact (recovered first).1.symm.trans ((congrArg firstStream same).trans (recovered last).1)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherClosedRestrictions
