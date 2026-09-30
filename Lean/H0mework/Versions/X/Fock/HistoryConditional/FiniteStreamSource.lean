import H0mework.Versions.X.Fock.HistoryConditional.StreamMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalFiniteStream

open SourceGeneratedRuntimeHistoryProbability SourceGeneratedAcquisitionContinuation
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation values born bornObservation count)
open scoped Classical
noncomputable section

abbrev Table := Field parity →₀ (ℝ × SourceJointClockGraph.Carrier)

def read (table : Table) : SourceConditionalStream.Data :=
  (fun value => (table value).1, fun value => (table value).2)

def seed (depth : Nat) : Table :=
  Finsupp.single (observation 0 depth 0) (1, values 0 0)

def advance (bound depth : Nat) (previous : Table) : Table :=
  let value := bornObservation bound depth
  let old := previous value
  previous.update value (old.1 + 1, old.2 + ((old.1 + 1 : ℝ) : ℂ)⁻¹ • (born bound - old.2))

def generate (depth : Nat) : Nat → Table :=
  Nat.rec (seed depth) (fun bound previous => advance bound depth previous)

theorem generated_next (bound depth : Nat) : generate depth (bound + 1) = advance bound depth (generate depth bound) := rfl

theorem seed_read (depth : Nat) : read (seed depth) = SourceConditionalStream.seed depth := by
  apply Prod.ext
  · funext value
    by_cases same : observation 0 depth 0 = value
    · simp only [read, seed, Finsupp.single_apply, SourceConditionalStream.seed, if_pos same]
    · simp only [read, seed, Finsupp.single_apply, SourceConditionalStream.seed, if_neg same]
      rfl
  · funext value
    by_cases same : observation 0 depth 0 = value
    · simp only [read, seed, Finsupp.single_apply, SourceConditionalStream.seed, if_pos same]
    · simp only [read, seed, Finsupp.single_apply, SourceConditionalStream.seed, if_neg same]
      rfl

theorem advance_read (bound depth : Nat) (previous : Table) :
    read (advance bound depth previous) = SourceConditionalStream.advance bound depth (read previous) := by
  apply Prod.ext
  · funext value
    by_cases same : value = bornObservation bound depth
    · subst value
      simp only [read, advance, Finsupp.update_apply, SourceConditionalStream.advance, ite_true]
    · simp only [read, advance, Finsupp.update_apply, SourceConditionalStream.advance, if_neg same, if_neg (Ne.symm same), add_zero]
  · funext value
    by_cases same : value = bornObservation bound depth
    · subst value
      simp only [read, advance, Finsupp.update_apply, SourceConditionalStream.advance, ite_true]
    · simp only [read, advance, Finsupp.update_apply, SourceConditionalStream.advance, if_neg same, if_neg (Ne.symm same)]

theorem generated_read (bound depth : Nat) : read (generate depth bound) = SourceConditionalStream.generate depth bound := by
  induction bound with
  | zero => exact seed_read depth
  | succ bound previous => rw [generated_next, advance_read, previous, SourceConditionalStream.generated_next]

theorem generated_entry (bound depth : Nat) (value : Field parity) :
    generate depth bound value = (count bound depth value, SourceConditionalInnovation.decoder bound depth value) := by
  have same := generated_read bound depth
  rw [SourceConditionalStream.generated_source] at same
  exact Prod.ext (congrFun (congrArg Prod.fst same) value) (congrFun (congrArg Prod.snd same) value)

end
end SourceConditionalFiniteStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
