import H0mework.Versions.X.Fock.HistoryConditional.FiniteStreamMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalWordStream

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

abbrev Table := Field parity →₀ (ℝ × (Nat →₀ ℂ))

def sourceWord (bound : Nat) (index : Fin (bound + 1)) : Nat →₀ ℂ :=
  SourceClockComplex.ofNative (SourceOperationNative.point ((history runtimeSeed bound).stageAt index).next)

theorem source_read (bound : Nat) (index : Fin (bound + 1)) :
    SourceJointClockGraph.read (sourceWord bound index) = SourceConditionalInventory.values bound index := rfl

def bornWord (bound : Nat) : Nat →₀ ℂ := sourceWord (bound + 1) (Fin.last (bound + 1))

theorem born_read (bound : Nat) : SourceJointClockGraph.read (bornWord bound) = SourceConditionalInventory.born bound := rfl

def read (table : Table) : SourceConditionalFiniteStream.Table :=
  table.mapRange (fun item => (item.1, SourceJointClockGraph.read item.2)) (by simp only [map_zero, Prod.fst_zero, Prod.snd_zero]; rfl)

def seed (depth : Nat) : Table := Finsupp.single (observation 0 depth 0) (1, sourceWord 0 0)

def advance (bound depth : Nat) (previous : Table) : Table :=
  let value := bornObservation bound depth
  let old := previous value
  previous.update value (old.1 + 1, old.2 + ((old.1 + 1 : ℝ) : ℂ)⁻¹ • (bornWord bound - old.2))

def generate (depth : Nat) : Nat → Table :=
  Nat.rec (seed depth) (fun bound previous => advance bound depth previous)

theorem generated_next (bound depth : Nat) : generate depth (bound + 1) = advance bound depth (generate depth bound) := rfl

theorem seed_read (depth : Nat) : read (seed depth) = SourceConditionalFiniteStream.seed depth := by
  rw [seed, read, Finsupp.mapRange_single]
  simp only [source_read, SourceConditionalFiniteStream.seed]

theorem advance_read (bound depth : Nat) (previous : Table) :
    read (advance bound depth previous) = SourceConditionalFiniteStream.advance bound depth (read previous) := by
  apply Finsupp.ext
  intro value
  by_cases same : value = bornObservation bound depth
  · subst value
    simp only [read, advance, Finsupp.mapRange_apply, Finsupp.update_apply, SourceConditionalFiniteStream.advance,
      ite_true, map_add, map_smul, map_sub, born_read]
  · simp only [read, advance, Finsupp.mapRange_apply, Finsupp.update_apply, SourceConditionalFiniteStream.advance, if_neg same]

theorem generated_read (bound depth : Nat) : read (generate depth bound) = SourceConditionalFiniteStream.generate depth bound := by
  induction bound with
  | zero => exact seed_read depth
  | succ bound previous => rw [generated_next, advance_read, previous, SourceConditionalFiniteStream.generated_next]

end
end SourceConditionalWordStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
