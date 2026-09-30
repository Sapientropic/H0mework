import H0mework.Fock.FiniteObserver.Equation

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

open SourceConditionalRationalStream (embedWord)
open SourceGeneratedAcquisitionContinuation
open SourceCopyProgram (Index)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped InnerProductSpace
noncomputable section

def wordClock : (Nat →₀ ℚ) →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ fun index => (SourceClockModel.rawClock index : ℚ)

theorem word_clock_single (index : Nat) (scalar : ℚ) :
    wordClock (Finsupp.single index scalar) = scalar * (SourceClockModel.rawClock index : ℚ) :=
  Finsupp.linearCombination_single _ _ _

theorem embed_single (index : Nat) (scalar : ℚ) :
    embedWord (Finsupp.single index scalar) = Finsupp.single index (scalar : ℂ) := by
  rw [embedWord, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  rfl

theorem embed_at (word : Nat →₀ ℚ) (index : Nat) : embedWord word index = (word index : ℂ) := rfl

theorem mass_embed (word : Nat →₀ ℚ) :
    SourceSuccessorBoundary.mass ℂ (embedWord word) = (SourceSuccessorBoundary.mass ℚ word : ℂ) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero previous =>
    simp only [map_add, Rat.cast_add, embed_single, SourceSuccessorBoundary.mass_single, previous]

theorem clock_embed (word : Nat →₀ ℚ) : SourceClockComplex.clock (embedWord word) = (wordClock word : ℂ) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero previous =>
    simp only [map_add, Rat.cast_add, embed_single, SourceClockComplex.clock_single, word_clock_single,
      Rat.cast_mul, Rat.cast_intCast, previous]

def response (bound scale : Nat) (word : Nat →₀ ℚ) (actor : Fin (bound + 1)) : ℚ :=
  word ((actor.val + 1) * scale - 1) + SourceSuccessorBoundary.mass ℚ word +
    (((actor.val + 1) * scale : Nat) : ℚ) * wordClock word

def calculate (bound scale : Nat) (word : Nat →₀ ℚ) : Fin (bound + 1) → ℚ := solve bound scale (response bound scale word)

theorem response_source (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps : Nat)
    (word : Nat →₀ ℚ) (actor : Fin (inventoryBound runtime + steps + 1)) :
    (response (inventoryBound runtime + steps) (index.val + 1) word actor : ℂ) =
      ⟪SourceColumnForcing.column (inventoryBound runtime) index actor.val, SourceJointClockGraph.read (embedWord word)⟫_ℂ := by
  rw [SourceCopyCurrentCoordinates.column_pairing]
  change (response (inventoryBound runtime + steps) (index.val + 1) word actor : ℂ) =
    SourceSuccessorBoundary.readWord (embedWord word) (SourceCopyProgram.indexAfter (inventoryBound runtime) index actor.val) +
      SourceSuccessorBoundary.mass ℂ (embedWord word) +
      ((SourceCopyProgram.indexAfter (inventoryBound runtime) index actor.val + 1 : Nat) : ℂ) * SourceClockComplex.clock (embedWord word)
  rw [SourceSuccessorBoundary.readWord_coordinate, embed_at, mass_embed, clock_embed,
    SourceCopyProgram.index_exact, SourceCopyProgram.index_source, SourceCopyProgram.scale_source]
  simp only [response, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
