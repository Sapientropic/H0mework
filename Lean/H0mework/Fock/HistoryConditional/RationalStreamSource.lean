import H0mework.Fock.HistoryConditional.WordStreamMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceConditionalRationalStream

open SourceGeneratedRuntimeHistoryProbability
open SourceGeneratedScalarCofinalTopology.NativeProbability (Field)
open SourceObservationInvariantControls (parity)
open SourceConditionalInventory (observation bornObservation)
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
open scoped Classical
noncomputable section

abbrev Table := Field parity →₀ (Nat × (Nat →₀ ℚ))

def embedWord : (Nat →₀ ℚ) →ₗ[ℚ] (Nat →₀ ℂ) :=
  Finsupp.mapRange.linearMap (Algebra.linearMap ℚ ℂ)

def sourceWord (bound : Nat) (index : Fin (bound + 1)) : Nat →₀ ℚ :=
  Finsupp.mapRange (fun value : ℤ => (value : ℚ)) (by simp)
    (SourceOperationNative.point ((history runtimeSeed bound).stageAt index).next)

theorem source_embed (bound : Nat) (index : Fin (bound + 1)) :
    embedWord (sourceWord bound index) = SourceConditionalWordStream.sourceWord bound index := by
  change embedWord (Finsupp.mapRange (fun value : ℤ => (value : ℚ)) _
      (Finsupp.single (runtimeAt (index.val + 1)).state 1)) =
    SourceClockComplex.ofNative (Finsupp.single (runtimeAt (index.val + 1)).state 1)
  rw [Finsupp.mapRange_single, embedWord, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, SourceClockComplex.ofNative_single]
  norm_num

def bornWord (bound : Nat) : Nat →₀ ℚ := sourceWord (bound + 1) (Fin.last (bound + 1))

theorem born_embed (bound : Nat) : embedWord (bornWord bound) = SourceConditionalWordStream.bornWord bound := source_embed _ _

def embed (table : Table) : SourceConditionalWordStream.Table :=
  table.mapRange (fun item => ((item.1 : ℝ), embedWord item.2)) (by simp only [Prod.fst_zero, Prod.snd_zero, Nat.cast_zero, map_zero]; rfl)

def seed (depth : Nat) : Table := Finsupp.single (observation 0 depth 0) (1, sourceWord 0 0)

def advance (bound depth : Nat) (previous : Table) : Table :=
  let value := bornObservation bound depth
  let old := previous value
  previous.update value (old.1 + 1, old.2 + ((old.1 + 1 : Nat) : ℚ)⁻¹ • (bornWord bound - old.2))

def generate (depth : Nat) : Nat → Table :=
  Nat.rec (seed depth) (fun bound previous => advance bound depth previous)

theorem generated_next (bound depth : Nat) : generate depth (bound + 1) = advance bound depth (generate depth bound) := rfl

theorem seed_embed (depth : Nat) : embed (seed depth) = SourceConditionalWordStream.seed depth := by
  rw [seed, embed, Finsupp.mapRange_single, source_embed]
  norm_num [SourceConditionalWordStream.seed]

end
end SourceConditionalRationalStream
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
