import H0mework.Versions.X.Fock.HistoryModel.DynamicHilbertTopology

/-! Both dynamic dictionaries observe the same actual actors with their original history weights. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGeneratedActionWords.Fock.Dynamic.Hilbert

open MeasureTheory SourceWeightedRecovery
open SourceOwnedObservationHistory.Installed SourceGeneratedRuntimeHistoryProbability
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime

noncomputable section

local instance (depth : Nat) : UniformSpace (Complete.Carrier depth) := uniform depth
local instance (depth : Nat) : MeasurableSpace (Complete.Carrier depth) := measurable depth
local instance (depth : Nat) : BorelSpace (Complete.Carrier depth) := ⟨rfl⟩
local instance (depth : Nat) : T2Space (Complete.Carrier depth) := field_t2 depth

def read (depth bound : Nat) (index : Fin (bound + 1)) : Complete.Carrier depth :=
  Complete.point depth ((runtimeAt index.val).current.visit.current : Current)

abbrev law (depth bound : Nat) := observed (historyPMF bound) (read depth bound)

theorem original_law (depth bound : Nat) :
    law depth bound = SourceConditionalHistory.observed (Fock.sourceLaw bound) (Complete.point depth) := by
  have actual := congrArg (fun source : PMF Current => source.map (Complete.point depth)) (Fock.sourceLaw_actual bound)
  exact (PMF.map_comp (fun index : Fin (bound + 1) =>
    ((runtimeAt index.val).current.visit.current : Current)) (historyPMF bound) (Complete.point depth)).symm.trans actual.symm

theorem read_previous (depth bound : Nat) (index : Fin (bound + 1)) :
    previous depth (read (depth + 1) bound index) = read depth bound index :=
  previous_point depth _

theorem law_previous (depth bound : Nat) :
    (law (depth + 1) bound).map (previous depth) = law depth bound := by
  rw [law, observed, PMF.map_comp]
  exact congrArg (fun observer : Fin (bound + 1) → Complete.Carrier depth => (historyPMF bound).map observer)
    (funext (read_previous depth bound))

theorem previous_preserving (depth bound : Nat) :
    MeasurePreserving (previous depth) (law (depth + 1) bound).toMeasure (law depth bound).toMeasure :=
  ⟨previous_measurable depth, (PMF.toMeasure_map _ _ (previous_measurable depth)).trans
    (congrArg PMF.toMeasure (law_previous depth bound))⟩

def restriction (depth bound : Nat) : Space (law depth bound) →ₗᵢ[ℂ] Space (law (depth + 1) bound) :=
  Lp.compMeasurePreservingₗᵢ ℂ (previous depth) (previous_preserving depth bound)

theorem original_pullback (depth bound : Nat) :
    (pullback (historyPMF bound) (read (depth + 1) bound)).comp (restriction depth bound) =
      pullback (historyPMF bound) (read depth bound) := by
  apply LinearIsometry.ext
  intro value
  apply Lp.ext
  have restricted : restriction depth bound value =ᵐ[(law (depth + 1) bound).toMeasure]
      value ∘ previous depth :=
    Lp.coeFn_compMeasurePreserving value (previous_preserving depth bound)
  have sourceRestricted := (source_preserving (historyPMF bound) (read (depth + 1) bound)).quasiMeasurePreserving.ae_eq restricted
  have fine := Lp.coeFn_compMeasurePreserving (restriction depth bound value)
    (source_preserving (historyPMF bound) (read (depth + 1) bound))
  have coarse := Lp.coeFn_compMeasurePreserving value
    (source_preserving (historyPMF bound) (read depth bound))
  have square : previous depth ∘ read (depth + 1) bound = read depth bound := funext (read_previous depth bound)
  have evaluated : Lp.compMeasurePreserving (read (depth + 1) bound)
      (source_preserving (historyPMF bound) (read (depth + 1) bound)) (restriction depth bound value) =ᵐ[
        (historyPMF bound).toMeasure] value ∘ read depth bound := by
    simpa only [Function.comp_assoc, square] using fine.trans sourceRestricted
  exact evaluated.trans coarse.symm

end
end SourceGeneratedActionWords.Fock.Dynamic.Hilbert
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
