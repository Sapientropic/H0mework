import H0mework.Foundation.Ledger.CompilerFacade
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.FiniteRows

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary} (source : SourceNativeSource N V)

/-- Complete finite rows for an already fixed source and its actual local
ledger transition. This utility neither selects an action nor supplies a root. -/
structure Data where
  emitted : (current : V.Current) → source.toRootSource.actual.OccurrenceAt current
  next : V.Current → V.Current
  evolution : (current : V.Current) → LedgerWriteEvolutionAt N ⟨(emitted current).1⟩ ⟨(emitted (next current)).1⟩
  finite : (current : V.Current) → Finite (OpenResponsibilityAt N (emitted current).1)

variable {source} (data : Data source)

abbrev Seed (current : V.Current) := OpenResponsibilityAt N (data.emitted current).1 ⊕
  OpenResponsibilityAt N (data.emitted (data.next current)).1

@[instance_reducible] private def seedFintype (current : V.Current) : Fintype (Seed data current) := by
  letI : Fintype (OpenResponsibilityAt N (data.emitted current).1) := @Fintype.ofFinite _ (data.finite current)
  letI : Fintype (OpenResponsibilityAt N (data.emitted (data.next current)).1) := @Fintype.ofFinite _ (data.finite (data.next current))
  exact inferInstance

private def count (current : V.Current) := @Fintype.card _ (seedFintype data current)
private def enumerate (current : V.Current) := @Fintype.equivFin _ (seedFintype data current)

def before (current : V.Current) : Seed data current → OpenResponsibilityAt N (data.emitted current).1
  | .inl entry => entry
  | .inr entry => ((data.evolution current).origin entry).1

def after (current : V.Current) : Seed data current → OpenResponsibilityAt N (data.emitted (data.next current)).1
  | .inl entry => ((data.evolution current).destination entry).1
  | .inr entry => entry

def rowEvolution (current : V.Current) (seed : Seed data current) :
    LedgerEntryEvolutionAt N (before data current seed) (after data current seed) :=
  match seed with
  | .inl entry => ((data.evolution current).destination entry).2
  | .inr entry => ((data.evolution current).origin entry).2

inductive RawRowAt : {current : V.Current} → (occurrence : source.toRootSource.actual.OccurrenceAt current) →
    {targetSupport : N.Support} → OpenResponsibilityAt N occurrence.1 → OpenResponsibilityAt N targetSupport → Type
  | generated (current : V.Current) (seed : Seed data current) :
      RawRowAt (data.emitted current) (before data current seed) (after data current seed)

def rowSource : LedgerWriteRowSourceAt source (RawRowAt data) where
  IncidenceOccurrenceAt := RawRowAt data
  compileEvolution := by
    intro current occurrence targetSupport original target event
    cases event with
    | generated seed => exact rowEvolution data _ seed
  compileExact := fun event => event

def rows (current : V.Current) : FiniteGeneratedLedgerWriteRowsAt (rowSource data)
    (data.emitted current) ⟨(data.emitted (data.next current)).1⟩ where
  size := count data current
  sourceEntryAt := fun index => before data current ((enumerate data current).symm index)
  targetEntryAt := fun index => after data current ((enumerate data current).symm index)
  rowAt := fun index => (rowSource data).generate (.generated current ((enumerate data current).symm index))

def coverage (current : V.Current) : LedgerCompleteFiniteCoverageAt (rows data current) where
  destinationIndex := fun entry => enumerate data current (.inl entry)
  originIndex := fun entry => enumerate data current (.inr entry)
  destination_sound := by
    intro entry
    change before data current ((enumerate data current).symm (enumerate data current (.inl entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl
  origin_sound := by
    intro entry
    change after data current ((enumerate data current).symm (enumerate data current (.inr entry))) = entry
    rw [Equiv.symm_apply_apply]
    rfl

def patch (current : V.Current) : FiniteGeneratedLedgerWritePatchAt (rowSource data)
    (data.emitted current) ⟨(data.emitted (data.next current)).1⟩ :=
  .complete (rows data current) (coverage data current)

private theorem destination_selected (current : V.Current) (entry : OpenResponsibilityAt N (data.emitted current).1)
    (seed : Seed data current) (selected : seed = .inl entry) (same : before data current seed = entry) :
    (⟨after data current seed, Eq.mp (congrArg (fun original => LedgerEntryEvolutionAt N original (after data current seed)) same)
      (rowEvolution data current seed)⟩ : Σ targetEntry : OpenResponsibilityAt N (data.emitted (data.next current)).1,
        LedgerEntryEvolutionAt N entry targetEntry) = (data.evolution current).destination entry := by
  cases selected
  rfl

private theorem origin_selected (current : V.Current) (entry : OpenResponsibilityAt N (data.emitted (data.next current)).1)
    (seed : Seed data current) (selected : seed = .inr entry) (same : after data current seed = entry) :
    (⟨before data current seed, Eq.mp (congrArg (fun target => LedgerEntryEvolutionAt N (before data current seed) target) same)
      (rowEvolution data current seed)⟩ : Σ sourceEntry : OpenResponsibilityAt N (data.emitted current).1,
        LedgerEntryEvolutionAt N sourceEntry entry) = (data.evolution current).origin entry := by
  cases selected
  rfl

theorem patch_destination (current : V.Current) :
    (patch data current).toLedgerWriteEvolution.destination = (data.evolution current).destination := by
  funext entry
  exact destination_selected data current entry _ ((enumerate data current).symm_apply_apply (.inl entry))
    ((coverage data current).destination_sound entry)

theorem patch_origin (current : V.Current) :
    (patch data current).toLedgerWriteEvolution.origin = (data.evolution current).origin := by
  funext entry
  exact origin_selected data current entry _ ((enumerate data current).symm_apply_apply (.inr entry))
    ((coverage data current).origin_sound entry)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.FiniteRows
