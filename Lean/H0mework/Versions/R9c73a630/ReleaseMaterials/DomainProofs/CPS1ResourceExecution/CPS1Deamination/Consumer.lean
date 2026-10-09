import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.AtomicExecution

set_option autoImplicit false

namespace CPS1Deamination

open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

theorem source_reaction_atom_balance (edits : Target.Edits) (atom : Atom)
    (reaction : Reaction) (member : reaction ∈ (Source.sourceProgram edits).reactions) :
    moiety (editingAtoms atom) reaction.reactants = moiety (editingAtoms atom) reaction.products := by
  obtain ⟨step, _, generated⟩ := List.mem_map.mp member
  subst reaction
  exact primitive_atom_balance step.left step.right atom

theorem source_execution_atom_balance (edits : Target.Edits) (stock : Stock) (atom : Atom) :
    moiety (editingAtoms atom) stock =
      moiety (editingAtoms atom) (execute (Source.sourceProgram edits).reactions stock).stock :=
  execution_measure_preserved _ stock _ (source_reaction_atom_balance edits atom)

structure EditingContract (edits : Target.Edits) : Prop where
  sourceFollows : Source.follows Source.originalMinusAligned
    (Source.sourceProgram edits).steps (Source.sourceProgram edits).word
  addressed : (Source.sourceProgram edits).steps.map Source.Step.address ++
    (Source.sourceProgram edits).pending = Target.positions edits
  recognition : Source.plusReadout (Source.sourceProgram edits).word = Target.genomic edits
  untouched : ∀ coordinate, coordinate ∉ Target.positions edits →
    (Source.sourceProgram edits).word[coordinate]? = Source.originalMinusAligned[coordinate]?
  atoms : ∀ stock atom, moiety (editingAtoms atom) stock =
    moiety (editingAtoms atom) (execute (Source.sourceProgram edits).reactions stock).stock
  species : ∀ stock species,
    stock.count species + (credit (execute (Source.sourceProgram edits).reactions stock).fired).count species =
      (execute (Source.sourceProgram edits).reactions stock).stock.count species +
        (debit (execute (Source.sourceProgram edits).reactions stock).fired).count species
  potential : ∀ stock μ,
    speciesValue μ stock = speciesValue μ (execute (Source.sourceProgram edits).reactions stock).stock +
      affinity μ (execute (Source.sourceProgram edits).reactions stock).fired
  cut : ∀ stock missing, (execute (Source.sourceProgram edits).reactions stock).missing = some missing →
    ∃ reaction rest, (execute (Source.sourceProgram edits).reactions stock).remaining = reaction :: rest ∧
      (execute (Source.sourceProgram edits).reactions stock).stock.count missing < reaction.reactants.count missing
  disposition : ∀ stock,
    (execute (Source.sourceProgram edits).reactions stock).fired ++
      (execute (Source.sourceProgram edits).reactions stock).remaining = (Source.sourceProgram edits).reactions

theorem sourceGeneratedEditingContract (edits : Target.Edits) : EditingContract edits := by
  rcases edits with ⟨third,eighth,ninth⟩
  exact ⟨Source.compile_follows _ _, Source.compile_address_inventory _ _,
    Source.source_readout_commutes third eighth ninth,
    Source.source_untouched_coordinate third eighth ninth,
    source_execution_atom_balance _, execution_balance _, execution_potential _,
    execution_cut _, execution_decomposes _⟩

def modelStock (water : Nat) : Stock :=
  .dna Source.originalMinusAligned :: List.replicate water Species.water

theorem original_three_reactions_paid_by_finite_water :
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 3)).missing = none ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 3)).fired =
      (Source.sourceProgram ⟨true,true,true⟩).reactions ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 3)).stock.count .water = 0 ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 3)).stock.count .ammonia = 3 ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 3)).stock.count
      (.dna (Source.sourceProgram ⟨true,true,true⟩).word) = 1 := by
  decide +kernel

theorem original_water_shortage_preserves_two_paid_reactions :
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 2)).missing = some .water ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 2)).fired.length = 2 ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 2)).remaining.length = 1 ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 2)).stock.count .ammonia = 2 ∧
    (execute (Source.sourceProgram ⟨true,true,true⟩).reactions (modelStock 2)).stock.count
      (.dna (Source.sourceProgram ⟨true,true,false⟩).word) = 1 := by
  decide +kernel

end CPS1Deamination
