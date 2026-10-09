import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EndogenousTranslation.Program
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.Accounting

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1InitiationTermination.UnifiedBoundary
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
open CPS1Deamination.CodingReadout

/-- The first transfer retains initiator identity; subsequent cycles reuse the paid native producer. -/
def elongation (tail : List AA) : List Reaction :=
  match tail with
  | [] => []
  | aa :: rest => [.deliverInitiator aa,.transferInitiator aa,.translocateInitiator aa] ++
      Program.compileElongation (.M,[aa]) rest

def termination (tail : List AA) : List Reaction :=
  match tail with
  | [] => [.stopInitiator,.releaseInitiator]
  | _ :: _ => [.stopPeptidyl (.M,tail),.releasePeptidyl (.M,tail)]

/-- A source-generated post-start-recognition program, with raw initiator charging and terminal release. -/
def compile (tail : List AA) : List Reaction :=
  (.chargeInitiator :: tail.map Reaction.charge) ++
    [.captureInitiator,.joinSubunit] ++ elongation tail ++ termination tail

def sourceProgram (edits : Target.Edits) (water additional : Nat) : Option (List Reaction) := do
  let peptide ← CPS1EndogenousTranslation.continuedPeptide edits water additional
  if peptide.1 = .M then some (compile peptide.2) else none

def sourceExecution (edits : Target.Edits) (water additional : Nat) (raw : Stock) : Option Execution :=
  (sourceProgram edits water additional).map (fun program => execute program raw)

theorem source_selected_initiator (edits : Target.Edits) (water additional : Nat) :
    (CPS1EndogenousTranslation.selectedPeptide edits water additional).1 = .M := by
  unfold CPS1EndogenousTranslation.selectedPeptide
  split <;> decide +kernel

theorem source_generated_program (edits : Target.Edits) (water additional : Nat) :
    sourceProgram edits water additional =
      some (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) := by
  rw [sourceProgram,CPS1EndogenousTranslation.actual_peptide_generated]
  change (if (CPS1EndogenousTranslation.selectedPeptide edits water additional).1 = .M then
    some (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) else none) = _
  rw [if_pos (source_selected_initiator edits water additional)]

theorem source_executes_actual_program (edits : Target.Edits) (water additional : Nat) (raw : Stock) :
    sourceExecution edits water additional raw =
      some (execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw) := by
  rw [sourceExecution,source_generated_program]
  rfl

/-- Species identity and multiplicity remain accounted even when a boundary fails. -/
theorem source_resource_balance (edits : Target.Edits) (water additional : Nat)
    (raw : Stock) (species : Species) :
    let result := execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw
    raw.count species + (credit result.fired).count species =
      result.stock.count species + (debit result.fired).count species :=
  execution_balance _ _ _

theorem source_resource_potential (edits : Target.Edits) (water additional : Nat)
    (raw : Stock) (chemicalPotential : Species → ℚ) :
    let result := execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw
    speciesValue chemicalPotential raw = speciesValue chemicalPotential result.stock +
      affinity chemicalPotential result.fired :=
  execution_potential _ _ _

def actors : Stock := factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF1,.eRF3]

def oneResidueRaw : Stock :=
  [.freeAA .M,.initiatorTRNA,.atp,.subunit40,.subunit60] ++ actors ++
    [.gtp,.water,.gtp,.water,.gtp,.water,.water]

def twoResidueRaw : Stock :=
  [.freeAA .M,.initiatorTRNA,.atp,.freeAA .A,.tRNA .A,.atp,.subunit40,.subunit60] ++ actors ++
    [.gtp,.water,.gtp,.water,.gtp,.water,.gtp,.water,.gtp,.water,.water]

theorem native_one_residue_release :
    (execute (compile []) oneResidueRaw).missing = none ∧
    (execute (compile []) oneResidueRaw).remaining = [] ∧
    (execute (compile []) oneResidueRaw).stock.count (.releasedPeptide (.M,[])) = 1 ∧
    (execute (compile []) oneResidueRaw).stock.count .postTerminationInitiator = 1 ∧
    (execute (compile []) oneResidueRaw).stock.count .initiatorTRNA = 0 ∧
    (execute (compile []) oneResidueRaw).stock.count .gdp = 3 := by
  decide +kernel

theorem native_two_residue_release :
    (execute (compile [.A]) twoResidueRaw).missing = none ∧
    (execute (compile [.A]) twoResidueRaw).remaining = [] ∧
    (execute (compile [.A]) twoResidueRaw).stock.count (.releasedPeptide (.M,[.A])) = 1 ∧
    (execute (compile [.A]) twoResidueRaw).stock.count .initiatorTRNA = 1 ∧
    (execute (compile [.A]) twoResidueRaw).stock.count (.postTerminationElongator .A) = 1 ∧
    (execute (compile [.A]) twoResidueRaw).stock.count .gdp = 5 := by
  decide +kernel

theorem wrong_elongator_cannot_substitute_initiator :
    (execute (compile []) (oneResidueRaw.erase .initiatorTRNA ++ [.tRNA .M])).missing =
      some .initiatorTRNA ∧
    (execute (compile []) (oneResidueRaw.erase .initiatorTRNA ++ [.tRNA .M])).fired = [] := by
  decide +kernel

theorem missing_second_initiation_gtp_retains_first_update :
    let raw := [.freeAA .M,.initiatorTRNA,.atp,.subunit40,.subunit60] ++ actors ++ [.gtp,.water]
    let result := execute (compile []) raw
    result.missing = some .gtp ∧ result.stock.count .initiator48S = 1 ∧
      result.stock.count .gdp = 1 ∧ result.stock.count (.releasedPeptide (.M,[])) = 0 := by
  decide +kernel

theorem missing_release_water_preserves_actual_termination :
    let raw := oneResidueRaw.erase .water
    let result := execute (compile []) raw
    result.missing = some .water ∧ result.stock.count .terminatingInitiator = 1 ∧
      result.stock.count (.releasedPeptide (.M,[])) = 0 ∧ result.stock.count .gdp = 3 := by
  decide +kernel

/-- Generation factors through the actual coding word and its first-AUG/first-stop parser. -/
theorem source_coding_program (edits : Target.Edits) (water additional : Nat) :
    sourceProgram edits water additional = (do
      let dna ← CPS1Deamination.ContinuedCoding.continuedCoding edits water additional
      let peptide ← CPS1EndogenousTranslation.peptideFromCoding? dna
      if peptide.1 = .M then some (compile peptide.2) else none) := by
  unfold sourceProgram CPS1EndogenousTranslation.continuedPeptide
    CPS1Deamination.ContinuedCoding.continuedStopChain CPS1EndogenousTranslation.peptideFromCoding?
  simp only [bind_assoc]

theorem source_resource_cut (edits : Target.Edits) (water additional : Nat) (raw : Stock)
    (missing : Species)
    (cut : (execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw).missing =
      some missing) :
    ∃ reaction rest,
      (execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw).remaining =
        reaction :: rest ∧
      (execute (compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) raw).stock.count missing <
        reaction.reactants.count missing := execution_cut _ _ _ cut

theorem source_resource_disposition (edits : Target.Edits) (water additional : Nat) (raw : Stock) :
    let program := compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2
    let result := execute program raw
    result.fired ++ result.remaining = program := execution_decomposes _ _

theorem source_fine_inventory (edits : Target.Edits) (water additional : Nat) (raw : Stock) :
    let program := compile (CPS1EndogenousTranslation.selectedPeptide edits water additional).2
    let result := execute program raw
    (∀ actor, moiety (Accounting.actorCount actor) raw = moiety (Accounting.actorCount actor) result.stock) ∧
    (∀ subunit, moiety (Accounting.subunitCount subunit) raw = moiety (Accounting.subunitCount subunit) result.stock) ∧
    moiety Accounting.initiatorCount raw = moiety Accounting.initiatorCount result.stock :=
  ⟨fun actor => Accounting.execution_actor_balance _ _ actor,
    fun subunit => Accounting.execution_subunit_balance _ _ subunit,
    Accounting.execution_initiator_balance _ _⟩

structure SourceProgramContract : Prop where
  actualCoding : type_of% source_coding_program
  sourceProgram : type_of% source_generated_program
  nativeExecution : type_of% source_executes_actual_program
  speciesBalance : type_of% source_resource_balance
  chemicalPotential : type_of% source_resource_potential
  cut : type_of% source_resource_cut
  disposition : type_of% source_resource_disposition
  fineInventory : type_of% source_fine_inventory

theorem sourceGeneratedProgramContract : SourceProgramContract :=
  ⟨source_coding_program,source_generated_program,source_executes_actual_program,
    source_resource_balance,source_resource_potential,source_resource_cut,
    source_resource_disposition,source_fine_inventory⟩

end CPS1InitiationTermination.UnifiedBoundary
