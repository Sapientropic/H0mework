import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.NativeComplete

set_option autoImplicit false

namespace CPS1InitiationTermination.Source
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def rawSourceFuel (edits : Target.Edits) (water additional : Nat) : Option Stock :=
  (CPS1EndogenousTranslation.continuedPeptide edits water additional).map
    (fun peptide => NativeComplete.rawFuel peptide.2)

theorem source_raw_fuel_generated (edits : Target.Edits) (water additional : Nat) :
    rawSourceFuel edits water additional = some
      (NativeComplete.rawFuel (CPS1EndogenousTranslation.selectedPeptide edits water additional).2) := by
  rw [rawSourceFuel, CPS1EndogenousTranslation.actual_peptide_generated]
  rfl

theorem source_native_complete (edits : Target.Edits) (water additional : Nat) :
    let tail := (CPS1EndogenousTranslation.selectedPeptide edits water additional).2
    let fuel := NativeComplete.rawFuel tail
    let result := execute (UnifiedBoundary.compile tail) fuel
    rawSourceFuel edits water additional = some fuel ∧
    UnifiedBoundary.sourceExecution edits water additional fuel = some result ∧
    result.fired = UnifiedBoundary.compile tail ∧ result.remaining = [] ∧ result.missing = none ∧
    result.stock.Perm (NativeComplete.finalProducts tail) := by
  exact ⟨source_raw_fuel_generated edits water additional,
    UnifiedBoundary.source_executes_actual_program edits water additional _,
    NativeComplete.canonical_raw_complete _⟩

structure BoundaryContract : Prop where
  program : UnifiedBoundary.SourceProgramContract
  released : type_of% source_native_complete

theorem sourceGeneratedBoundary : BoundaryContract :=
  ⟨UnifiedBoundary.sourceGeneratedProgramContract,source_native_complete⟩

end CPS1InitiationTermination.Source
