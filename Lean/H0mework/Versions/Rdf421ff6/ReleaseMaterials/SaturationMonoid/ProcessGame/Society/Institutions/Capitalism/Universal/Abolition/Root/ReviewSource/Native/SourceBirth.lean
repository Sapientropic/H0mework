import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Source
import H0mework.Foundation.Agency.OriginExit

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument)

/-- The source creator declares its first task before its original first
write. It is not reconstructed from a later planning report. -/
def originalTask := code.taskAt (code.currentAt 1)
abbrev Slot := Fin (originalTask code).slots.length
def serviceSlot (index : Slot code) := (originalTask code).slots.get index

def sourceSeat : Fin (ProgrammeSource.registrationSize code.input) :=
  ⟨0, by change 0 < 1; decide⟩

def birthRow := ProgrammeSource.targetEntry code.input .bootstrap (.instruction (sourceSeat code))

structure BirthWrite where
  private mk ::
  original : LedgerEntryEvolutionAt (ProgrammeSource.N code.input)
    ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).1 (birthRow code)
  written : original = ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).2
  inherited : ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).1 =
    ProgrammeWorld.inheritedEntry _ (ProgrammeSource.registrationSize code.input)
  paidRegistration : (birthRow code).progressBudget <
    (ProgrammeWorld.inheritedEntry (RawCurrent Party Good Technology Instrument)
      (ProgrammeSource.registrationSize code.input)).progressBudget

def originalBirthWrite : BirthWrite code where
  original := ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).2
  written := rfl
  inherited := (ProgrammeLedger.first_origin_parent_iff code.input (birthRow code)).mpr
    (by intro impossible; cases impossible)
  paidRegistration := ProgrammeLedger.first_child_debit code.input (birthRow code)
    (by intro impossible; cases impossible)

/-- Raw declaration and native-admission evidence are two restrictions of
the same creator and its original whole-ledger first write. -/
structure Birth where
  private mk ::
  task : PublicTaskSpec Party Good
  taskSource : task = originalTask code
  firstWrite : BirthWrite code
  firstWriteSource : firstWrite = originalBirthWrite code

def generateBirth : Birth code := ⟨originalTask code, rfl, originalBirthWrite code, rfl⟩

theorem source_declares_the_task_used_by_its_actual_first_body :
    (generateBirth code).task = code.taskAt (code.actualExecution 0).before := rfl

theorem original_source_birth_uses_the_original_written_child :
    (generateBirth code).firstWrite.original =
        ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).2 ∧
      ((ProgrammeLedger.evolution code.input .bootstrap).origin (birthRow code)).1 =
        ProgrammeWorld.inheritedEntry _ (ProgrammeSource.registrationSize code.input) ∧
      (birthRow code).progressBudget <
        (ProgrammeWorld.inheritedEntry (RawCurrent Party Good Technology Instrument)
          (ProgrammeSource.registrationSize code.input)).progressBudget :=
  ⟨rfl, (originalBirthWrite code).inherited, (originalBirthWrite code).paidRegistration⟩

#print axioms generateBirth
#print axioms source_declares_the_task_used_by_its_actual_first_body
#print axioms original_source_birth_uses_the_original_written_child

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native
