import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Material.Payments
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Fold

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.PublicFunction
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Registered Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (code : SourceCode Party Good Port Technology Instrument) (depth count : Nat)

def declarationOrdinal := Settlement.physicalIndex code.input depth count - 1

theorem original_entry_ordinal : declarationOrdinal code depth 0 = depth + 1 := by
  unfold declarationOrdinal Settlement.physicalIndex Settlement.oldCursor Settlement.oldFrame
  rw [Financial.Installation.Runtime.frames_cursor]
  change Financial.Installation.Cursor.physicalVisitIndex code.input
    (Financial.Installation.Cursor.next code.input (Financial.Installation.Ingress.start code.input depth)) - 1 = depth + 1
  rw [Financial.Installation.Cursor.entry_has_one_actual_body code.input _ rfl]
  rfl

/-- The identity test is an original occurrence address, never equality of
service content. Its task equality is derived from that same source write. -/
structure SameBirth (task : Material.OriginalTask code.input depth count) : Type where
  private mk ::
  originalOrdinal : declarationOrdinal code depth count = 1
  task_eq : task.val = originalTask code

omit [DecidableEq Port] in
theorem source_payload_at_the_first_original_body :
    taskOfPayload (originalPayload code.input (ProgrammeHistory.visitAt code.input 1).current) =
      some (originalTask code) := by
  rw [show (ProgrammeHistory.visitAt code.input 1).current =
    .running (code.currentAt 1)
      (ProgrammeSource.pastAt (ProgrammeHistory.visitAt code.input 1).current) from rfl]
  dsimp only [originalPayload]
  rw [every_original_row_writes_the_same_payload]
  rfl

def sameBirth (task : Material.OriginalTask code.input depth count)
    (original : declarationOrdinal code depth count = 1) : SameBirth code depth count task := by
  refine ⟨original, ?_⟩
  have disclosed := task.property
  change taskOfPayload (originalPayload code.input
    (ProgrammeHistory.visitAt code.input (declarationOrdinal code depth count)).current) = some task.val at disclosed
  rw [original, source_payload_at_the_first_original_body] at disclosed
  exact (Option.some.inj disclosed).symm

variable (prefixLimit renewalLimit : Nat)
  (snapshot : Physical.Cursor Party Good Port Technology Instrument)

/-- A later declaration remains a distinct responsibility. Its original
native source, full state and source row remain available in the residual. -/
structure DistinctDeclaration where
  private mk ::
  ordinal : Nat
  originalOrdinal : ordinal = declarationOrdinal code depth count
  notBirth : ordinal ≠ 1

def DistinctDeclaration.originalRow (_residual : DistinctDeclaration code depth count) :=
  ProgrammeSource.sourceEntry code.input (Settlement.committedVisit code.input depth count).current .inherited

def DistinctDeclaration.originalNextRow (residual : DistinctDeclaration code depth count) :=
  ((ProgrammeLedger.evolution code.input (Settlement.committedVisit code.input depth count).current).destination
    residual.originalRow).1

def DistinctDeclaration.retainedState (_residual : DistinctDeclaration code depth count) (index : Slot code) :=
  (OriginAt.source code).state depth count
    (atPast (.source code) depth count prefixLimit renewalLimit snapshot.past index)

inductive Recognition (task : Material.OriginalTask code.input depth count) where
  | same (identity : SameBirth code depth count task)
  | distinct (residual : DistinctDeclaration code depth count)

def recognize (task : Material.OriginalTask code.input depth count) : Recognition code depth count task :=
  if original : declarationOrdinal code depth count = 1 then .same (sameBirth code depth count task original)
  else .distinct ⟨_, rfl, original⟩

theorem a_later_declaration_keeps_its_original_responsibility
    (residual : DistinctDeclaration code depth count) :
    residual.originalNextRow = ProgrammeSource.targetEntry code.input
      (Settlement.committedVisit code.input depth count).current .inherited := by
  unfold DistinctDeclaration.originalNextRow DistinctDeclaration.originalRow
  cases (Settlement.committedVisit code.input depth count).current <;>
    exact ProgrammeLedger.destination_exact code.input _ _

theorem recognition_uses_the_original_occurrence
    (task : Material.OriginalTask code.input depth count) :
    match recognize code depth count task with
    | .same _identity => declarationOrdinal code depth count = 1 ∧ task.val = originalTask code
    | .distinct residual => residual.ordinal = declarationOrdinal code depth count ∧ residual.ordinal ≠ 1 := by
  cases recognize code depth count task with
  | same identity => exact ⟨identity.originalOrdinal, identity.task_eq⟩
  | distinct residual => exact ⟨residual.originalOrdinal, residual.notBirth⟩

#print axioms sameBirth
#print axioms recognition_uses_the_original_occurrence
#print axioms a_later_declaration_keeps_its_original_responsibility

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.ReviewSource.Native.Link
