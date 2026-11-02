import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Source.Origin
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Responsibility.Consumer.Matrix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Scenario.Original

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Innovation.Control

noncomputable section

namespace C
export Responsibility.Consumer (programme originalPast nature costedResponse familyClaim matrixWord)
end C

/-- This is the already registered controlled input, with its original
retaliation rule. The costed comparison never creates a second actual source. -/
def input := Scenario.originalInput C.nature Scenario.retaliation

def original := Financial.Installation.Runtime.frames input 1 48

def native := original.native

def visit : SourceNativeTemporalVisitAt native.root.toAuthoritativeRoot.toLedgerRoot := original.temporal input

theorem cursor_eq : original.cursor input = Financial.Installation.Runtime.cursorAt input 1 48 :=
  Financial.Installation.Runtime.frames_cursor input 1 48

set_option maxHeartbeats 2400000 in
theorem the_original_native_cursor_has_finished_the_complete_controlled_inventory :
    Financial.Installation.Cursor.lastExecutedIndex input (Financial.Installation.Runtime.cursorAt input 1 48) = 2 ∧
      Financial.Installation.Cursor.pending input (Financial.Installation.Runtime.cursorAt input 1 48) = [] := by
  decide +kernel

theorem originalOrigin : Source.OriginAt input native visit C.familyClaim where
  law := rfl
  before := by
    change C.programme.code.initial = ProgrammeSource.rawCurrent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_native_cursor_has_finished_the_complete_controlled_inventory.1]
    rfl
  word := by
    change Innovation.Control.responseWord C.programme C.originalPast C.nature C.costedResponse =
      ProgrammeSource.rawEvent input (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_native_cursor_has_finished_the_complete_controlled_inventory.1]
    exact Responsibility.Consumer.the_assessment_preserves_the_entire_original_actual_word
  history := by
    change C.originalPast =
      (List.range (Financial.Installation.Cursor.lastExecutedIndex input (original.cursor input))).map fun index =>
        ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current
    rw [cursor_eq,the_original_native_cursor_has_finished_the_complete_controlled_inventory.1]
    rfl
  accounted := by
    change Financial.Installation.Cursor.pending input (original.cursor input) = []
    rw [cursor_eq]
    exact the_original_native_cursor_has_finished_the_complete_controlled_inventory.2

theorem the_live_physical_cursor_is_the_original_controlled_successor :
    (Source.initialState input native visit C.familyClaim).raw =
      (Responsibility.State.initial Responsibility.Consumer.claim).raw := by
  have sourced := Financial.Installation.Cursor.last_execution_returns_actual_physical_current input
    (native.cursor visit.current)
  change ProgrammeSource.rawCurrent input
    (Financial.Installation.Cursor.physicalVisit input
      (Financial.Installation.Cursor.next input (native.cursor visit.current))).current = _
  rw [← sourced]
  rw [← originalOrigin.law,← originalOrigin.before,← originalOrigin.word]
  rfl

#print axioms originalOrigin
#print axioms the_live_physical_cursor_is_the_original_controlled_successor

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Consumer
