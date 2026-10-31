import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Source

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact

open Source.Program
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

def original := Financial.Installation.Runtime.frames input 0 19
def native := original.native
def visit : SourceNativeTemporalVisitAt native.root.toAuthoritativeRoot.toLedgerRoot := original.temporal input

theorem cursor_eq : original.cursor input = Financial.Installation.Runtime.cursorAt input 0 19 :=
  Financial.Installation.Runtime.frames_cursor input 0 19

theorem the_original_cause_and_financial_queue_are_fully_consumed :
    Financial.Installation.Cursor.lastExecutedIndex input (Financial.Installation.Runtime.cursorAt input 0 19) = 1 ∧
      Financial.Installation.Cursor.pending input (Financial.Installation.Runtime.cursorAt input 0 19) = [] := by decide +kernel

theorem origin : Abolition.Accounting.Root.Source.OriginAt input native visit productiveClaim where
  law := rfl
  before := by
    change mechanism.code.initial = ProgrammeSource.rawCurrent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_cause_and_financial_queue_are_fully_consumed.1]
    rfl
  word := by
    change originalWord = ProgrammeSource.rawEvent input
      (Financial.Installation.Cursor.lastExecutedVisit input (original.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_cause_and_financial_queue_are_fully_consumed.1]
    rfl
  history := by
    change past = (List.range (Financial.Installation.Cursor.lastExecutedIndex input (original.cursor input))).map
      (fun index => ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current)
    rw [cursor_eq,the_original_cause_and_financial_queue_are_fully_consumed.1]
    rfl
  accounted := by
    change Financial.Installation.Cursor.pending input (original.cursor input) = []
    rw [cursor_eq]
    exact the_original_cause_and_financial_queue_are_fully_consumed.2

def seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response) where
  input := input
  depth := 0
  count := 19
  claim := productiveClaim
  origin := origin
  inputs := []

theorem window_before : (window seed).before = before := origin.before.symm
theorem window_word : (window seed).word = originalWord := origin.word.symm

theorem the_gross_source_has_only_its_original_hundred :
    (Entitlement.Source.demands (window seed)).map Entitlement.Source.Demand.quantity = [100] := by
  unfold Entitlement.Source.demands Entitlement.Source.Window.legs
  unfold Entitlement.Source.Window.before Entitlement.Source.Window.word Entitlement.Source.Window.visit
    Entitlement.Source.Window.cursor Entitlement.Source.Window.frame window seed
  simp only [Financial.Installation.Cursor.lastExecutedVisit]
  decide +kernel

def grossClaim : Entitlement.Source.Claim (window seed) :=
  (Entitlement.Source.assess (window seed)).get (by
    have nonempty : Entitlement.Source.demands (window seed) ≠ [] := by
      intro empty
      have source := the_gross_source_has_only_its_original_hundred
      rw [empty] at source
      cases source
    simp only [Entitlement.Source.assess,dif_pos (original_cause_is_accounted seed),dif_pos nonempty,Option.isSome_some])

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact
