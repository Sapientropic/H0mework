import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Joint.Consumers.Compact.Execution

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers

open Source.Program Innovation PublicFunction ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered
open Quantifiers.Joint

noncomputable section

namespace CompactSource
export Quantifiers.Joint.Consumers.Compact (past response)
export Quantifiers.Joint.Consumers.Compact.Original (initial)
end CompactSource

/-- The old controlled operation still belongs to the original debtor.
The other participant can produce replenishable food once access is opened. -/
def law : RawLaw Bool Bool Bool Unit Unit := { Quantifiers.Joint.Consumers.Compact.law with
  technique := fun _ person =>
    ⟨[], if person then [(false,18), (true,2)] else [(false,18)], [], [true]⟩ }

abbrev code : Distributed.Code Bool Bool Bool Unit Unit :=
  { Quantifiers.Joint.Consumers.Compact.code with
    law := law
    initial := law.next CompactSource.initial [] }

def mechanism : Trials.Mechanism Bool Bool Bool Unit Unit :=
  { Quantifiers.Joint.Consumers.Compact.mechanism with code := code }

def nature : mechanism.Nature := Quantifiers.Joint.Consumers.Compact.nature
def oldWord := Control.responseWord mechanism CompactSource.past nature CompactSource.response

def input : ProgrammeSource.Input Bool Bool Bool Unit Unit where
  law := law
  initial := CompactSource.initial
  instructions := oldWord

def productiveClaim : Responsibility.Family.Claim mechanism CompactSource.past nature CompactSource.response :=
  (Responsibility.Family.assess mechanism CompactSource.past nature CompactSource.response).get
    (by decide +kernel)

def oldFrame := Financial.Installation.Runtime.frames input 0 19
def native := oldFrame.native
def visit : SourceNativeTemporalVisitAt native.root.toAuthoritativeRoot.toLedgerRoot := oldFrame.temporal input

theorem cursor_eq : oldFrame.cursor input = Financial.Installation.Runtime.cursorAt input 0 19 :=
  Financial.Installation.Runtime.frames_cursor input 0 19

theorem the_original_cause_is_at_its_paid_native_cut :
    Financial.Installation.Cursor.lastExecutedIndex input (Financial.Installation.Runtime.cursorAt input 0 19) = 1 ∧
      Financial.Installation.Cursor.pending input (Financial.Installation.Runtime.cursorAt input 0 19) = [] := by
  decide +kernel

theorem origin : Abolition.Accounting.Root.Source.OriginAt input native visit productiveClaim where
  law := rfl
  before := by
    change code.initial = ProgrammeSource.rawCurrent input
      (Financial.Installation.Cursor.lastExecutedVisit input (oldFrame.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_cause_is_at_its_paid_native_cut.1]
    rfl
  word := by
    change oldWord = ProgrammeSource.rawEvent input
      (Financial.Installation.Cursor.lastExecutedVisit input (oldFrame.cursor input)).current
    rw [cursor_eq]
    unfold Financial.Installation.Cursor.lastExecutedVisit
    rw [the_original_cause_is_at_its_paid_native_cut.1]
    rfl
  history := by
    change CompactSource.past = (List.range (Financial.Installation.Cursor.lastExecutedIndex
      input (oldFrame.cursor input))).map (fun index =>
        ProgrammeSource.rawEvent input (ProgrammeHistory.visitAt input index).current)
    rw [cursor_eq, the_original_cause_is_at_its_paid_native_cut.1]
    rfl
  accounted := by
    change Financial.Installation.Cursor.pending input (oldFrame.cursor input) = []
    rw [cursor_eq]
    exact the_original_cause_is_at_its_paid_native_cut.2

def seed : Global.Seed (mechanism := mechanism) (past := CompactSource.past)
    (nature := nature) (response := CompactSource.response) :=
  ⟨input, 0, 19, productiveClaim, origin, []⟩

def grossClaim : Entitlement.Source.Claim (window seed) :=
  (Entitlement.Source.assess (window seed)).get (by
    have named : Entitlement.Source.demands (window seed) ≠ [] := by
      unfold Entitlement.Source.demands Entitlement.Source.Window.legs
      unfold Entitlement.Source.Window.before Entitlement.Source.Window.word Entitlement.Source.Window.visit
        Entitlement.Source.Window.cursor Entitlement.Source.Window.frame window seed
      simp only [Financial.Installation.Cursor.lastExecutedVisit]
      decide +kernel
    simp only [Entitlement.Source.assess, dif_pos (original_cause_is_accounted seed),
      dif_pos named, Option.isSome_some])

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Consumers
