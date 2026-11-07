import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold

/-! A finite native suffix from the original physical input past. Each
prefix uses its literal source occurrence and the shared item factory.
The current incoming payload is not part of this fold. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.ActualPast

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Interface.ActualOccurrence

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)

abbrev Input := Registered.Compile.RawInput Party Good Port Technology Instrument

def foldFrom (priorInputs : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) →
    (process input depth count).GeneratedState → (process input depth count).GeneratedState
  | [], state => state
  | raw :: remaining, state => foldFrom (priorInputs ++ [raw]) remaining
      (consumeVisit input depth count (eventTag input depth count prefixLimit renewalLimit priorInputs raw)
        (eventVisit input depth count prefixLimit renewalLimit priorInputs raw) state)

def runFrom (priorInputs past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (state : (process input depth count).GeneratedState) :
    (process input depth count).Run state.current (foldFrom input depth count prefixLimit renewalLimit priorInputs past state).current := by
  induction past generalizing priorInputs state with
  | nil => exact .nil
  | cons raw remaining inherited =>
      exact (consumeVisit_run input depth count (eventTag input depth count prefixLimit renewalLimit priorInputs raw)
        (eventVisit input depth count prefixLimit renewalLimit priorInputs raw) state).concatRuns (process input depth count)
          (inherited (priorInputs ++ [raw]) _)

def account (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) := foldFrom input depth count prefixLimit renewalLimit [] past initial

def run (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :
    (process input depth count).Run initial.current (account input depth count prefixLimit renewalLimit past initial).current :=
  runFrom input depth count prefixLimit renewalLimit [] past initial

theorem from_append (priorInputs left right : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :
    foldFrom input depth count prefixLimit renewalLimit priorInputs (left ++ right) initial =
      foldFrom input depth count prefixLimit renewalLimit (priorInputs ++ left) right
        (foldFrom input depth count prefixLimit renewalLimit priorInputs left initial) := by
  induction left generalizing priorInputs initial with
  | nil => simp only [List.nil_append, foldFrom, List.append_nil]
  | cons raw remaining inherited =>
      simp only [List.cons_append, foldFrom, inherited, List.append_assoc, List.nil_append]

theorem account_append (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (raw : Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))
    (initial : (process input depth count).GeneratedState) :
    account input depth count prefixLimit renewalLimit (past ++ [raw]) initial =
      consumeVisit input depth count (eventTag input depth count prefixLimit renewalLimit past raw)
        (eventVisit input depth count prefixLimit renewalLimit past raw)
        (account input depth count prefixLimit renewalLimit past initial) := by
  unfold account
  rw [from_append]
  rfl

theorem cursor_append_is_one_original_update
    (current : Registered.Physical.Cursor Party Good Port Technology Instrument)
    (initial : (process input depth count).GeneratedState) :
    account input depth count prefixLimit renewalLimit (Registered.Physical.next current).past initial =
      consumeVisit input depth count (.actual prefixLimit renewalLimit current)
        (Interface.root input depth count (.actual prefixLimit renewalLimit current)).initialVisit
        (account input depth count prefixLimit renewalLimit current.past initial) := by
  change account input depth count prefixLimit renewalLimit (current.past ++ [current.incoming]) initial = _
  rw [account_append]
  exact congrArg (fun cursor : Registered.Physical.Cursor Party Good Port Technology Instrument =>
    consumeVisit input depth count (.actual prefixLimit renewalLimit cursor)
      (Interface.root input depth count (.actual prefixLimit renewalLimit cursor)).initialVisit
      (account input depth count prefixLimit renewalLimit current.past initial))
    (reconstruction_has_the_same_cursor current)

theorem original_account_history_is_retained
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :
    initial.current.history <+: (account input depth count prefixLimit renewalLimit past initial).current.history := by
  rw [(run input depth count prefixLimit renewalLimit past initial).history_eq]
  exact List.prefix_append _ _

#print axioms run
#print axioms cursor_append_is_one_original_update
#print axioms original_account_history_is_retained

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.ActualPast
