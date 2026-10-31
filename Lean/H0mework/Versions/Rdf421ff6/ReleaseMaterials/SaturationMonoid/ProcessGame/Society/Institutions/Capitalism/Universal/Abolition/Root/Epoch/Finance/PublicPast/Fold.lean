import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Fold
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.Actors.PublicPast

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.PublicPast

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Registered.Compile.RawInput Party Good Port Technology Instrument))

abbrev Input := Registered.Compile.RawInput Party Good Port Technology Instrument

/-- Only the new consumed prefix is folded. Its tags refer to the original
cut and the same public source occurrences used by the existing M0 fold. -/
def foldFrom (prior : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument))) :
    List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)) →
    (process input depth count).GeneratedState → (process input depth count).GeneratedState
  | [], state => state
  | raw :: remaining, state => foldFrom (prior ++ [raw]) remaining
      (consumeVisit input depth count
        (Interface.Actors.PublicPast.eventTag input depth count prefixLimit renewalLimit oldPast prior raw)
        (Interface.Actors.PublicPast.eventVisit input depth count prefixLimit renewalLimit oldPast prior raw) state)

def runFrom (prior past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (state : (process input depth count).GeneratedState) :
    (process input depth count).Run state.current (foldFrom input depth count prefixLimit renewalLimit oldPast prior past state).current := by
  induction past generalizing prior state with
  | nil => exact .nil
  | cons raw remaining inherited =>
      exact (consumeVisit_run input depth count
        (Interface.Actors.PublicPast.eventTag input depth count prefixLimit renewalLimit oldPast prior raw)
        (Interface.Actors.PublicPast.eventVisit input depth count prefixLimit renewalLimit oldPast prior raw) state).concatRuns
          (process input depth count) (inherited (prior ++ [raw]) _)

def account (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :=
  foldFrom input depth count prefixLimit renewalLimit oldPast [] past initial

def run (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :
    (process input depth count).Run initial.current
      (account input depth count prefixLimit renewalLimit oldPast past initial).current :=
  runFrom input depth count prefixLimit renewalLimit oldPast [] past initial

theorem an_empty_new_prefix_is_the_literal_existing_account
    (initial : (process input depth count).GeneratedState) :
    account input depth count prefixLimit renewalLimit oldPast [] initial = initial := rfl

theorem every_new_prefix_retains_the_complete_old_history
    (past : List (Input (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)))
    (initial : (process input depth count).GeneratedState) :
    initial.current.history <+:
      (account input depth count prefixLimit renewalLimit oldPast past initial).current.history := by
  rw [(run input depth count prefixLimit renewalLimit oldPast past initial).history_eq]
  exact List.prefix_append _ _

#print axioms run
#print axioms an_empty_new_prefix_is_the_literal_existing_account
#print axioms every_new_prefix_retains_the_complete_old_history

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.PublicPast
