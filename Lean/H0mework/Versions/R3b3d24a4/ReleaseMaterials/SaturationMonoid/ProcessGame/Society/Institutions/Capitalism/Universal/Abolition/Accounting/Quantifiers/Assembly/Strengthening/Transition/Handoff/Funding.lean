import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff.Source
import H0mework.Versions.R3b3d24a4.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Exchange.Run

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff

open Source.Program Quantities PublicFunction Abolition.Root Abolition.Root.Registered

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {source : Evolving.Epoch.Current (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {position : PublicFunction.Repayment.Position Party Instrument}
  {exchange : Exchange.Plan Party Good Port Technology Instrument} {index : Nat}

/-- Take the actual disposition of the original funding legs. Refused
funding contributes no instruction or stock to the handoff. -/
def withExchange (outcome : Exchange.Outcome source position exchange index)
    (proposal : Proposal Party Good Port Technology Instrument) : Proposal Party Good Port Technology Instrument :=
  { proposal with preparation := outcome.script ++ proposal.preparation }

theorem the_bridge_begins_at_the_original_exchange_successor
    (outcome : Exchange.Outcome source position exchange index)
    (proposal : Proposal Party Good Port Technology Instrument) :
    prepared source (withExchange outcome proposal) = prepared outcome.current proposal := by
  simp only [prepared, preparedScript, withExchange, Execution.endAt_append]

theorem the_exchange_and_migration_have_one_original_ledger
    (outcome : Exchange.Outcome source position exchange index)
    (proposal : Proposal Party Good Port Technology Instrument) :
    Recorded source (script source (withExchange outcome proposal)) ∧
      prepared source (withExchange outcome proposal) = prepared outcome.current proposal :=
  ⟨the_handoff_uses_one_original_ledger _ _, the_bridge_begins_at_the_original_exchange_successor outcome proposal⟩

def fundedCandidates (outcome : Exchange.Outcome source position exchange index)
    (preparationLimit prefixLimit renewalLimit : Nat) :
    List (Proposal Party Good Port Technology Instrument) :=
  (sourceCandidates outcome.current preparationLimit prefixLimit renewalLimit).map (withExchange outcome)

/-- The selection compares the funded words on the pre-exchange clock and
inventory. Its budgets and handoff include the actual exchange prefix. -/
def selectWithExchange {TaskId : Type} [DecidableEq TaskId]
    (outcome : Exchange.Outcome source position exchange index)
    (preparationLimit prefixLimit renewalLimit : Nat)
    (ordered : List TaskId) (task : TaskId → PublicTaskSpec Party Good)
    (reserved : ∀ word : List (Option (Compile.RawInput Party Good Port Technology Instrument)),
      Finset (Due.Service.Ordinal source word))
    (held : Finset (Due.Service.Need ordered.toFinset task)) (budget : Party × Good → ℚ) (deadline : WithTop ℚ) :=
  select source ordered task reserved held budget deadline
    (fundedCandidates outcome preparationLimit prefixLimit renewalLimit) (handoffTime source)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Transition.Handoff
