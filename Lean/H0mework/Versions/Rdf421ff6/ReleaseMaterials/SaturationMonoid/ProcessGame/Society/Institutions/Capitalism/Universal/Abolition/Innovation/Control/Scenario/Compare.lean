import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control.Physical
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Trials.Source.Decision

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control

open Source.Program
open SaturationMonoid.ProcessGame.Society.PublicFunction

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]

/-- The same executable programme is interpreted publicly; its signed
financing, investment, local rule and finite closing obligations remain. -/
def openedProgramme (source : Trials.Mechanism Party Good Port Technology Instrument) :
    Trials.Mechanism Party Good Port Technology Instrument :=
  { source with code := { source.code with law := physicalLaw source.code.law } }

abbrev HistoryResponse := List (RawEvent Party Good Port Technology Instrument) →
  RawEvent Party Good Port Technology Instrument → RawCurrent Party Good Technology Instrument →
    RawEvent Party Good Port Technology Instrument

def responseWord (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :=
  source.word nature ++ opponent past (source.word nature) (source.after nature)

def responseExecution (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :=
  source.code.law.execute source.code.initial 0 (responseWord source past nature opponent)

def measuredLoss (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (good : Good) :=
  controlLoss source.code.law (openedProgramme source).code.law
    (responseExecution source past nature opponent).items
    (responseExecution (openedProgramme source) past nature opponent).items good

def isProductiveBlockage (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (good : Good) : Bool :=
  decide (0 < measuredLoss source past nature opponent good)

theorem the_two_runs_keep_one_source_seed_and_every_contribution_clause
    (source : Trials.Mechanism Party Good Port Technology Instrument) :
    (openedProgramme source).code.initial = source.code.initial ∧
      (openedProgramme source).funding = source.funding ∧
      (openedProgramme source).investmentRequest = source.investmentRequest ∧
      (openedProgramme source).closing = source.closing ∧
      HEq (openedProgramme source).policy source.policy := ⟨rfl,rfl,rfl,rfl,HEq.rfl⟩

theorem every_unknown_event_and_finite_reaction_has_an_exact_cost_classification
    (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) (good : Good) :
    isProductiveBlockage source past nature opponent good = true ↔
      cost (openedProgramme source).code.law
          (responseExecution (openedProgramme source) past nature opponent).items good -
        cost source.code.law (responseExecution source past nature opponent).items good <
      output (openedProgramme source).code.law
          (responseExecution (openedProgramme source) past nature opponent).items good -
        output source.code.law (responseExecution source past nature opponent).items good := by
  unfold isProductiveBlockage measuredLoss
  rw [decide_eq_true_eq, control_loss_is_foregone_output_after_all_additional_costs]
  exact sub_pos

theorem the_response_inventory_retains_every_attempt_in_order
    (source : Trials.Mechanism Party Good Port Technology Instrument)
    (past : List (RawEvent Party Good Port Technology Instrument))
    (nature : Request Party Good Port Technology Instrument)
    (opponent : HistoryResponse (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)) :
    (responseExecution source past nature opponent).items.map ExecutionItem.request =
      responseWord source past nature opponent :=
  source.code.law.inventory_requests_exact source.code.initial 0 _

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Control
