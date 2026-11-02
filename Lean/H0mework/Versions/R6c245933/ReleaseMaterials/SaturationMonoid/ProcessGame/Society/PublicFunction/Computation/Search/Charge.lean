import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Cut.Consumer
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Prepaid.Receipt

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Charge
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {code : Code Party Good Port (Mandate.State Party Technology) Instrument}

/-- A registered resource quote is fixed independently of the search outcome. -/
structure Quote where
  construction : RawEvent Party Good Port (Mandate.State Party Technology) Instrument
  selection : RawEvent Party Good Port (Mandate.State Party Technology) Instrument

variable (quote : Quote (Party := Party) (Good := Good) (Port := Port)
  (Technology := Technology) (Instrument := Instrument))
abbrev fee := quote.construction ++ quote.selection
abbrev holds (_ : Unit) : Prop := True
def tariff : Tariff (Party := Party) (Good := Good) (Port := Port)
    (Technology := Mandate.State Party Technology) (Instrument := Instrument) Unit := ⟨fun _ => fee quote,fun _ => []⟩
variable (worker : Fin code.sites) (point : View (code := code)) (rival : Opponent code)

def trace : Cut.Trace worker holds (tariff quote) rival point [()] :=
  if empty : (Cut.seed point.point).remaining = 0 then .exhausted point () [] empty
  else match Replay.inspect worker ((tariff quote).word () 1) point rival with
    | .unsupported outside => .stalled point () [] (.unsupported outside) (by simp [Cut.Ready])
    | .withheld supported different => .stalled point () [] (.withheld supported different) (by simp [Cut.Ready])
    | .refused supported emitted illegal => .stalled point () [] (.refused supported emitted illegal) (by simp [Cut.Ready])
    | .paid supported emitted legal =>
        let tried : Replay.Attempt worker ((tariff quote).word () 1) point rival := .paid supported emitted legal
        if ready : Cut.Ready worker tried then .passed point () [] tried ready trivial (.empty tried.next)
        else .stalled point () [] tried ready

variable (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
variable (worker : Fin model.source.code.sites) (point : View (code := model.source.code)) (rival : Opponent model.source.code)
abbrev final := (trace quote worker point rival).final.point
abbrev source := (final quote model worker point rival).source
abbrev facade := Cut.Consumer.facade model worker holds [()] (tariff quote) point rival (trace quote worker point rival)
abbrev endAt := arrival (final quote model worker point rival)
abbrev read := Cut.Consumer.read model worker holds [()] (tariff quote) point rival (trace quote worker point rival)
def paid (ordinal : Nat) : Prop := ∃ checked, (read quote model worker point rival ordinal).1 = some (.accepted checked)

def feeRule (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code) :=
  if supported : fee quote ∈ words model.source.code.actions model.source.code.actionLimit then
    Replay.protocol worker (fee quote) supported
  else original

theorem completed_charge_is_exactly_the_precommitted_rule
    (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
    (result : Inspection holds [()]) (finished : (trace quote worker point rival).result = some result) :
    (trace quote worker point rival).rules = [feeRule quote model worker original] := by
  by_cases empty : (Cut.seed point.point).remaining = 0
  · simp only [trace,dif_pos empty,Cut.Trace.result] at finished
    cases finished
  · cases looked : Replay.inspect worker ((tariff quote).word () 1) point rival with
    | unsupported outside | withheld supported different | refused supported emitted illegal =>
        simp only [trace,dif_neg empty,looked,Cut.Trace.result] at finished
        cases finished
    | paid supported emitted legal =>
        by_cases ready : Cut.Ready worker (Replay.Attempt.paid supported emitted legal)
        · have listed : fee quote ∈ words model.source.code.actions model.source.code.actionLimit := by
            simpa only [tariff,Tariff.word,List.append_nil] using supported
          simp only [trace,dif_neg empty,looked,dif_pos ready,Cut.Trace.rules,
            Replay.Attempt.rule,Option.toList_some,Cut.Trace.rules,List.append_nil]
          simp only [feeRule,dif_pos listed,tariff,Tariff.word,List.append_nil]
        · simp only [trace,dif_neg empty,looked,dif_neg ready,Cut.Trace.result] at finished
          cases finished

end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Charge
