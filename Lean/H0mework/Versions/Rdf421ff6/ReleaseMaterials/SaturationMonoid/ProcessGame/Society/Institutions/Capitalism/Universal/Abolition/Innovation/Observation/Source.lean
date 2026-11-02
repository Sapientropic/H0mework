import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Current
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Prefix
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Recall

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation

open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root Abolition.Root.Registered Source.Program
open PublicFunction.Distributed

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

/-- The sensor and its own material charge are fixed before the reading. -/
structure Rule (Party Good Port Technology Instrument : Type)
    [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument] where
  code : Code Party Good Port Technology Instrument
  site : Fin code.sites
  cost : Bundle Good
  cost_nonnegative : NonnegativeBundle Good cost
  cost_positive : ∃ good, 0 < amount Good cost good
  port : Port

namespace Rule

variable (rule : Rule Party Good Port Technology Instrument)

def observer := rule.code.siteParty rule.site

def request : Request Party Good Port Technology Instrument :=
  ⟨rule.observer, [], rule.port, [], .use rule.observer rule.cost .contribution⟩

omit [DecidableEq Port] in
theorem its_original_request_is_self_signed_and_self_charged :
    rule.request.signer = rule.observer ∧ rule.request.consents = [] ∧
      rule.request.operation = .use rule.observer rule.cost .contribution := ⟨rfl, rfl, rfl⟩

omit [DecidableEq Port] in
theorem public_resigning_keeps_the_original_observation_request :
    rule.request.resign rule.request.signer = rule.request := rfl

end Rule

variable (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (rule : Rule Party Good Port Technology Instrument)

abbrev Before (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast past

def readCursor (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  Physical.receive (Physical.Prefix.cursor past) (.primitive rule.request)

def originalResult (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  Physical.Public.compile input (Before input depth count prefixLimit renewalLimit oldPast past)
    (.primitive rule.request)

def localSnapshot (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  rule.code.snapshot rule.site (Before input depth count prefixLimit renewalLimit oldPast past).raw

def localSignal (past : List (Compile.RawInput Party Good Port Technology Instrument)) :=
  rule.code.readLocal rule.site (localSnapshot input depth count prefixLimit renewalLimit oldPast rule past)

theorem the_read_uses_the_effective_interpreter_at_the_original_prefix
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    originalResult input depth count prefixLimit renewalLimit oldPast rule past =
      Physical.Public.compile input (Before input depth count prefixLimit renewalLimit oldPast past)
        (.primitive rule.request) := rfl

theorem the_read_is_the_original_public_result
    (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    HEq (Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast (readCursor rule past))
      (originalResult input depth count prefixLimit renewalLimit oldPast rule past) := by
  have natural (first second : List (Compile.RawInput Party Good Port Technology Instrument)) (same : first = second) :
      HEq (Physical.Public.compile input (Before input depth count prefixLimit renewalLimit oldPast first) (.primitive rule.request))
        (Physical.Public.compile input (Before input depth count prefixLimit renewalLimit oldPast second) (.primitive rule.request)) := by
    cases same
    rfl
  exact natural _ _ (Physical.Prefix.past_readback past)

theorem a_paid_read_contains_the_original_valid_item
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (paid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = true) :
    let before := (Before input depth count prefixLimit renewalLimit oldPast past).raw
    let item : ExecutionItem Party Good Port Technology Instrument := ⟨0, before, rule.request⟩
    item ∈ (originalResult input depth count prefixLimit renewalLimit oldPast rule past).execution.items ∧
      (Physical.Public.interpreter input).Valid before rule.request := by
  cases source : originalResult input depth count prefixLimit renewalLimit oldPast rule past with
  | accepted word selected checked =>
      have selectedWord : [rule.request] = word := by
        change some [rule.request.resign rule.request.signer] = some word at selected
        rw [rule.public_resigning_keeps_the_original_observation_request] at selected
        exact Option.some.inj selected
      subst word
      have valid := checked ⟨0, (Before input depth count prefixLimit renewalLimit oldPast past).raw, rule.request⟩
        (by simp only [RawLaw.rawItems, RawLaw.execute, List.mem_cons, true_or])
      simp only [Physical.Public.ResultAt.execution, RawLaw.execute, List.mem_cons, true_or]
      exact ⟨trivial, valid⟩
  | refused word selected item listed failed => simp only [source, Physical.Public.ResultAt.isAccepted, Bool.false_eq_true] at paid
  | metadata selected => simp only [source, Physical.Public.ResultAt.isAccepted, Bool.false_eq_true] at paid

theorem a_paid_read_debits_only_its_original_observer
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (paid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = true) :
    let before := (Before input depth count prefixLimit renewalLimit oldPast past).raw
    (Physical.Public.interpreter input).actualDebit before rule.request = locate rule.observer rule.cost ∧
      (Physical.Public.interpreter input).actualCredit before rule.request = [] := by
  have valid := (a_paid_read_contains_the_original_valid_item input depth count prefixLimit renewalLimit oldPast rule past paid).2
  dsimp only
  rw [RawLaw.actualDebit, if_pos valid, RawLaw.actualCredit, if_pos valid]
  exact ⟨rfl, rfl⟩

theorem the_original_positive_charge_is_actually_deducted
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (paid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = true) :
    ∃ good, 0 < flowAt ((Physical.Public.interpreter input).actualDebit
      (Before input depth count prefixLimit renewalLimit oldPast past).raw rule.request) rule.observer good := by
  obtain ⟨good, positive⟩ := rule.cost_positive
  refine ⟨good, ?_⟩
  rw [(a_paid_read_debits_only_its_original_observer input depth count prefixLimit renewalLimit oldPast rule past paid).1]
  simpa only [flowAt, locate, amount, List.map_map, Function.comp_def, Prod.mk.injEq, true_and] using positive

/-- A readout of the original compiler's rejected item, not a new receipt. -/
def originalFailure? (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    Option {item : ExecutionItem Party Good Port Technology Instrument //
      item ∈ (Physical.Public.interpreter input).rawItems
        (Before input depth count prefixLimit renewalLimit oldPast past).raw [rule.request] ∧
      ¬ (Physical.Public.interpreter input).Valid item.before item.request} := by
  cases source : originalResult input depth count prefixLimit renewalLimit oldPast rule past with
  | accepted word selected checked => exact none
  | metadata selected => exact none
  | refused word selected item listed failed =>
      have selectedWord : [rule.request] = word := by
        change some [rule.request.resign rule.request.signer] = some word at selected
        rw [rule.public_resigning_keeps_the_original_observation_request] at selected
        exact Option.some.inj selected
      exact some ⟨item, selectedWord.symm ▸ listed, failed⟩

def paidNotice? (past : List (Compile.RawInput Party Good Port Technology Instrument)) :
    Option (Recall.Notice rule.code) :=
  if (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted then
    some (.sent rule.site (localSignal input depth count prefixLimit renewalLimit oldPast rule past))
  else none

theorem an_unpaid_read_cannot_add_local_knowledge
    (past : List (Compile.RawInput Party Good Port Technology Instrument))
    (unpaid : (originalResult input depth count prefixLimit renewalLimit oldPast rule past).isAccepted = false) :
    paidNotice? input depth count prefixLimit renewalLimit oldPast rule past = none := by
  simp only [paidNotice?, unpaid, Bool.false_eq_true, ↓reduceIte]

#print axioms a_paid_read_contains_the_original_valid_item
#print axioms a_paid_read_debits_only_its_original_observer
#print axioms the_original_positive_charge_is_actually_deducted
#print axioms an_unpaid_read_cannot_add_local_knowledge

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Innovation.Observation
