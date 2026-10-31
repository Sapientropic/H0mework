import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross.Prefix
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.History.Runtime
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Transport
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Lifecycle.Observed.Cuts

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Scope (Party := Party) (Good := Good) (Port := Port)}
  (bound : BoundSource base scope)
  (inputs : List (RawEvent Party Good Port (State Party Technology) Instrument))
  (word : RawEvent Party Good Port (State Party Technology) Instrument)

abbrev grantCurrent := Mandate.History.Runtime.currentAt bound inputs
abbrev grantWord := Mandate.History.Runtime.wordAt bound inputs

private def reindex {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Grant base scope first firstWord) : Grant base scope second secondWord := by
  cases sameCurrent
  cases sameWord
  exact grant

private theorem reindex_event {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Grant base scope first firstWord) : (reindex sameCurrent sameWord grant).electionEvent = grant.electionEvent := by
  cases sameCurrent; cases sameWord; rfl

private theorem reindex_index {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Grant base scope first firstWord) :
    (reindex sameCurrent sameWord grant).acceptance.item.val.index = grant.acceptance.item.val.index := by
  cases sameCurrent; cases sameWord; rfl

def transportGrant (birth : Fin (inputs.length + 1))
    (grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)) :
    Grant base scope (grantCurrent bound (nextInputs inputs word) birth.val) (grantWord bound (nextInputs inputs word) birth.val) :=
  reindex (common_current bound inputs word (birth.val + 1) (by omega))
    (common_word bound inputs word birth.val birth.isLt) grant

private theorem reindex_actual {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Grant base scope first firstWord) (actual : grant ∈ grantsAt base scope first firstWord) :
    reindex sameCurrent sameWord grant ∈ grantsAt base scope second secondWord := by
  cases sameCurrent; cases sameWord; exact actual

theorem transportGrant_actual (birth : Fin (inputs.length + 1))
    (grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val))
    (actual : grant ∈ grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)) :
    transportGrant bound inputs word birth grant ∈ grantsAt base scope
      (grantCurrent bound (nextInputs inputs word) birth.val) (grantWord bound (nextInputs inputs word) birth.val) :=
  reindex_actual _ _ grant actual

private theorem reindex_items {first second : RawCurrent Party Good (State Party Technology) Instrument}
    {firstWord secondWord : RawEvent Party Good Port (State Party Technology) Instrument}
    (sameCurrent : second = first) (sameWord : secondWord = firstWord)
    (grant : Grant base scope first firstWord) :
    (reindex sameCurrent sameWord grant).proposal.item.val = grant.proposal.item.val ∧
    (reindex sameCurrent sameWord grant).acceptance.item.val = grant.acceptance.item.val ∧
    (reindex sameCurrent sameWord grant).candidate = grant.candidate := by
  cases sameCurrent
  cases sameWord
  exact ⟨rfl,rfl,rfl⟩

theorem transportGrant_actual_birth_items (birth : Fin (inputs.length + 1))
    (grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)) :
    (transportGrant bound inputs word birth grant).proposal.item.val = grant.proposal.item.val ∧
    (transportGrant bound inputs word birth grant).acceptance.item.val = grant.acceptance.item.val ∧
    (transportGrant bound inputs word birth grant).candidate = grant.candidate :=
  reindex_items _ _ grant

theorem transportGrant_original_admission (birth : Fin (inputs.length + 1))
    (grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)) :
    (admitGrant base scope _ _ (transportGrant bound inputs word birth grant)).native.target =
      (admitGrant base scope _ _ grant).native.target := by
  change (Election.mandateAdmissionEdge Grant.lineageCompiler
    (transportGrant bound inputs word birth grant).electionEvent).target =
      (Election.mandateAdmissionEdge Grant.lineageCompiler grant.electionEvent).target
  rw [show (transportGrant bound inputs word birth grant).electionEvent = grant.electionEvent from reindex_event _ _ grant]

theorem transportGrant_entire_cut_state (birth : Fin (inputs.length + 1))
    (grant : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)) :
    (Lifecycle.Observed.through (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
      (birth := birth.val) (grant := transportGrant bound inputs word birth grant) inputs.length).state =
    (Lifecycle.Observed.through (base := base) (scope := scope)
      (currentAt := grantCurrent bound inputs) (wordAt := grantWord bound inputs)
      (birth := birth.val) (grant := grant) inputs.length).state :=
  Lifecycle.Observed.through_state_congr inputs.length (reindex_index _ _ grant)
    (transportGrant_original_admission bound inputs word birth grant)
    (fun visit earlier => common_current bound inputs word (visit + 1) (by omega))
    (fun visit earlier => common_word bound inputs word visit (by omega))

structure GrantContinuation where
  private mk ::
  birth : Fin (inputs.length + 1)
  original : Grant base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)
  actual : original ∈ grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)
  before : Lifecycle.Observed.History base scope (grantCurrent bound inputs) (grantWord bound inputs) birth.val original
  before_exact : before = Lifecycle.Observed.through inputs.length
  after : Lifecycle.Observed.History base scope (grantCurrent bound (nextInputs inputs word))
    (grantWord bound (nextInputs inputs word)) birth.val (transportGrant bound inputs word birth original)
  after_exact : after = Lifecycle.Observed.through (inputs.length + 1)

private def generateGrant (birth : Fin (inputs.length + 1))
    (grant : {grant // grant ∈ grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)}) :
    GrantContinuation bound inputs word :=
  ⟨birth, grant.val, grant.property, Lifecycle.Observed.through inputs.length, rfl,
    Lifecycle.Observed.through (inputs.length + 1), rfl⟩

def grantContinuations : List (GrantContinuation bound inputs word) :=
  (List.finRange (inputs.length + 1)).flatMap fun birth =>
    (grantsAt base scope (grantCurrent bound inputs birth.val) (grantWord bound inputs birth.val)).attach.map
      (generateGrant bound inputs word birth)

def GrantContinuation.actualRun (record : GrantContinuation bound inputs word) :
    (Lifecycle.Observed.process (base := base) (scope := scope)
      (currentAt := grantCurrent bound (nextInputs inputs word)) (wordAt := grantWord bound (nextInputs inputs word))
      (birth := record.birth.val) (grant := transportGrant bound inputs word record.birth record.original)).Run
      record.before.state record.after.state := by
  rw [record.before_exact, record.after_exact, ← transportGrant_entire_cut_state bound inputs word record.birth record.original]
  exact Lifecycle.Observed.fromActualCut inputs.length 1

end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Challenge.Cross
