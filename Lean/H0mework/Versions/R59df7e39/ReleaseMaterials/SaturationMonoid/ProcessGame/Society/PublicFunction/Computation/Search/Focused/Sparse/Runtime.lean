import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Scan

set_option autoImplicit false
set_option maxRecDepth 65536
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Runtime
open Distributed Distributed.Reaction Distributed.Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol
open Distributed.Recall.Information.Agency.Protocol.Continuation
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Budget.Programme.Debt Budget.Programme.Debt.Information Budget.Programme.Debt.Information.Inquiry
open Budget.Programme.Debt.Information.Inquiry.Replay.Suffix.Window.Whole

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (domain : List (Cursor model.source.code))
  (original : Distributed.Recall.Information.Agency.Protocol.Rule model.source.code)
  (reference : Program model.source.code (horizon domain))
  (worker : Fin model.source.code.sites)
  (quote : Charge.Quote (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))

  (quotas : List Nat)

variable (point : View (code := model.source.code)) (rival : Opponent model.source.code)
abbrev execution := Sparse.trace model domain original reference worker quote quotas point rival
abbrev final := (execution model domain original reference worker quote quotas point rival).final.point
abbrev source := (final model domain original reference worker quote quotas point rival).source
abbrev endAt := arrival (final model domain original reference worker quote quotas point rival)
abbrev bound := Replanning.native model (final model domain original reference worker quote quotas point rival)
abbrev Snapshot := Sparse.Scan model domain original reference worker quote quotas rival point none quotas ×
  Option (Sparse.Finished model domain original reference worker quote quotas)
def available (ordinal : Nat) : Option (Snapshot model domain original reference worker quote quotas point rival) :=
  let scanned := execution model domain original reference worker quote quotas point rival
  if arrival scanned.final.point ≤ ordinal then
    some (scanned,Sparse.close model domain original reference worker quote quotas point rival scanned)
  else none

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (source model domain original reference worker quote quotas point rival).input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ => (ordinal : Nat) →
    current = (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival).input ordinal).current →
      Option (Snapshot model domain original reference worker quote quotas point rival)
  project := fun _ {_} _ _ ordinal _ =>
    available model domain original reference worker quote quotas point rival ordinal

def root := (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival)).withProjectionCoface
  (projectionLaw model domain original reference worker quote quotas point rival)

theorem original_programme_root_is_preserved :
    (root model domain original reference worker quote quotas point rival).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (source model domain original reference worker quote quotas point rival).input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker quote quotas point rival).input) :=
  ⟨ProgrammeSource.V (source model domain original reference worker quote quotas point rival).input,root model domain original reference worker quote quotas point rival,
    ProgrammeHistory.temporalVisit (source model domain original reference worker quote quotas point rival).input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N (source model domain original reference worker quote quotas point rival).input) where
  State := Nat
  stateAt := stateAt model domain original reference worker quote quotas point rival
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (source model domain original reference worker quote quotas point rival).input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective _ (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : Native.AuthorityRuntime.Face)
  | search

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (source model domain original reference worker quote quotas point rival).input) where
  process := process model domain original reference worker quote quotas point rival
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).componentAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).seed previous
    | .search => projectionLaw model domain original reference worker quote quotas point rival
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
        exact ((Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).installationAt
          (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
            (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival)).toAuthoritativeRoot.source
            (projectionLaw model domain original reference worker quote quotas point rival))
    | search =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (Native.AuthorityRuntime.root (bound model domain original reference worker quote quotas point rival)).toAuthoritativeRoot.source
          (projectionLaw model domain original reference worker quote quotas point rival)
  projectionAt := fun _ face => match face with
    | .previous previous => (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).projectionAt
        (Native.AuthorityRuntime.facade (bound model domain original reference worker quote quotas point rival)).seed previous
    | .search => ()

abbrev activated (ordinal : Nat) := (facade model domain original reference worker quote quotas point rival).seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated model domain original reference worker quote quotas point rival ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

def read (ordinal : Nat) : Option (Snapshot model domain original reference worker quote quotas point rival) :=
  match (facade model domain original reference worker quote quotas point rival).readoutAt (activated model domain original reference worker quote quotas point rival ordinal) .search with
  | .inl actual => actual.2 ordinal (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival).input
        (activated model domain original reference worker quote quotas point rival ordinal).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem read_is_the_arrived_source_generated_outcome (ordinal : Nat) :
    read model domain original reference worker quote quotas point rival ordinal =
      available model domain original reference worker quote quotas point rival ordinal := rfl

def nativeRead (depth : Nat) : Native.Authority.Disposition (bound model domain original reference worker quote quotas point rival) depth :=
  match (facade model domain original reference worker quote quotas point rival).readoutAt (activated model domain original reference worker quote quotas point rival (depth+1))
      (.previous .responsibilities) with
  | .inl actual => actual.2 depth (by
      change (ProgrammeHistory.visitAt (source model domain original reference worker quote quotas point rival).input
        (activated model domain original reference worker quote quotas point rival (depth+1)).state).current = _
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem the_same_facade_reads_the_entire_native_financial_account (depth : Nat) :
    (nativeRead model domain original reference worker quote quotas point rival depth).joint.finance =
      Financial.accountAt (source model domain original reference worker quote quotas point rival).input (depth+2) := by
  rw [(nativeRead model domain original reference worker quote quotas point rival depth).joint_exact]
  exact (Native.generate (source model domain original reference worker quote quotas point rival) depth).finance_exact

theorem search_payment_and_next_factor_through_one_actual_root (ordinal : Nat) :
    let current := activated model domain original reference worker quote quotas point rival ordinal
    HEq ((facade model domain original reference worker quote quotas point rival).readoutAt current .search)
      (current.tick.generated.projectionOutcome (.component ())) ∧
    HEq current.tick.generated.wholeLedgerWriteBack
      (current.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current.current.visit.current) ∧
    current.tick.nextCurrent = (activated model domain original reference worker quote quotas point rival (ordinal+1)).current := by
  have rooted := (facade model domain original reference worker quote quotas point rival).readoutAt_factorizes
    (activated model domain original reference worker quote quotas point rival ordinal) .search
  exact ⟨rooted.2.2.2.1,rooted.2.2.1,rfl⟩


end SaturationMonoid.ProcessGame.Society.PublicFunction.Computation.Search.Focused.Sparse.Runtime
