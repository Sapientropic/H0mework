import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Assessment

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Action old)}

structure Output (original : Receipt old oldDepth target count word) (tariffPosition : Nat) where
  private mk ::
  result : Result (begin original) tariffPosition
  generated : result = run (begin original) tariffPosition
  native : Authority.FullDisposition result.finish.model (result.finish.depth-1)
  native_exact : native = Authority.fullGenerate result.finish.model (result.finish.depth-1)

/-- The configured source tariff is interpreted on the prior receipt's actual next. -/
def produce (original : Receipt old oldDepth target count word) (tariffPosition : Nat) : Output original tariffPosition :=
  ⟨run (begin original) tariffPosition,rfl,Authority.fullGenerate _ _,rfl⟩

namespace Output
variable {original : Receipt old oldDepth target count word} {tariffPosition : Nat} (made : Output original tariffPosition)

abbrev bound := made.result.finish.model
abbrev depth := made.result.finish.depth-1

theorem the_complete_original_financial_history_is_preserved (ordinal : Nat)
    (earlier : ordinal ≤ (begin original).depth+1) :
    Coupling.Match (begin original).source.val.code (begin original).source.val.input made.bound.source.input
      (Financial.accountAt (begin original).source.val.input ordinal)
      (Financial.accountAt made.bound.source.input ordinal) := made.result.complete_financial_prefix ordinal earlier

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource made.bound.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt made.bound.source.input (made.depth+1)).current → Output original tariffPosition
  project := fun _ {_} _ _ _own => made

def root := (AuthorityRuntime.root made.bound).withProjectionCoface made.projectionLaw

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N made.bound.source.input) :=
  ⟨ProgrammeSource.V _,made.root,ProgrammeHistory.temporalVisit _ ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N made.bound.source.input) where
  State := Nat
  stateAt := made.stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N made.bound.source.input) =>
        (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt made.bound.source.input first).current =
        (ProgrammeHistory.visitAt made.bound.source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective _ currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal+1,rfl,HEq.rfl⟩

inductive Face where
  | previous (face : AuthorityRuntime.Face)
  | recovery

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N made.bound.source.input) where
  process := made.process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade made.bound).componentAt (AuthorityRuntime.facade made.bound).seed previous
    | .recovery => made.projectionLaw
  installationAt := by
    intro _ face
    cases face with
    | previous previous =>
      exact ((AuthorityRuntime.facade made.bound).installationAt (AuthorityRuntime.facade made.bound).seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (AuthorityRuntime.root made.bound).toAuthoritativeRoot.source made.projectionLaw)
    | recovery =>
      exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (AuthorityRuntime.root made.bound).toAuthoritativeRoot.source made.projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => (AuthorityRuntime.facade made.bound).projectionAt (AuthorityRuntime.facade made.bound).seed previous
    | .recovery => ()

abbrev activated := made.facade.seed.advance (made.depth+1)

theorem activated_state : made.activated.state = made.depth+1 := by
  have all (n : Nat) : (made.facade.seed.advance n).state = n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg Nat.succ ih
  exact all _

def read : Output original tariffPosition := match made.facade.readoutAt made.activated .recovery with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt made.bound.source.input made.activated.state).current = _
      rw [made.activated_state];rfl)
  | .inr impossible => nomatch impossible

theorem read_exact : made.read = made := rfl

def reportFrom (start : Nat) (sameCode : target.val.code = old.source.code) : Assessment.Report old :=
  ⟨made.result.finish.consumed.length,
    (made.result.preserves.code.trans sameCode) ▸
      Window.evaluate made.bound start (made.result.finish.depth-start)⟩

theorem the_report_is_read_from_its_actual_installed_output
    (start : Nat) (sameCode : target.val.code = old.source.code) :
    made.read.reportFrom start sameCode = made.reportFrom start sameCode := by
  rw [made.read_exact]

theorem the_paid_interval_reaches_its_actual_next (start : Nat) (earlier : start ≤ (begin original).depth) :
    Window.finish start (made.result.finish.depth-start) = made.result.finish.depth+1 ∧
      ∀ ordinal, (begin original).depth ≤ ordinal → ordinal < made.result.finish.depth →
        start ≤ ordinal ∧ ordinal < start+(made.result.finish.depth-start) := by
  have ordered := made.result.preserves.depth
  dsimp only [Window.finish]
  constructor
  · omega
  · intro ordinal afterStart beforeFinish
    constructor <;> omega

theorem the_actual_root_consumes_metering_all_original_positions_native_rows_and_its_own_next :
    let active := made.activated
    made.result = run (begin original) tariffPosition ∧ made.result.finish.consumed ++ made.result.finish.residual = word ∧
    made.native = Authority.fullGenerate made.bound made.depth ∧
    HEq (made.facade.readoutAt active .recovery) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .recovery
  exact ⟨made.generated,made.result.finish.split,made.native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Output

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering
