import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Source

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Action old)}

inductive Pricing (Request : Type) where
  | unpriced
  | batch (fee : List Request)
  | workload (position : Nat)
  deriving DecidableEq

def Pricing.ofTariff {Request : Type} : Option (List Request) → Pricing Request
  | none => .unpriced
  | some fee => .batch fee

instance {Request : Type} : Coe (Option (List Request)) (Pricing Request) := ⟨Pricing.ofTariff⟩

def Pricing.execute (pricing : Pricing (Action old)) (cursor : Cursor old oldDepth word) : Walk cursor :=
  match pricing with
  | .unpriced => Recovery.execute cursor
  | .batch fee => executePaid fee cursor
  | .workload position => executeWorkload position cursor

structure Output (original : Receipt old oldDepth target count word) where
  private mk ::
  pricing : Pricing (Action old)
  walk : Walk (begin original)
  generated : walk = pricing.execute (begin original)
  native : Authority.FullDisposition walk.finish.model (walk.finish.depth-1)
  native_exact : native = Authority.fullGenerate walk.finish.model (walk.finish.depth-1)

/-- The only input is the prior generated transport receipt, never a repair plan. -/
def produce (original : Receipt old oldDepth target count word) : Output original :=
  ⟨.unpriced,execute (begin original),rfl,Authority.fullGenerate _ _,rfl⟩

/-- The source supplies a registered batch request, never a paid receipt or a selected repair. -/
def producePaid (fee : List (Action old)) (original : Receipt old oldDepth target count word) : Output original :=
  ⟨.batch fee,executePaid fee (begin original),rfl,Authority.fullGenerate _ _,rfl⟩

/-- A source action slot prices each word's own construction and comparison workload. -/
def produceWorkload (position : Nat) (original : Receipt old oldDepth target count word) : Output original :=
  ⟨.workload position,executeWorkload position (begin original),rfl,Authority.fullGenerate _ _,rfl⟩

def produceWith (pricing : Pricing (Action old)) (original : Receipt old oldDepth target count word) : Output original :=
  ⟨pricing,pricing.execute (begin original),rfl,Authority.fullGenerate _ _,rfl⟩

namespace Output
variable {original : Receipt old oldDepth target count word} (made : Output original)

abbrev bound := made.walk.finish.model
abbrev depth := made.walk.finish.depth-1

/-- Whole-batch quotes retain their original meaning, including the explicit empty quote. -/
def tariff : Option (List (Action old)) := match made.pricing with
  | .batch fee => some fee
  | _ => none

def workloadPosition : Option Nat := match made.pricing with
  | .workload position => some position
  | _ => none

def Metered : Prop := match made.pricing with
  | .unpriced => True
  | .batch fee => Walk.Metered fee made.walk
  | .workload position => Walk.WorkloadMetered position made.walk

theorem metered : made.Metered := by
  unfold Metered
  cases priced : made.pricing with
  | unpriced => trivial
  | batch fee =>
      have generated := made.generated
      rw [priced] at generated
      rw [generated]
      exact every_source_priced_search_is_actually_prepaid _ _
  | workload position =>
      have generated := made.generated
      rw [priced] at generated
      rw [generated]
      exact every_workload_search_is_generated_after_its_actual_invoices _ _

theorem every_priced_search_has_its_own_paid_batch (fee : List (Action old)) (priced : made.tariff = some fee) :
    made.walk.searchBatches = made.walk.paidBatches := by
  have ready := made.metered
  cases mode : made.pricing with
  | unpriced => simp only [tariff,mode] at priced;cases priced
  | batch actual =>
      simp only [tariff,mode,Option.some.injEq] at priced
      simp only [Metered,mode] at ready
      exact ready.every_search_has_its_own_preceding_paid_batch
  | workload position => simp only [tariff,mode] at priced;cases priced

theorem every_workload_search_has_its_own_two_prior_invoices (position : Nat)
    (priced : made.workloadPosition = some position) :
    Walk.WorkloadMetered position made.walk := by
  have ready := made.metered
  cases mode : made.pricing with
  | unpriced => simp only [workloadPosition,mode] at priced;cases priced
  | batch _ => simp only [workloadPosition,mode] at priced;cases priced
  | workload actual =>
      simp only [workloadPosition,mode,Option.some.injEq] at priced
      subst actual
      simpa only [Metered,mode] using ready

theorem the_complete_original_financial_history_is_preserved (ordinal : Nat)
    (earlier : ordinal ≤ (begin original).depth+1) :
    Coupling.Match (begin original).source.val.code (begin original).source.val.input made.bound.source.input
      (Financial.accountAt (begin original).source.val.input ordinal)
      (Financial.accountAt made.bound.source.input ordinal) := made.walk.complete_financial_prefix ordinal earlier

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource made.bound.source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    current = (ProgrammeHistory.visitAt made.bound.source.input (made.depth+1)).current → Output original
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

def read : Output original := match made.facade.readoutAt made.activated .recovery with
  | .inl actual => actual.2 (by
      change (ProgrammeHistory.visitAt made.bound.source.input made.activated.state).current = _
      rw [made.activated_state];rfl)
  | .inr impossible => nomatch impossible

theorem read_exact : made.read = made := rfl

theorem the_actual_root_consumes_recovery_all_original_positions_native_rows_and_its_own_next :
    let active := made.activated
    made.Metered ∧ made.walk.Closed ∧ made.walk.finish.consumed ++ made.walk.finish.residual = word ∧
    made.native = Authority.fullGenerate made.bound made.depth ∧
    HEq (made.facade.readoutAt active .recovery) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) := by
  have rooted := made.facade.readoutAt_factorizes made.activated .recovery
  exact ⟨made.metered,made.walk.closed,made.walk.finish.split,made.native_exact,rooted.2.2.2.1,rooted.2.2.1,rooted.2.2.2.2⟩
end Output

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery
