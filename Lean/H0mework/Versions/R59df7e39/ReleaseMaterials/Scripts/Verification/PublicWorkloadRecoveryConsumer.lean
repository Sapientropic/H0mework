import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Runtime
import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Funding
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.PublicWorkloadRecoveryConsumer
open Distributed Distributed.Reaction Native.Future.Recovery
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
section Universal
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {old : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  {oldDepth : Nat} {target : Native.Authority.Sources old.base old.scope} {count : Nat}
  {word : List (Action old)} (receipt : Native.Future.Receipt old oldDepth target count word) (tariffPosition : Nat)

noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicWorkloadRecoveryConsumer.case001 : (produceWorkload tariffPosition receipt).read = produceWorkload tariffPosition receipt :=
  (produceWorkload tariffPosition receipt).read_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicWorkloadRecoveryConsumer.case002 : Walk.WorkloadMetered tariffPosition (produceWorkload tariffPosition receipt).walk :=
  (produceWorkload tariffPosition receipt).every_workload_search_has_its_own_two_prior_invoices tariffPosition rfl
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicWorkloadRecoveryConsumer.case003 :
    let made := produceWorkload tariffPosition receipt
    let active := made.activated
    made.Metered ∧ made.walk.Closed ∧ made.walk.finish.consumed ++ made.walk.finish.residual = word ∧
    made.native = Native.Authority.fullGenerate made.bound made.depth ∧
    HEq (made.facade.readoutAt active .recovery) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) :=
  (produceWorkload tariffPosition receipt).the_actual_root_consumes_recovery_all_original_positions_native_rows_and_its_own_next
end Universal

inductive Good where | fuel | service deriving DecidableEq
abbrev Port := Mandate.Source.Port
abbrev Raw := RawCurrent Bool Good (Mandate.State Bool Unit) Unit
abbrev Request := Institutions.Capitalism.Universal.Source.Program.Request Bool Good Port (Mandate.State Bool Unit) Unit

def task : PublicTaskSpec Bool Good :=
  ⟨[⟨false,[(.service,1)],.necessity⟩,⟨false,[(.service,1)],.maintenance⟩],0,5000,by decide +kernel⟩
def base : RawLaw Bool Good Port Unit Unit where
  technique := fun _ _ => ⟨[(.fuel,1)],[(.service,1)],[(.fuel,1/10)],[]⟩
  controller := fun _ _ => false
  allowed := fun _ port _ => decide (port = .resource)
  stockPort := fun _ _ _ => .resource
  revisionPort := fun _ => .challenge
  revisionCost := fun _ _ => [(.service,1)]
  settlementUnit := fun _ => .service
  settlementRate := fun _ => 1
  issuerPort := fun _ => .resource
  necessities := fun _ _ => [(.service,1)]
  mandatoryMaintenance := fun _ _ => [(.service,1)]
  duration := fun _ => 1
  policy := .opaque fun current request => match request.operation with
    | .produce actor => decide (current.stock actor .service < 1)
    | _ => true

def scope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Port) :=
  ⟨task,.service,.challenge,by decide,[(.service,1)]⟩
def law := Mandate.law base scope

def initial (fuel : ℚ) : Raw where
  stock := fun _ good => match good with | .fuel => fuel | .service => 10
  claims := fun _ _ _ => 0
  technology := ⟨(),0,none,none,none⟩
  clock := 0
  round := 0

def proposal (fuel : ℚ) := Mandate.request scope (initial fuel) false (.propose true)
def offered (fuel : ℚ) := law.step (initial fuel) (proposal fuel)
def acceptance (fuel : ℚ) := Mandate.request scope (offered fuel) true .accept
def issue : Request := ⟨true,[],.resource,[],.issue () true false 1⟩
def challenge : Request := ⟨false,[],.challenge,[.challenge],.present⟩
def prelude (fuel : ℚ) := [proposal fuel,acceptance fuel,challenge]
def quiet : Request := ⟨true,[],.resource,[],.present⟩
def foreign : Request := ⟨false,[],.resource,[],.produce false⟩

def fee : Request := ⟨true,[],.resource,[],.use true [(.fuel,1/1000)] .external⟩

def code (fuel : ℚ) : Code Bool Good Port (Mandate.State Bool Unit) Unit where
  law := law
  initial := initial fuel
  bootstrap := prelude fuel
  task := task
  actions := [foreign,quiet,fee]
  actionLimit := 1
  sites := 1
  signals := 1
  initialSignal := 0
  siteParty := fun _ => true
  readLocal := fun _ _ => 0
  historyAlphabet := []
  historyLimit := 0
  eventAlphabet := []
  eventLimit := 0
  eligible := fun _ => true
  parties := [false,true]
  goods := [.fuel,.service]
  instruments := [()]
  parties_cover := by intro p;cases p <;> simp
  goods_cover := by intro g;cases g <;> simp
  instruments_cover := by intro i;cases i;simp

def policy (fuel : ℚ) : (code fuel).Policy := fun _ _ => []
def source (fuel : ℚ) : Machine Bool Good Port (Mandate.State Bool Unit) Unit where
  code := code fuel
  reference := policy fuel
  reference_generated := by
    apply (code fuel).every_local_policy_is_enumerated
    intro key _
    exact (mem_words_iff _ _ _).mpr ⟨by simp [policy],by simp [policy]⟩
  history := [(code fuel).bootstrap]
  original := by
    simpa only [Code.publicPrefix,if_neg (show (code fuel).bootstrap ≠ [] from by intro empty;cases empty)] using
      (code fuel).public_prefix_is_an_actual_generated_history
  opponent := fun _ _ _ => none
  side := .original

def model (fuel : ℚ) : Native.Authority.Bound (Party := Bool) (Good := Good) (Port := Port)
    (Technology := Unit) (Instrument := Unit) := ⟨base,scope,source fuel,rfl,rfl⟩
def repay : Request := ⟨true,[],.resource,[],.settle () true false 1⟩
def exit (fuel : ℚ) := Mandate.request scope ((source fuel).actualExecution 2).before true .exit
def original (fuel : ℚ) := [exit fuel,issue,repay,quiet]
def drain (fuel : ℚ) : Request :=
  ⟨true,[],.resource,[],.use true [(.service,((source fuel).actualExecution 2).before.stock true .service)] .external⟩
def target (fuel : ℚ) : Native.Authority.Sources (model fuel).base (model fuel).scope :=
  ⟨(source fuel).withContinuation [[drain fuel]],rfl,rfl⟩

def check (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS "++label) else throw (IO.userError ("FAIL "++label))

def main : IO Unit := do
  match Native.Future.produce (model 4) 2 (target 4) 1 (original 4) with
  | .inl _ => throw (IO.userError "old source rejected its legal exit, issuance and repayment word")
  | .inr receipt =>
    let made := Native.Future.Recovery.produceWorkload 2 receipt
    let start := begin receipt
    check "the original output selects per-word workload pricing" (decide (made.workloadPosition = some 2))
    match made.walk with
    | .workloadAdvanced _ _ first _ later =>
      check "one-slot storage forces exit and new issuance before the next production round"
        (decide (first.endpoint.consumed.length = 2 ∧ first.endpoint.residual = [repay,quiet] ∧
          first.endpoint.before.claims () true false = 1))
      check "the first cached endpoint is the generated single-step result"
        (decide (first.endpoint.before.stock true .fuel = first.result.finish.before.stock true .fuel))
      match later with
      | .workloadAdvanced _ _ second _ tail =>
        check "the next actual principal regenerates its own paid comparison catalogue"
          (match second.result with | .searched .. => true | _ => false)
        check "the second round really settles the new principal and unchanged tail"
          (decide (second.endpoint.residual = [] ∧ second.endpoint.consumed = original 4 ∧
            second.endpoint.before.claims () true false = 0))
        check "empty residual terminates without a new bill or task attempt"
          (match tail with | .finished .. => true | _ => false)
      | _ => throw (IO.userError "second source-paid recovery round was not generated")
    | _ => throw (IO.userError "first source-paid recovery round was not generated")
    check "each released search has its own actual prior invoices"
      (decide (made.walk.searchBatches = 2 ∧ made.walk.paidBatches = 2))
    check "the original recovery root reads its complete recursive execution"
      (decide (made.read.walk.finish.consumed = original 4 ∧ made.read.walk.finish.residual = []))
    check "the installed native account contains the new Claim and its actual repayment"
      (decide (made.native.authority.joint.finance.current.slots.length = 1 ∧
        Financial.outstanding made.bound.source.input made.native.authority.joint.finance.current = 0))
    check "independent financial replay retains the complete original prefix"
      (Native.Coupling.verify start.source.val.code start.source.val.input made.bound.source.input
        (Financial.accountAt start.source.val.input (start.depth+1))
        (Financial.accountAt made.bound.source.input (start.depth+1)))
    check "the successful recursive path has no source funding failure"
      (Funding.ofWalk made.walk |>.isNone)
    let missing := Native.Future.Recovery.produceWorkload 99 receipt
    check "an unpriced service still attempts the unchanged old word"
      (decide ((missing.bound.source.actualExecution start.depth).submitted = start.attemptPath.output ∧
        missing.walk.searchBatches = 0))
    check "missing tariff retains its exact source-indexed failure"
      (match Funding.ofWalk missing.walk with
       | some (.workload _ 99 stage _) => match stage.result with | .unpriced .. => true | _ => false
       | _ => false)
    let explicit := Native.Future.Recovery.producePaid [] receipt
    check "explicit empty batch remains an actual override of workload pricing"
      (decide (explicit.tariff = some [] ∧ explicit.workloadPosition = none))
  match Native.Future.produce (model (2/1000)) 2 (target (2/1000)) 1 (original (2/1000)) with
  | .inl _ => throw (IO.userError "low fuel does not invalidate the old legal word")
  | .inr receipt =>
    let made := Native.Future.Recovery.produceWorkload 2 receipt
    check "comparison refusal preserves partial paid costs and the original outstanding word"
      (decide (made.walk.finish.before.stock true .fuel = 0 ∧
        made.walk.finish.residual = original (2/1000) ∧ made.walk.searchBatches = 0))
    check "refused comparison never releases an unpaid quality fold"
      (match Funding.ofWalk made.walk with
       | some (.workload _ _ stage _) => match stage.result with | .comparisonRefused .. => true | _ => false
       | _ => false)
    match made.walk with
    | .workloadStopped _ _ stage _ =>
      check "the exact post-invoice source still emits the original raw retry"
        (decide ((made.bound.source.actualExecution stage.endpoint.depth).submitted = stage.endpoint.attemptPath.output))
    | _ => throw (IO.userError "expected a stopped metering service with the old attempt retained")
  IO.println "WORKLOAD RECOVERY PASS"
end SaturationMonoid.ProcessGame.Society.PublicFunction.PublicWorkloadRecoveryConsumer

def main := SaturationMonoid.ProcessGame.Society.PublicFunction.PublicWorkloadRecoveryConsumer.main
