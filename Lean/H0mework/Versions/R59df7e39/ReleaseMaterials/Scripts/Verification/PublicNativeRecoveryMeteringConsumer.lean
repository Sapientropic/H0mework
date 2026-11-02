import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Future.Recovery.Metering.Runtime

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.PublicNativeRecoveryMeteringConsumer
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

noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicNativeRecoveryMeteringConsumer.case001 : (Metering.produce receipt tariffPosition).read = Metering.produce receipt tariffPosition :=
  (Metering.produce receipt tariffPosition).read_exact
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicNativeRecoveryMeteringConsumer.case002 (ordinal : Nat) (earlier : ordinal ≤ (begin receipt).depth+1) :
    Native.Coupling.Match (begin receipt).source.val.code (begin receipt).source.val.input
      (Metering.produce receipt tariffPosition).bound.source.input
      (Financial.accountAt (begin receipt).source.val.input ordinal)
      (Financial.accountAt (Metering.produce receipt tariffPosition).bound.source.input ordinal) :=
  (Metering.produce receipt tariffPosition).the_complete_original_financial_history_is_preserved ordinal earlier
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicNativeRecoveryMeteringConsumer.case003 :
    let made := Metering.produce receipt tariffPosition
    let active := made.activated
    made.result = Metering.run (begin receipt) tariffPosition ∧
    made.result.finish.consumed ++ made.result.finish.residual = word ∧
    made.native = Native.Authority.fullGenerate made.bound made.depth ∧
    HEq (made.facade.readoutAt active .recovery) (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      (active.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt active.current.visit.current) ∧
    active.tick.nextCurrent = made.facade.process.stateAt (made.facade.process.successor active.state) :=
  (Metering.produce receipt tariffPosition).the_actual_root_consumes_metering_all_original_positions_native_rows_and_its_own_next
noncomputable def _root_.H0mework.OriginalConsumerChecks.Versions.R59df7e39.ReleaseMaterials.Scripts.Verification.PublicNativeRecoveryMeteringConsumer.case004 (catalogue : List (List (Action old))) :
    Metering.requestVisits (begin receipt) [] +
      (catalogue.map (Metering.requestVisits (begin receipt))).sum + catalogue.length <
        Metering.comparisonUnits (begin receipt).residual catalogue :=
  Metering.every_evaluated_request_visit_is_reserved _ _
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
def prelude (fuel : ℚ) := [proposal fuel,acceptance fuel,issue,challenge]
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
def original (fuel : ℚ) := [repay,exit fuel,quiet]
def drain (fuel : ℚ) : Request :=
  ⟨true,[],.resource,[],.use true [(.service,((source fuel).actualExecution 2).before.stock true .service)] .external⟩
def target (fuel : ℚ) : Native.Authority.Sources (model fuel).base (model fuel).scope :=
  ⟨(source fuel).withContinuation [[drain fuel]],rfl,rfl⟩

def check (label : String) (ok : Bool) : IO Unit :=
  if ok then IO.println ("PASS "++label) else throw (IO.userError ("FAIL "++label))

def main : IO Unit := do
  match Native.Future.produce (model (23/10)) 2 (target (23/10)) 1 (original (23/10)) with
  | .inl _ => throw (IO.userError "old legal source unexpectedly refused")
  | .inr receipt =>
    let start := begin receipt
    let made := Metering.produce receipt 2
    check "explicit tariff selects the original registered positive own expense"
      (decide (Metering.quote start true 2 = some fee))
    check "the old task positions remain outstanding after construction payment"
      (decide ((Metering.charged start fee 1).residual = start.residual ∧
        (Metering.charged start fee 1).consumed = start.consumed))
    check "construction actually debits the payer before the search catalogue"
      (decide ((Metering.charged start fee 1).before.stock true .fuel = start.before.stock true .fuel-1/1000))
    let built := Metering.charged start fee 1
    let catalogue := Search.repairs built.model built.before true start.residual
    let units := Metering.comparisonUnits start.residual catalogue
    IO.println ("comparison reservation units "++toString units)
    check "nonempty comparison reservation precedes all quality scoring"
      (decide (0 < units ∧ (Metering.attempt built fee units).succeeded = true))
    check "both successful invoices release the actual original-word recovery"
      (match made.result with | .searched .. => true | _ => false)
    check "actual recovery consumes the unchanged old word and settles its original principal"
      (decide (made.result.finish.consumed = original (23/10) ∧ made.result.finish.residual = [] ∧
        made.result.finish.before.claims () true false = 0))
    check "the real fee and real production maintenance share the same material stock"
      (decide (made.result.finish.before.stock true .fuel = 23/10 - (units+1:Nat)/1000 - 22/10))
    check "the actual source contains construction comparison and recovery in order"
      (decide ((made.bound.source.actualExecution start.depth).submitted = [fee] ∧
        (made.bound.source.actualExecution (start.depth+1)).submitted = List.replicate units fee ∧
        (made.bound.source.actualExecution (start.depth+2)).submitted.length = 5))
    check "native accounting retains the original Claim and its actual paid status"
      (decide (made.native.authority.joint.finance.current.slots.length = 1 ∧
        Financial.outstanding made.bound.source.input made.native.authority.joint.finance.current = 0))
    check "the independent native prefix checker retains original births and archives"
      (Native.Coupling.verify start.source.val.code start.source.val.input made.bound.source.input
        (Financial.accountAt start.source.val.input (start.depth+1))
        (Financial.accountAt made.bound.source.input (start.depth+1)))
    check "the complete cost report includes the same positive fuel fee and maintenance"
      (decide ((made.reportFrom start.depth rfl).evaluation.value (.material (.debit true .fuel)) =
        (units+1:Nat)/1000 + 22/10))
    check "the installed root reads its own metered output and same actual report"
      (decide (made.read.result.finish.consumed = made.result.finish.consumed ∧
        (made.read.reportFrom 2 rfl).consumed = 3))
    check "an explicit nonfee registration cannot silently fall back to another quote"
      (match Metering.run start 1 with | .unpriced .. => true | _ => false)
    check "an out of range tariff gives a typed unpriced result"
      (match Metering.run start 99 with | .unpriced .. => true | _ => false)
  match Native.Future.produce (model (1/2000)) 2 (target (1/2000)) 1 (original (1/2000)) with
  | .inl _ => throw (IO.userError "old legal source unexpectedly refused")
  | .inr receipt =>
    let made := Metering.produce receipt 2
    check "construction refusal prevents catalogue release and preserves all old positions"
      (match made.result with
       | .constructionRefused .. => decide (made.result.finish.residual = original (1/2000) ∧
           made.result.finish.consumed = [] ∧ made.result.finish.count = (begin receipt).count+1)
       | _ => false)
  match Native.Future.produce (model (2/1000)) 2 (target (2/1000)) 1 (original (2/1000)) with
  | .inl _ => throw (IO.userError "old legal source unexpectedly refused")
  | .inr receipt =>
    let made := Metering.produce receipt 2
    check "partial comparison payment keeps actual paid expenses and its precise remaining old word"
      (match made.result with
       | .comparisonRefused .. => decide (made.result.finish.residual = original (2/1000) ∧
          made.result.finish.consumed = [] ∧ made.result.finish.before.stock true .fuel = 0 ∧
          made.result.finish.count = (begin receipt).count+2)
       | _ => false)

end SaturationMonoid.ProcessGame.Society.PublicFunction.PublicNativeRecoveryMeteringConsumer

def main : IO Unit := SaturationMonoid.ProcessGame.Society.PublicFunction.PublicNativeRecoveryMeteringConsumer.main
