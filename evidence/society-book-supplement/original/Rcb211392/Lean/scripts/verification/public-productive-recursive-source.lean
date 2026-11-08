import SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Future.Runtime

open Lean
open SaturationMonoid.ProcessGame.Society
open PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open Productive.Synthesis
open Settlement
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

private def fullStateJson (current : Current) : Json :=
  let visible := Privacy.Wire.stateJson current
  visible.setObjVal! "stock" (toJson ((actors.flatMap fun actor => goods.map fun good =>
    Json.arr #[Privacy.Wire.actorJson actor,toJson (Privacy.Wire.goodName good),toJson (toString (current.stock actor good))])))

private def accountJson (account : Finance.Account) : Json :=
  Json.arr ((account.current.slots.map fun slot =>
    let claim := Financial.Family.slotClaim Finance.sources slot
    Json.mkObj [
      ("instrument",toJson (Privacy.Wire.instrumentName claim.2.instrument)),
      ("debtor",Privacy.Wire.actorJson claim.2.debtor),
      ("holder",Privacy.Wire.actorJson claim.2.holder),
      ("quantity",toJson (toString claim.2.quantity)),
      ("instruction",toJson claim.2.instruction.index),
      ("birthRound",toJson claim.2.instruction.before.round),
      ("birthClock",toJson (toString claim.2.instruction.before.clock)),
      ("request",Privacy.Wire.actionJson claim.2.instruction.request),
      ("balance",toJson (toString (Financial.Family.slotBalance Finance.sources slot claim.2.holder))),
      ("fulfilled",toJson (match slot with
        | .terminal archive => match archive.receipt with | .fulfilled _ => true | _ => false
        | .live _ => false)),
      ("payment",match slot with
        | .terminal archive => match archive.sourceEvent with
          | .review _ receipt _ cap => Json.mkObj [
            ("request",Privacy.Wire.actionJson receipt.instruction.request),
            ("round",toJson receipt.instruction.before.round),("index",toJson receipt.instruction.index),
            ("quantity",toJson (toString receipt.quantity)),("cap",toJson (toString cap)),
            ("payment",toJson (match receipt.kind with | .payment => true | .assignment => false))]
          | .birth _ => Json.null
        | .live _ => Json.null),
      ("terminal",toJson (match slot with | .terminal _ => true | .live _ => false))]).toArray)

private def nativeAccountJson {P G Port T : Type} [DecidableEq P] [DecidableEq G] [DecidableEq Port]
    (sources : ProgrammeSource.Input P G Port T Unit → ProgrammeSource.Input P G Port T Unit)
    (actor : P → Json) (account : (Financial.Family.process sources).GeneratedState) : Json :=
  toJson (account.current.slots.map fun slot =>
    let claim := Financial.Family.slotClaim sources slot
    Json.mkObj [
      ("debtor",actor claim.2.debtor),("holder",actor claim.2.holder),
      ("quantity",toJson (toString claim.2.quantity)),("instruction",toJson claim.2.instruction.index),
      ("birthClock",toJson (toString claim.2.instruction.before.clock)),
      ("birthRound",toJson claim.2.instruction.before.round),
      ("balance",toJson (toString (Financial.Family.slotBalance sources slot claim.2.holder))),
      ("terminal",toJson (match slot with | .terminal _ => true | .live _ => false)),
      ("fulfilled",toJson (match slot with
        | .terminal archive => match archive.receipt with | .fulfilled _ => true | _ => false
        | .live _ => false)),
      ("payment",match slot with
        | .terminal archive => match archive.sourceEvent with
          | .review _ receipt _ cap => Json.mkObj [
            ("debtor",actor claim.2.debtor),("holder",actor receipt.sender),
            ("index",toJson receipt.instruction.index),("round",toJson receipt.instruction.before.round),
            ("clock",toJson (toString receipt.instruction.before.clock)),
            ("quantity",toJson (toString receipt.quantity)),("cap",toJson (toString cap)),
            ("payment",toJson (match receipt.kind with | .payment => true | .assignment => false))]
          | .birth _ => Json.null
        | .live _ => Json.null)])

private def taskJson (task : PublicFunction.PublicTaskSpec Actor PublicFunction.Productivity.Cell.Good) : Json := Json.mkObj [
  ("earliest",toJson (toString task.earliest)),("deadline",toJson (toString task.deadline)),
  ("slots",toJson (task.slots.map fun slot => Json.mkObj [
    ("bearer",Privacy.Wire.actorJson slot.bearer),("goods",Privacy.Wire.bundleJson slot.goods),
    ("purpose",toJson (Privacy.Wire.useName slot.purpose))]))]

@[noinline] private def roleJson (seed : Stream.Resume.Seed) : Json :=
  match seed.role with
  | none => Json.null
  | some role =>
    let claim := Financial.Family.slotClaim Finance.sources role.slot.val
    Json.mkObj [("debtor",Privacy.Wire.actorJson claim.2.debtor),("holder",Privacy.Wire.actorJson claim.2.holder),
      ("quantity",toJson (toString claim.2.quantity)),("instruction",toJson claim.2.instruction.index),
      ("birthClock",toJson (toString claim.2.instruction.before.clock)),("birthRound",toJson claim.2.instruction.before.round)]

private def windowJson (role : Json) {basis : Settlement.State} (window : Requests.Window basis) : Json :=
  Json.mkObj [
    ("id",toJson window.id),("task",taskJson window.task),("nonce",toJson window.submission.nonce),
    ("requestBeforeClock",toJson (toString window.before.clock)),("requestBeforeRound",toJson window.before.round),
    ("registrationIndex",toJson window.receipt.registration.val.index),
    ("registration",Privacy.Wire.actionJson window.receipt.registration.val.request),
    ("feeIndex",toJson window.receipt.fee.val.index),("fee",Privacy.Wire.actionJson window.receipt.fee.val.request),
    ("feeBeforeClock",toJson (toString window.receipt.fee.val.before.clock)),
    ("role",role)]

private def eventName : Stream.Event → String
  | .bootstrap => "bootstrap" | .idle => "idle" | .refusedRequest => "refused-request" | .admitted => "admitted"
  | .waiting => "waiting" | .pastDue => "past-due" | .served => "served" | .refusedService => "refused-service"

private def protocolJson (role : Json) {basis : Settlement.State} (protocol : Stream.Protocol basis) : Json := Json.mkObj [
  ("received",toJson protocol.received),("pending",protocol.pending.map (windowJson role) |>.getD Json.null),
  ("expired",toJson (protocol.expired.map fun due => Json.mkObj [
    ("id",toJson due.debt.id),("task",taskJson due.debt.task),
    ("observedClock",toJson (toString due.observed.clock)),("ordinal",toJson due.ordinal),
    ("inherited",toJson (match due.debt with | .inherited => true | _ => false))])),
  ("completed",toJson (protocol.completed.map fun completion => Json.mkObj [
    ("window",windowJson role completion.window),("beforeClock",toJson (toString completion.before.clock)),
    ("fees",toJson (Stream.search basis completion.window completion.before).fees)])),
  ("event",toJson (eventName protocol.event))]


open Stream Stream.Resume Stream.Resume.Regen Stream.Resume.Regen.Recovery

private def routeName : Route → String
  | .local .ordinary => "ordinary"
  | .local .recycle => "recycle"
  | .local .factory => "factory"
  | .reserve .ordinary => "reserve+ordinary"
  | .reserve .recycle => "reserve+recycle"
  | .reserve .factory => "reserve+factory"

private def branchName (seed : Seed) (requests : Requests.Source) (ordinal : Nat)
    (frame : Frame seed.basis) : String :=
  match selection seed (permissionAt seed requests .normal ordinal frame) frame with
  | .original => "original"
  | .repay choice => routeName choice.val
  | .blocked _ => "blocked"

private def tickJson {basis : Settlement.State} (role : Json) (scope : Productive.Scope)
    (ordinal sourceOrdinal : Nat) (before : Frame basis) (actions : List JointAction)
    (after : Frame basis) (branch : String) : Json := Json.mkObj [
  ("ordinal",toJson ordinal),("sourceOrdinal",toJson sourceOrdinal),("branch",toJson branch),
  ("before",fullStateJson before.raw),("protocolBefore",protocolJson role before.protocol),
  ("rows",toJson (((Productive.law scope).rawItems before.raw actions).map fun item =>
    Json.mkObj [("index",toJson item.index),("before",fullStateJson item.before),
      ("request",Privacy.Wire.actionJson item.request),
      ("accepted",toJson (decide ((Productive.law scope).Valid item.before item.request))),
      ("debit",Privacy.Wire.flowJson ((Productive.law scope).actualDebit item.before item.request)),
      ("credit",Privacy.Wire.flowJson ((Productive.law scope).actualCredit item.before item.request))])),
  ("after",fullStateJson after.raw),("protocolAfter",protocolJson role after.protocol)]

/-- The continuing requester supplies its current round, not future endpoints. -/
private def registeredRequests : Requests.Source := fun _ round => some (Requests.signed round)

def main : IO Unit := do
  let request ← IO.ofExcept (Json.parse (←(←IO.getStdin).getLine))
  let decoded ← IO.ofExcept (PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Privacy.Wire.decode request)
  let original ← IO.ofExcept (Privacy.Source.initial false decoded)
  let generated := Production.run (Productive.Synthesis.start Production.code original) 2
  let basis := Settlement.Root.next .provider
    (Settlement.Root.next .audit (Settlement.Root.next .provider (Settlement.Root.next .audit (Settlement.start generated))))
  let seed := Resume.start basis
  let role := roleJson seed
  let inherited := Regen.inherit seed (Requests.finite 18) .normal 47
  IO.eprintln "RECURSIVE SOURCE: recovering the original native clock122 account"
  let native122 := Regen.Runtime.consume inherited (Requests.finite 20) .original 4
  let cut := Recovery.fromRecorded inherited (Requests.finite 20) .original 4 native122
  let snapshot := Future.capture cut 4
  let .inl _ := Future.opening snapshot | throw (IO.userError "original clock126 account refuses admission")
  unless decide (snapshot.frame.raw.clock = 126 ∧ snapshot.frame.protocol.received = 20 ∧
      snapshot.frame.protocol.completed.length = 20 ∧ snapshot.frame.protocol.expired.length = 1) do
    throw (IO.userError "wrong actual predecessor")
  IO.eprintln "RECURSIVE SOURCE: complete clock126 frame and native account recovered"
  let mut regenBefore := inherited.result.frame
  let mut regenerationPrefix : Array Json := #[]
  for offset in [:5] do
    let actions := Regen.word seed (Requests.finite 20) .original (offset + 1) regenBefore
    let after := Regen.step seed (Requests.finite 20) .original (offset + 1) regenBefore
    regenerationPrefix := regenerationPrefix.push
      (tickJson role basis.origin.scope offset (offset + 1) regenBefore actions after "regeneration")
    regenBefore := after
  let mut prior := native122.frame
  let mut priorTicks : Array Json := #[]
  for offset in [:4] do
    let actions := Recovery.admittedWord cut offset prior
    let after := Recovery.admittedStep cut offset prior
    priorTicks := priorTicks.push (tickJson role basis.origin.scope offset (6 + offset) prior actions after
      (branchName seed (Requests.finite 20) (6 + offset) prior))
    prior := after
  IO.print ((Json.mkObj [
    ("schema",toJson "productive-recursive/v1"),("scope",toJson "original-base-local-private-audit"),
    ("predecessor117",fullStateJson inherited.result.frame.raw),
    ("predecessor117Protocol",protocolJson role inherited.result.frame.protocol),
    ("predecessor117Account",accountJson inherited.result.account),
    ("regenerationPrefix",Json.arr regenerationPrefix),
    ("before122",fullStateJson native122.frame.raw),("protocol122",protocolJson role native122.frame.protocol),
    ("account122",accountJson native122.account),("prefix",Json.arr priorTicks),
    ("initial",fullStateJson snapshot.frame.raw),("protocolInitial",protocolJson role snapshot.frame.protocol),
    ("accountBefore",accountJson snapshot.account),("oldTaskId",toJson basis.taskId),("oldTask",taskJson basis.task),
    ("nativeAudit",nativeAccountJson auditSources toJson seed.original.legacy.auditAccount),
    ("nativeProvider",nativeAccountJson providerSources (fun p=>toJson p.val) seed.original.legacy.providerAccount)]).compress.dropEnd 1 |>.toString)
  IO.print ",\"ticks\":["
  let mut current := snapshot.frame
  for offset in [:24] do
    let actions := Future.word snapshot registeredRequests .original .normal offset current
    let after := Future.step snapshot registeredRequests .original .normal offset current
    if offset > 0 then IO.print ","
    IO.print ((tickJson role basis.origin.scope offset (10 + offset) current actions after
      (branchName seed registeredRequests (10 + offset) current)).compress)
    IO.eprintln s!"RECURSIVE SOURCE: emitted actual successor {offset + 1}, clock {after.raw.clock}"
    current := after
  IO.print "]"
  IO.eprintln "RECURSIVE SOURCE: consuming the same native execution coface"
  let published := Future.Runtime.consume snapshot registeredRequests .original .normal 23
  IO.print ",\"publishedFinal\":"
  IO.print ((fullStateJson published.frame.raw).compress)
  IO.print ",\"publishedProtocol\":"
  IO.print ((protocolJson role published.frame.protocol).compress)
  IO.print ",\"accountAfter\":"
  IO.print ((accountJson published.account).compress)
  IO.println "}"
  IO.eprintln "RECURSIVE SOURCE: complete recursive transcript exported"
