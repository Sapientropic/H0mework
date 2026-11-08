import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Refeed

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root

structure Cached (Key Value : Type) where
  values : List (Key×Value)
  fallback : Key → Value

/-- A value carrier prevents eta expansion from rebuilding the table at every lookup. -/
@[noinline] def cache {Key Value : Type} [DecidableEq Key] (keys : List Key) (read : Key → Value) : Cached Key Value :=
  ⟨keys.map (fun key => (key,read key)),read⟩

def Cached.get {Key Value : Type} [DecidableEq Key] (stored : Cached Key Value) (key : Key) : Value :=
  match stored.values.find? (fun entry => entry.1==key) with
  | some entry => entry.2
  | none => stored.fallback key
instance {Key Value : Type} [DecidableEq Key] : CoeFun (Cached Key Value) (fun _ => Key → Value) := ⟨Cached.get⟩

theorem cache_exact {Key Value : Type} [DecidableEq Key] (keys : List Key) (read : Key → Value) (key : Key) :
    cache keys read key=read key := by
  unfold cache Cached.get
  dsimp only
  split
  · rename_i entry found
    have member := List.mem_of_find?_eq_some found
    obtain ⟨original,_,equal⟩ := List.mem_map.mp member
    subst entry
    have same : original=key := by simpa using List.find?_some found
    subst original
    rfl
  · rfl

def actors : List Actor := (List.range 4).map Sum.inl ++ (List.finRange 3).map Sum.inr
def goods : List Good := [.seed,.feed,.life,.spare,.waste,.energy,.labor]
def initialMemo (current : Current) : Current :=
  let stock := cache ((actors.flatMap fun actor => goods.map fun good => (actor,good)).filter
    fun key => key != (receiver,Good.feed)) (fun (p,g) => current.stock p g)
  let claims := cache ([Instrument.audit,.provider,.delivery].flatMap fun i =>
    actors.flatMap fun p => actors.map fun q => (i,p,q)) (fun (i,p,q) => current.claims i p q)
  {current with stock:=fun p g => stock (p,g),claims:=fun i p q => claims (i,p,q)}

theorem initialMemo_exact (current : Current) : initialMemo current=current := by
  apply RawCurrent.ext
  · funext actor good;exact cache_exact _ _ _
  · funext instrument debtor creditor;exact cache_exact _ _ _
  all_goals rfl


def memo (current : Current) : Current :=
  let stock := cache ([((.inl 0 : Actor),Good.feed)] ++
    (List.range 4).map (fun p => ((.inl p : Actor),Good.energy)) ++
    [((supplier : Actor),Good.feed),(supplier,Good.energy),(supplier,Good.labor)]) (fun (p,g) => current.stock p g)
  let claims := cache [(Instrument.delivery,supplier,receiver)] (fun (i,p,q) => current.claims i p q)
  {current with stock:=fun p g => stock (p,g),claims:=fun i p q => claims (i,p,q)}

theorem memo_exact (current : Current) : memo current=current := by
  apply RawCurrent.ext
  · funext actor good;exact cache_exact _ _ _
  · funext instrument debtor creditor;exact cache_exact _ _ _
  all_goals rfl

def cachedExecute (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) : Nat → List JointAction → ExecutionResult Actor Good Port Technology Instrument
  | _,[] => ⟨memo current,[]⟩
  | index,action::rest =>
    let before := memo current
    let remaining := cachedExecute scope ((law scope).step before action) (index+1) rest
    ⟨remaining.final,⟨index,before,action⟩::remaining.items⟩

theorem cachedExecute_exact (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (index : Nat) (actions : List JointAction) :
    cachedExecute scope current index actions=(law scope).execute current index actions := by
  induction actions generalizing current index with
  | nil => simp [cachedExecute,RawLaw.execute,memo_exact]
  | cons action rest ih => simp only [cachedExecute,memo_exact,ih,RawLaw.execute]

def cachedItems (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (actions : List JointAction) := (cachedExecute scope current 0 actions).items

theorem cachedItems_exact (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (actions : List JointAction) :
    cachedItems scope current actions=(law scope).rawItems current actions := by
  simp only [cachedItems,cachedExecute_exact,RawLaw.rawItems]

def cachedNext (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (actions : List JointAction) : Current :=
  memo { (cachedExecute scope current 0 actions).final with clock:=current.clock+1,round:=current.round+1 }

theorem cachedNext_exact (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (actions : List JointAction) : cachedNext scope current actions=(law scope).next current actions := by
  simp only [cachedNext,memo_exact,cachedExecute_exact,RawLaw.next]
  rfl

def attempt (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) : List (Current → JointAction) → List JointAction
  | [] => []
  | stage::rest => let action := stage before
      if (law scope).Valid before action then action::attempt scope (memo ((law scope).step before action)) rest else [action]

def allPaid (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (word : List JointAction) : Bool :=
  (cachedItems scope before word).all fun item => decide ((law scope).Valid item.before item.request)

inductive Mode where
  | normal | withholdFuel | denyProduction | wrongSupplier | refeed | denyRecycling
  deriving DecidableEq
def dispatch (current : Current) (mode : Mode) : List (Current → JointAction) :=
  let pending := current.claims .delivery supplier receiver
  let needsEnergy := current.stock supplier .energy<pending
  if (mode=.refeed ∨ mode=.denyRecycling) ∧ needsEnergy ∧ current.stock supplier .feed<1 then
    Refeed.stages current (mode=.denyRecycling) ++ [production,fun _ => shipment pending]
  else
  (if needsEnergy ∧ current.stock supplier .feed<1 then
    if mode=.withholdFuel then [] else [fun _ => feed] else []) ++
  (if needsEnergy then
    [fun state => if mode=.denyProduction then {production state with signer:=customer} else production state] else []) ++
  [fun _ => if mode=.wrongSupplier then {shipment pending with signer:=customer} else shipment pending]

def lot (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (mode : Mode) : List JointAction :=
  let start := if current.claims .delivery supplier receiver=0 then [obligation] else []
  let after := (cachedExecute scope current 0 start).final
  if allPaid scope current start then start++attempt scope after (dispatch after mode) else start

def fill (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (required : ℚ) (mode : Mode) : Nat → Current → List JointAction
  | 0,_ => []
  | n+1,current =>
    if required≤current.stock receiver .energy ∧ current.claims .delivery supplier receiver=0 then [] else
      let first := lot scope current mode
      if allPaid scope current first then
        first++fill scope required mode n (cachedExecute scope current 0 first).final
      else first

def members (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) (current : Current) : List Party :=
  (Delegation.members scope.task).eraseDups.filter fun actor => actor != 0 && current.technology.audit.holder != some actor
def replacement (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) (current : Current) : Party :=
  (members scope current).head?.getD 0
def revisionEnergy (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) : ℚ :=
  amount Good scope.revisionCost .energy
def requiredOwner (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) : ℚ := 2*revisionEnergy scope+2
def requiredCandidate (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) : ℚ := revisionEnergy scope+1
def topup (recipient : Party) (required : ℚ) (current : Current) : JointAction :=
  liftAudit current (transfer recipient (max 0 (required-current.stock (.inl recipient) .energy)))

def renewal (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (mode : Mode) : List JointAction :=
  let target := replacement scope current
  let need := max 0 (requiredOwner scope-current.stock customer .energy) +
    max 0 (requiredCandidate scope-current.stock (.inl target) .energy)
  let supply := fill scope need mode (⌈max 0 need/2⌉₊+1) current
  let after := (cachedExecute scope current 0 supply).final
  if allPaid scope current supply then supply++attempt scope after
    [topup 0 (requiredOwner scope),topup target (requiredCandidate scope),
     fun state => liftAudit state (Mandate.request scope (audit state) 0 .revoke),
     fun state => liftAudit state applicationFee]
  else supply

def serve (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (target : Party) (query : Query) (current : Current) : List JointAction :=
  attempt scope current
    ((if current.technology.audit.offered=some target then [] else
      [fun state => liftAudit state (Mandate.request scope (audit state) 0 (.propose target))]) ++
     [fun state => liftAudit state (Mandate.request scope (audit state) target .accept),
      fun state => liftAudit state (accessRequest target query),fun state => liftAudit state deliveryFee])

def read (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (actor : Party) (query : Query) (current : Current) : List JointAction :=
  attempt scope current [fun state => liftAudit state (accessRequest actor query),fun state => liftAudit state deliveryFee]

def word (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (target : Party) (query : Query) (mode : Mode) (current : Current) : List JointAction :=
  if scope.task.deadline<current.clock then renewal scope current mode
  else if current.technology.audit.holder.isNone then serve scope target query current
  else read scope (current.technology.audit.holder.getD target) query current

def input (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (target : Party) (query : Query) (mode : Mode) (current : Current) :
    ProgrammeSource.Input Actor Good Port Technology Instrument :=
  { law:=law scope,initial:=current,instructions:=[],emission?:=some (word scope target query mode) }

theorem attempt_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (stages : List (Current → JointAction)) (safe : ∀ stage∈stages,∀ current,Historical (stage current))
    (current : Current) : ∀ action∈attempt scope current stages,Historical action := by
  induction stages generalizing current with
  | nil => simp [attempt]
  | cons stage rest ih =>
    simp only [attempt]
    split
    · intro action member
      rcases List.mem_cons.mp member with rfl | tail
      · exact safe stage (by simp) current
      · exact ih (fun stage member => safe stage (List.mem_cons_of_mem _ member)) _ action tail
    · intro action member
      have equal := List.mem_singleton.mp member
      subst action
      exact safe stage (by simp) current

theorem dispatch_historical (current : Current) (mode : Mode) :
    ∀ stage∈dispatch current mode,∀ before,Historical (stage before) := by
  unfold dispatch
  dsimp only
  split
  · intro stage member
    rcases List.mem_append.mp member with original | rest
    · exact Refeed.stages_historical _ _ stage original
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at rest
      rcases rest with rfl | rfl
      all_goals simp [Historical,production,liftProvider,liftProviderOperation,shipment]
  · repeat' split
    all_goals simp [Historical,feed,shipment,production,liftProvider,liftProviderOperation]

theorem lot_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (mode : Mode) : ∀ action∈lot scope current mode,Historical action := by
  unfold lot
  simp only [cachedExecute_exact]
  by_cases empty : current.claims .delivery supplier receiver=0
  · simp only [if_pos empty]
    split
    · intro action member
      rcases List.mem_append.mp member with first | second
      · simp only [List.mem_singleton] at first;subst action;rfl
      · exact attempt_historical scope _ (dispatch_historical _ mode) _ action second
    · intro action member
      simp only [List.mem_singleton] at member;subst action;rfl
  · simp only [if_neg empty]
    change ∀ action∈ (if allPaid scope current [] then
      []++attempt scope ((law scope).execute current 0 []).final
        (dispatch ((law scope).execute current 0 []).final mode) else []),Historical action
    simp only [allPaid,cachedItems_exact,cachedExecute_exact,RawLaw.rawItems,RawLaw.execute,List.all_nil,ite_true,List.nil_append]
    exact attempt_historical scope _ (dispatch_historical _ mode) _

theorem fill_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (required : ℚ) (mode : Mode) (count : Nat) (current : Current) :
    ∀ action∈fill scope required mode count current,Historical action := by
  induction count generalizing current with
  | zero => simp [fill]
  | succ count ih =>
    simp only [fill]
    split
    · simp
    · split
      · intro action member
        rcases List.mem_append.mp member with first | second
        · exact lot_historical _ _ _ action first
        · exact ih _ action second
      · exact lot_historical _ _ _

theorem renewal_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (mode : Mode) : ∀ action∈renewal scope current mode,Historical action := by
  unfold renewal
  dsimp only
  split
  · intro action member
    rcases List.mem_append.mp member with first | second
    · exact fill_historical _ _ _ _ _ action first
    · apply attempt_historical scope _ ?_ _ action second
      intro stage member before
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;>
        trivial
  · exact fill_historical _ _ _ _ _

theorem serve_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (target : Party) (query : Query) (current : Current) : ∀ action∈serve scope target query current,Historical action := by
  unfold serve
  apply attempt_historical scope _ ?_ current
  intro stage member before
  split at member
  · simp only [List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> trivial
  · simp only [List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> trivial

theorem word_historical (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (target : Party) (query : Query) (mode : Mode) (current : Current) :
    ∀ action∈word scope target query mode current,Historical action := by
  unfold word
  split
  · exact renewal_historical _ _ _
  · split
    · exact serve_historical _ _ _ _
    · apply attempt_historical scope _ ?_ current
      intro stage member before
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> trivial

private abbrev operationDecidableEq : DecidableEq (Operation Actor Good Technology Instrument) := by
  intro left right
  cases left <;> cases right <;> (try simp only [Operation.produce.injEq,Operation.transfer.injEq,Operation.use.injEq,
    Operation.issue.injEq,Operation.assign.injEq,Operation.settle.injEq,Operation.revise.injEq,reduceCtorEq]) <;> infer_instance
private abbrev actionDecidableEq : DecidableEq JointAction := by
  letI := operationDecidableEq
  intro left right
  cases left;cases right
  simp only [Institutions.Capitalism.Universal.Source.Program.Request.mk.injEq]
  infer_instance
attribute [local instance] actionDecidableEq

inductive RefusalKind where
  | fuelAbsent | laborAbsent | sourceRejected
  deriving DecidableEq

def refusalKind (before : Current) (request : JointAction) : RefusalKind :=
  if request=feed ∧ before.stock customer .feed<1 then .fuelAbsent
  else if request=production before ∧ before.stock supplier .labor<1 then .laborAbsent
  else .sourceRejected

structure Refusal (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) where
  private mk ::
  item : {item // item∈cachedItems scope before actions}
  rejected : ¬ (law scope).Valid item.val.before item.val.request
  kind : RefusalKind
  kindActual : kind=refusalKind item.val.before item.val.request

def refusal (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) : Option (Refusal scope before actions) :=
  (cachedItems scope before actions).attach.findSome? fun item =>
    if h : (law scope).Valid item.val.before item.val.request then none
    else some ⟨item,h,refusalKind item.val.before item.val.request,rfl⟩

structure Opening (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) where
  private mk ::
  item : {item // item∈cachedItems scope before actions}
  request : item.val.request=liftAudit item.val.before applicationFee
  paid : (law scope).Valid item.val.before item.val.request
  quiet : Quiet (audit item.val.before)
  expired : scope.task.deadline < item.val.before.clock

def opening (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) : Option (Opening scope before actions) :=
  if scope.task.deadline<before.clock then
    (cachedItems scope before actions).attach.findSome? fun item =>
      if h : item.val.request=liftAudit item.val.before applicationFee ∧
          (law scope).Valid item.val.before item.val.request ∧ Quiet (audit item.val.before) ∧
          scope.task.deadline < item.val.before.clock then
        some ⟨item,h.1,h.2.1,h.2.2.1,h.2.2.2⟩ else none
  else none

theorem Opening.the_original_fee_is_actually_admitted
    {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)}
    {before : Current} {actions : List JointAction} (receipt : Opening scope before actions) :
    (Mandate.law energyBase scope).Valid (audit receipt.item.val.before) applicationFee := by
  apply audit_admission scope receipt.item.val.before applicationFee
  rw [←receipt.request]
  exact receipt.paid

structure Packet (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) (actor : Party) (query : Query) where
  private mk ::
  access : {item // item∈cachedItems scope before actions}
  request : access.val.request=liftAudit access.val.before (accessRequest actor query)
  paid : (law scope).Valid access.val.before access.val.request
  fee : {item // item∈cachedItems scope before actions}
  feeRequest : fee.val.request=liftAudit fee.val.before deliveryFee
  feePaid : (law scope).Valid fee.val.before fee.val.request
  consecutive : fee.val.index=access.val.index+1

def packets (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (before : Current) (actions : List JointAction) (actor : Party) (query : Query) :
    List (Packet scope before actions actor query) :=
  (cachedItems scope before actions).attach.flatMap fun access =>
    (cachedItems scope before actions).attach.filterMap fun fee =>
      if h : access.val.request=liftAudit access.val.before (accessRequest actor query) ∧
          (law scope).Valid access.val.before access.val.request ∧
          fee.val.request=liftAudit fee.val.before deliveryFee ∧ (law scope).Valid fee.val.before fee.val.request ∧
          fee.val.index=access.val.index+1 then
        some ⟨access,h.1,h.2.1,fee,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩ else none

theorem Packet.the_original_access_is_actually_admitted
    {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)}
    {before : Current} {actions : List JointAction} {actor : Party} {query : Query}
    (receipt : Packet scope before actions actor query) :
    (Mandate.law energyBase scope).Valid (audit receipt.access.val.before) (accessRequest actor query) := by
  apply audit_admission scope receipt.access.val.before (accessRequest actor query)
  rw [←receipt.request]
  exact receipt.paid

def Packet.evidence {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)}
    {before : Current} {actions : List JointAction} {actor : Party} {query : Query}
    (_receipt : Packet scope before actions actor query) : List (Slot×Evidence) :=
  (selected query).map fun slot => (slot,restrict (fields query) (originalEvidence slot))

theorem Packet.every_slice_keeps_its_original_service
    {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)}
    {before : Current} {actions : List JointAction} {actor : Party} {query : Query}
    (receipt : Packet scope before actions actor query) (slot : Slot) (evidence : Evidence)
    (member : (slot,evidence)∈receipt.evidence) : Origin slot evidence := by
  obtain ⟨original,_,same⟩ := List.mem_map.mp member
  rcases Prod.mk.inj same with ⟨rfl,rfl⟩
  exact restrict_has_origin _ _ _ (original_evidence_has_origin _)

open private Continuation.Window.mk from H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Continuation

structure Record where
  source : ProgrammeSource.Input Actor Good Port Technology Instrument
  ordinal : Nat
def Record.before (record : Record) := ProgrammeSource.rawCurrent record.source (ProgrammeHistory.visitAt record.source record.ordinal).current
def Record.after (record : Record) := ProgrammeSource.rawCurrent record.source (ProgrammeHistory.visitAt record.source (record.ordinal+1)).current

structure Session (plan : Plan) where
  private mk ::
  origin : Handoff.Seed plan
  received : List Handoff.Request
  window : Continuation.Window plan
  current : Current
  target : Party
  history : List Record
  finance : (audit current).claims=(EnergyRenewal.before plan).claims
  providerFinance : (provider current).claims=providerInitial.claims

def start {plan : Plan} (seed : Handoff.Seed plan) (received : List Handoff.Request) : Session plan :=
  let old := seed.current received (seed.ordinal+received.length+1)
  ⟨seed,received,seed.window,initialMemo (join old providerInitial),
    (seed.candidates old).head?.getD 0,[],by
      rw [initialMemo_exact,join_keeps_the_entire_original_current]
      exact seed.preserves_every_claim _ _,by
      rw [initialMemo_exact,join_keeps_the_entire_provider_current]⟩

theorem start_is_the_original_consumed_handoff_and_the_actual_provider
    {plan : Plan} (seed : Handoff.Seed plan) (received : List Handoff.Request) :
    audit (start seed received).current=ProgrammeSource.rawCurrent (seed.input received)
      (ProgrammeHistory.visitAt (seed.input received) (seed.ordinal+received.length+1)).current ∧
    provider (start seed received).current=providerInitial := by
  simp only [start,initialMemo_exact,join_keeps_the_entire_original_current,join_keeps_the_entire_provider_current]
  exact ⟨(seed.current_is_own_root_current _ _).symm,trivial⟩

variable {plan : Plan}
def Session.input (session : Session plan) (query : Query) (mode : Mode) :=
  Supply.input session.window.scope session.target query mode session.current
def Session.prepared (session : Session plan) := (law session.window.scope).next session.current []
def Session.actions (session : Session plan) (query : Query) (mode : Mode) :=
  word session.window.scope session.target query mode session.prepared
def Session.after (session : Session plan) (query : Query) (mode : Mode) :=
  cachedNext session.window.scope session.prepared (session.actions query mode)

theorem Session.before_is_own_root_current (session : Session plan) (query : Query) (mode : Mode) :
    ProgrammeSource.rawCurrent (session.input query mode) (ProgrammeHistory.visitAt (session.input query mode) 1).current=session.prepared := rfl
theorem Session.after_is_own_root_next (session : Session plan) (query : Query) (mode : Mode) :
    ProgrammeSource.rawCurrent (session.input query mode) (ProgrammeHistory.visitAt (session.input query mode) 2).current=session.after query mode := by
  unfold Session.after
  rw [cachedNext_exact]
  rfl

theorem Session.after_keeps_historical_claims (session : Session plan) (query : Query) (mode : Mode)
    (instrument : Instrument) (old : instrument≠.delivery) :
    (session.after query mode).claims instrument=session.current.claims instrument := by
  unfold Session.after
  rw [cachedNext_exact]
  change ((law session.window.scope).execute session.prepared 0 (session.actions query mode)).final.claims instrument=_
  calc
    _ = session.prepared.claims instrument :=
      historical_claims_execute session.window.scope session.prepared (session.actions query mode) 0
        (word_historical _ _ _ _ _) instrument old
    _ = _ := rfl

theorem Session.after_finance (session : Session plan) (query : Query) (mode : Mode) :
    (audit (session.after query mode)).claims=(EnergyRenewal.before plan).claims := by
  calc
    _ = (audit session.current).claims := by
      funext instrument debtor creditor
      exact congrFun (congrFun (session.after_keeps_historical_claims query mode .audit (by decide)) (.inl debtor)) (.inl creditor)
    _ = _ := session.finance

theorem Session.after_provider_finance (session : Session plan) (query : Query) (mode : Mode) :
    (provider (session.after query mode)).claims=providerInitial.claims := by
  calc
    _ = (provider session.current).claims := by
      funext instrument debtor creditor
      exact congrFun (congrFun (session.after_keeps_historical_claims query mode .provider (by decide)) (.inr debtor)) (.inr creditor)
    _ = _ := session.providerFinance

def Session.opening (session : Session plan) (query : Query) (mode : Mode) :=
  Supply.opening session.window.scope session.prepared (session.actions query mode)

def Session.nextWindow (session : Session plan) (query : Query) (mode : Mode) : Option (Continuation.Window plan) :=
  match session.opening query mode with
  | none => none
  | some _ => if (session.after query mode).claims .delivery supplier receiver=0 then
      let post := audit (session.after query mode)
      let task : PublicTaskSpec Party Good := ⟨energySlots,post.clock+1,post.clock+1+energySlots.length,by decide +kernel⟩
      some (Continuation.Window.mk session.window.origin task rfl post (session.after_finance query mode) session.window.ancestry)
    else none

def Session.actor (session : Session plan) := session.prepared.technology.audit.holder.getD session.target
def Session.packets (session : Session plan) (query : Query) (mode : Mode) :=
  Supply.packets session.window.scope session.prepared (session.actions query mode) session.actor query

abbrev providerDepth := Protocol.SymbolicAuthentication.MaterialRoundSource.depth providerOrigin.model providerOrigin.cut

/-- Existing debts remain on their original source accounts. Only new delivery debts belong to the joint input. -/
structure OriginalAccounts (session : Session plan) where
  provider : Distributed.Reaction.Native.Authority.FullDisposition providerOrigin.model providerDepth
  providerActual : provider=Distributed.Reaction.Native.Authority.fullGenerate providerOrigin.model providerDepth
  archive : List Protocol.SymbolicAuthentication.RoundEpisodeSource.Archive
  archiveActual : archive=providerOrigin.archive
  legacy : (Financial.process (session.origin.input session.received)).GeneratedState
  legacyActual : legacy=Financial.accountAt (session.origin.input session.received)
    (session.origin.ordinal+session.received.length+1)

def originalAccounts (session : Session plan) : OriginalAccounts session :=
  ⟨Distributed.Reaction.Native.Authority.fullGenerate providerOrigin.model providerDepth,rfl,
   providerOrigin.archive,rfl,Financial.accountAt (session.origin.input session.received)
     (session.origin.ordinal+session.received.length+1),rfl⟩

theorem original_provider_slots_keep_their_actual_births (session : Session plan) :
    (originalAccounts session).provider.authority.joint.finance=
      Financial.accountAt providerOrigin.model.source.input (providerDepth+2) :=
  (originalAccounts session).provider.authority.joint.finance_exact

theorem original_provider_is_consumed_on_its_own_native_root (session : Session plan) :
    Protocol.SymbolicAuthentication.RoundEpisodeConsumer.NativeConsumed providerOrigin.model providerDepth
      (originalAccounts session).provider :=
  Protocol.SymbolicAuthentication.RoundEpisodeConsumer.native_generated_consumed _ _

namespace Runtime
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
variable (session : Session plan) (query : Query) (mode : Mode)
def beforeAt (ordinal : Nat) := ProgrammeSource.rawCurrent (session.input query mode)
  (ProgrammeHistory.visitAt (session.input query mode) ordinal).current
def actionsAt (ordinal : Nat) := ProgrammeSource.rawEvent (session.input query mode)
  (ProgrammeHistory.visitAt (session.input query mode) ordinal).current

structure Result (ordinal : Nat) where
  originals : Unit → OriginalAccounts session
  originalsActual : originals=fun _ => originalAccounts session
  newFinance : Unit → (Financial.process (session.input query mode)).GeneratedState
  newFinanceActual : newFinance=fun _ => Financial.accountAt (session.input query mode) (ordinal+1)
  blocked : Option (Refusal session.window.scope (beforeAt session query mode ordinal) (actionsAt session query mode ordinal))
  blockedActual : blocked=refusal session.window.scope (beforeAt session query mode ordinal) (actionsAt session query mode ordinal)
  current : Current
  actualCurrent : current=ProgrammeSource.rawCurrent (session.input query mode)
    (ProgrammeHistory.visitAt (session.input query mode) (ordinal+1)).current
  window : Option (Continuation.Window plan)
  actualWindow : window=if ordinal=1 then session.nextWindow query mode else none
  delivery : List (Packet session.window.scope (beforeAt session query mode ordinal)
    (actionsAt session query mode ordinal)
    ((beforeAt session query mode ordinal).technology.audit.holder.getD session.target) query)
  actualDelivery : delivery=packets session.window.scope (beforeAt session query mode ordinal)
    (actionsAt session query mode ordinal)
    ((beforeAt session query mode ordinal).technology.audit.holder.getD session.target) query

def result (ordinal : Nat) : Result session query mode ordinal :=
  ⟨(fun _ => originalAccounts session),rfl,
   (fun _ => Financial.accountAt (session.input query mode) (ordinal+1)),rfl,
   refusal session.window.scope (beforeAt session query mode ordinal) (actionsAt session query mode ordinal),rfl,
   cachedNext session.window.scope (beforeAt session query mode ordinal) (actionsAt session query mode ordinal),by
     rw [cachedNext_exact]
     exact (ProgrammeSource.actual_raw_next (session.input query mode)
       (ProgrammeHistory.visitAt (session.input query mode) ordinal).current).symm,
   (if ordinal=1 then session.nextWindow query mode else none),rfl,
   packets session.window.scope (beforeAt session query mode ordinal) (actionsAt session query mode ordinal)
     ((beforeAt session query mode ordinal).technology.audit.holder.getD session.target) query,rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (session.input query mode)).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (ordinal : Nat) → current=(ProgrammeHistory.visitAt (session.input query mode) ordinal).current →
      Result session query mode ordinal
  project := fun _ {_} _ _ ordinal _ => result session query mode ordinal

def root := (ProgrammeLiving.livingRoot (session.input query mode)).withProjectionCoface (projectionLaw session query mode)
def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (session.input query mode)) :=
  ⟨ProgrammeSource.V (session.input query mode),root session query mode,
   ProgrammeHistory.temporalVisit (session.input query mode) ordinal⟩
def process : SourceNativeLivingRootProcess (ProgrammeSource.N (session.input query mode)) where
  State := Nat
  stateAt := stateAt session query mode
  stateAt_injective := by
    intro first second same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (session.input query mode)) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    exact ProgrammeHistory.visit_current_injective (session.input query mode) (eq_of_heq (Sigma.mk.inj labels).2)
  initial := 0
  successorAt := fun n => ⟨n+1,rfl,HEq.rfl⟩

inductive Face where | execution | supply
def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (session.input query mode)) where
  process := process session query mode
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .execution => ProgrammeLiving.projectionLaw (session.input query mode)
    | .supply => projectionLaw session query mode
  installationAt := by
    intro state face
    cases face
    · exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
        (ProgrammeLiving.authoritySource (session.input query mode)) (projectionLaw session query mode)
    · exact SourceNativeProjectionLaw.InstallationAt.componentCoface
        (ProgrammeLiving.authoritySource (session.input query mode)) (projectionLaw session query mode)
  projectionAt := fun _ face => match face with | .execution => .execution | .supply => ()
def activated (ordinal : Nat) := (facade session query mode).seed.advance ordinal
theorem activated_state (ordinal : Nat) : (activated session query mode ordinal).state=ordinal := by
  induction ordinal with | zero => rfl | succ n ih => exact congrArg Nat.succ ih
def consume (ordinal : Nat) : Result session query mode ordinal :=
  match (facade session query mode).readoutAt (activated session query mode ordinal) .supply with
  | .inl ⟨_,payload⟩ => payload ordinal (by
      change (ProgrammeHistory.visitAt (session.input query mode) (activated session query mode ordinal).state).current=_
      rw [activated_state])
  | .inr impossible => nomatch impossible

theorem same_occurrence_whole_ledger_and_own_next (ordinal : Nat) :
    (activated session query mode ordinal).tick.generated.occurrence=
      (activated session query mode ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.emitted
        (activated session query mode ordinal).current.visit.current ∧
    HEq (activated session query mode ordinal).tick.generated.wholeLedgerWriteBack
      ((activated session query mode ordinal).current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt
        (activated session query mode ordinal).current.visit.current) ∧
    HEq ((facade session query mode).readoutAt (activated session query mode ordinal) .supply)
      ((activated session query mode ordinal).tick.generated.projectionOutcome
        (((facade session query mode).installationAt (activated session query mode ordinal) .supply).embed
          ((facade session query mode).projectionAt (activated session query mode ordinal) .supply))) ∧
    (activated session query mode ordinal).tick.nextCurrent=
      (process session query mode).stateAt ((process session query mode).successor (activated session query mode ordinal).state) :=
  ((facade session query mode).readoutAt_factorizes (activated session query mode ordinal) .supply).2
end Runtime

def Session.next (session : Session plan) (query : Query) (mode : Mode) : Session plan :=
  let generated := Runtime.consume session query mode 1
  let next := generated.window
  let target := if next.isSome then replacement session.window.scope session.prepared else session.target
  ⟨session.origin,session.received,next.getD session.window,memo generated.current,target,
   session.history++[⟨session.input query mode,1⟩],by
     rw [memo_exact,generated.actualCurrent,session.after_is_own_root_next]
     exact session.after_finance query mode,by
     rw [memo_exact,generated.actualCurrent,session.after_is_own_root_next]
     exact session.after_provider_finance query mode⟩

theorem Session.next_is_the_same_actual_generated_next (session : Session plan) (query : Query) (mode : Mode) :
    (session.next query mode).current=ProgrammeSource.rawCurrent (session.input query mode)
      (ProgrammeHistory.visitAt (session.input query mode) 2).current := by
  change memo (Runtime.consume session query mode 1).current=_
  rw [memo_exact]
  exact (Runtime.consume session query mode 1).actualCurrent

def run (initial : Session plan) (requests : Nat → Query×Mode) : Nat → Session plan
  | 0 => initial
  | n+1 => (run initial requests n).next (requests n).1 (requests n).2

theorem every_recursive_step_keeps_both_native_finances (initial : Session plan) (requests : Nat → Query×Mode) (n : Nat) :
    (audit (run initial requests n).current).claims=(EnergyRenewal.before plan).claims ∧
    (provider (run initial requests n).current).claims=providerInitial.claims :=
  ⟨(run initial requests n).finance,(run initial requests n).providerFinance⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
