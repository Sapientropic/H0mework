import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.Step
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.RawLaw.ValiditySource
variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good]

/- Source operation leaves retain their scalar, policy, function-read and allocation internals.
   The finite consent, bundle, flow-sum and conjunction scans execute here. -/
inductive Event where
  | operand (kind : Fin 3)
  | signer (accepted : Bool)
  | policy (accepted : Bool)
  | access (allowed : Bool)
  | controller
  | consent (matched : Bool)
  | consentEnd
  | claim
  | rate
  | quantity (accepted : Bool)
  | bundleKey (matched : Bool)
  | bundleQuantity (matched : Bool)
  | bundleEnd (sameLength : Bool)
  | guard (accepted : Bool)
  | nonnegative (accepted : Bool)
  | flowKey (matched : Bool)
  | add (value : ℚ)
  | sumEnd
  | stock
  | affordable (accepted : Bool)
  | scanEnd (kind : Fin 4)
  | conjunction (kind : Fin 4) (accepted : Bool)
  | finish (accepted : Bool)
  deriving DecidableEq
private structure Part (α : Type) where
  value : α
  work : List Event

private def contains (party : Party) : List Party → Part Bool
  | [] => ⟨false,[.consentEnd]⟩
  | head::tail =>
      let matched := decide (party=head)
      let rest := contains party tail
      ⟨matched || rest.value,.consent matched::rest.work⟩
private theorem contains_exact (party : Party) (parties : List Party) :
    (contains party parties).value = true ↔ party ∈ parties := by
  induction parties with
  | nil => simp [contains]
  | cons head tail ih => simp [contains,ih]
private theorem contains_work (party : Party) (parties : List Party) :
    (contains party parties).work.length = parties.length+1 := by
  induction parties with
  | nil => rfl
  | cons head tail ih => simp [contains,ih]

private def bundleEqual : Bundle Good → Bundle Good → Part Bool
  | [],[] => ⟨true,[.bundleEnd true]⟩
  | [],_::_ | _::_,[] => ⟨false,[.bundleEnd false]⟩
  | a::left,b::right =>
      let key := decide (a.1=b.1)
      let quantity := decide (a.2=b.2)
      let rest := bundleEqual left right
      ⟨key && quantity && rest.value,[.bundleKey key,.bundleQuantity quantity]++rest.work⟩
private theorem bundle_exact (left right : Bundle Good) :
    (bundleEqual left right).value = true ↔ left=right := by
  induction left generalizing right with
  | nil => cases right <;> simp [bundleEqual]
  | cons a left ih =>
      cases right with
      | nil => simp [bundleEqual]
      | cons b right => simp [bundleEqual,ih,Prod.ext_iff,and_assoc]
private theorem bundle_work (left right : Bundle Good) :
    (bundleEqual left right).work.length ≤ 2*left.length+1 := by
  induction left generalizing right with
  | nil => cases right <;> simp [bundleEqual]
  | cons a left ih =>
      cases right with
      | nil => simp [bundleEqual]
      | cons b right =>
          have h := ih right
          simp only [bundleEqual,List.length_append,List.length_cons,List.length_nil]
          omega

private def scan {α : Type} (kind : Fin 4) (check : α → Part Bool) : List α → Part Bool
  | [] => ⟨true,[.scanEnd kind]⟩
  | head::tail =>
      let first := check head
      let rest := scan kind check tail
      let accepted := first.value && rest.value
      ⟨accepted,first.work++rest.work++[.conjunction kind accepted]⟩
private theorem scan_exact {α : Type} (kind : Fin 4) (check : α → Part Bool) (items : List α) :
    (scan kind check items).value = true ↔ ∀ x ∈ items,(check x).value = true := by
  induction items with
  | nil => simp [scan]
  | cons head tail ih => simp [scan,ih]
private theorem scan_work {α : Type} (kind : Fin 4) (check : α → Part Bool) (items : List α)
    (bound : Nat) (bounded : ∀ x ∈ items,(check x).work.length ≤ bound) :
    (scan kind check items).work.length ≤ (bound+1)*items.length+1 := by
  induction items with
  | nil => simp [scan]
  | cons head tail ih =>
      have first := bounded head (by simp)
      have rest := ih (by intro x hx;exact bounded x (by simp [hx]))
      simp only [scan,List.length_append,List.length_cons,List.length_nil,Nat.mul_succ]
      omega

private def signer (request : Request Party Good Port Technology Instrument) : Part Bool :=
  let accepted := match request.operation with
    | .issue _ issuer _ _ => decide (request.signer=issuer)
    | .assign _ _ sender _ _ => decide (request.signer=sender)
    | _ => true
  ⟨accepted,[.signer accepted]⟩
omit [DecidableEq Good] in
private theorem signer_exact (request : Request Party Good Port Technology Instrument) :
    (signer request).value = true ↔ SignerMatches request := by
  unfold signer SignerMatches
  cases request.operation <;> simp

private def access (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (port : Port) : Part Bool :=
  let allowed := law.allowed current.technology port request.signer
  if allowed then ⟨true,[.access true]⟩ else
    let owner := law.controller current.technology port
    let found := contains owner request.consents
    ⟨found.value,[.access false,.controller]++found.work⟩
omit [DecidableEq Good] in
private theorem access_exact (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (port : Port) :
    (access law current request port).value = true ↔
      law.allowed current.technology port request.signer = true ∨
        law.controller current.technology port ∈ request.consents := by
  unfold access
  dsimp only
  split <;> simp_all [contains_exact]
omit [DecidableEq Good] in
private theorem access_work (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) (port : Port) :
    (access law current request port).work.length ≤ request.consents.length+3 := by
  unfold access
  dsimp only
  split
  · simp
  · simp [contains_work]

def payloadLength (request : Request Party Good Port Technology Instrument) : Nat :=
  match request.operation with | .use _ goods _ => goods.length | _ => 0
private def guard (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Part Bool :=
  match request.operation with
  | .issue _ _ _ quantity =>
      let accepted := decide (0≤quantity)
      ⟨accepted,[.quantity accepted]⟩
  | .assign instrument issuer sender _ quantity =>
      let present := current.claims instrument issuer sender
      let nonnegative := decide (0≤quantity)
      let within := decide (quantity≤present)
      ⟨nonnegative && within,[.claim,.quantity nonnegative,.quantity within]⟩
  | .settle instrument debtor creditor quantity =>
      let present := current.claims instrument debtor creditor
      let rate := law.settlementRate instrument
      let nonnegative := decide (0≤quantity)
      let within := decide (quantity≤present)
      let positive := decide (0<rate)
      ⟨nonnegative && within && positive,[.claim,.rate,.quantity nonnegative,.quantity within,.quantity positive]⟩
  | .use bearer goods .necessity =>
      let same := bundleEqual goods (law.necessities current bearer)
      ⟨same.value,same.work++[.guard same.value]⟩
  | .use bearer goods .maintenance =>
      let same := bundleEqual goods (law.mandatoryMaintenance current bearer)
      ⟨same.value,same.work++[.guard same.value]⟩
  | _ => ⟨true,[.guard true]⟩
omit [DecidableEq Party] in
private theorem guard_exact (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (guard law current request).value = true ↔ law.ClaimGuard current request := by
  unfold guard ClaimGuard
  cases request.operation with
  | use bearer goods purpose => cases purpose <;> simp [bundle_exact]
  | _ => simp [and_assoc]
omit [DecidableEq Party] in
private theorem guard_work (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (guard law current request).work.length ≤ 2*payloadLength request+6 := by
  unfold guard payloadLength
  cases request.operation with
  | use bearer goods purpose =>
      have necessity := bundle_work goods (law.necessities current bearer)
      have maintenance := bundle_work goods (law.mandatoryMaintenance current bearer)
      cases purpose <;> simp only [List.length_append,List.length_cons,List.length_nil] <;> omega
  | _ => simp

private def nonnegative (item : (Party × Good) × ℚ) : Part Bool :=
  let accepted := decide (0≤item.2)
  ⟨accepted,[.nonnegative accepted]⟩
private def sum (party : Party) (good : Good) : Flow Party Good → Part ℚ
  | [] => ⟨0,[.sumEnd]⟩
  | item::tail =>
      let matched := decide (item.1=(party,good))
      let value := if matched then item.2 else 0
      let rest := sum party good tail
      ⟨value+rest.value,[.flowKey matched,.add value]++rest.work⟩
private theorem sum_exact (party : Party) (good : Good) (flow : Flow Party Good) :
    (sum party good flow).value = flowAt flow party good := by
  induction flow with
  | nil => rfl
  | cons item tail ih => simpa [sum,flowAt,amount] using congrArg (fun x => (if item.1=(party,good) then item.2 else 0)+x) ih
private theorem sum_work (party : Party) (good : Good) (flow : Flow Party Good) :
    (sum party good flow).work.length = 2*flow.length+1 := by
  induction flow with
  | nil => rfl
  | cons item tail ih => simp [sum,ih];omega
private def affordable (current : RawCurrent Party Good Technology Instrument) (debit : Flow Party Good)
    (item : (Party × Good) × ℚ) : Part Bool :=
  let quantity := sum item.1.1 item.1.2 debit
  let stock := current.stock item.1.1 item.1.2
  let accepted := decide (quantity.value≤stock)
  ⟨accepted,quantity.work++[.stock,.affordable accepted]⟩
private theorem affordable_exact (current : RawCurrent Party Good Technology Instrument) (debit : Flow Party Good)
    (item : (Party × Good) × ℚ) :
    (affordable current debit item).value = true ↔ flowAt debit item.1.1 item.1.2≤current.stock item.1.1 item.1.2 := by
  simp [affordable,sum_exact]
private theorem affordable_work (current : RawCurrent Party Good Technology Instrument) (debit : Flow Party Good)
    (item : (Party × Good) × ℚ) :
    (affordable current debit item).work.length ≤ 2*debit.length+3 := by
  simp [affordable,sum_work]

private def produce (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Part Bool :=
  let debit := law.debit current request
  let credit := law.credit current request
  let ports := law.requiredPorts current request
  let signed := signer request
  let policy := law.operationAllowed current request
  let accesses := scan 0 (access law current request) ports
  let guarded := guard law current request
  let incoming := scan 1 nonnegative debit
  let outgoing := scan 2 nonnegative credit
  let stocked := scan 3 (affordable current debit) debit
  let accepted := (signed.value && policy) && accesses.value && guarded.value && incoming.value && outgoing.value && stocked.value
  ⟨accepted,[.operand 0,.operand 1,.operand 2]++signed.work++[.policy policy]++accesses.work++guarded.work++
    incoming.work++outgoing.work++stocked.work++[.finish accepted]⟩
private theorem produce_exact (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (produce law current request).value = true ↔ law.Valid current request := by
  simp only [produce,Bool.and_eq_true,scan_exact,signer_exact,access_exact,guard_exact,affordable_exact,nonnegative,decide_eq_true_eq]
  simp only [Valid,NonnegativeBundle,and_assoc]

def budget (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Nat :=
  let debit := (law.debit current request).length
  (request.consents.length+4)*(law.requiredPorts current request).length +
    (2*debit+6)*debit + 2*(law.credit current request).length + 2*payloadLength request+20
private theorem produce_work (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (produce law current request).work.length ≤ budget law current request := by
  have signed : (signer request).work.length = 1 := by rfl
  have accesses := scan_work 0 (access law current request) (law.requiredPorts current request) (request.consents.length+3)
    (by intro port _;exact access_work law current request port)
  have guarded := guard_work law current request
  have incoming := scan_work 1 (nonnegative (Party := Party) (Good := Good)) (law.debit current request) 1 (by intro item _;rfl)
  have outgoing := scan_work 2 (nonnegative (Party := Party) (Good := Good)) (law.credit current request) 1 (by intro item _;rfl)
  have stocked := scan_work 3 (affordable current (law.debit current request)) (law.debit current request)
    (2*(law.debit current request).length+3) (by intro item _;exact affordable_work current _ item)
  simp only [produce,List.length_append,List.length_cons,List.length_nil]
  dsimp only [budget]
  nlinarith

structure Compilation (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) where
  private mk ::
  accepted : Bool
  work : List Event
  exact : accepted = true ↔ law.Valid current request
  private generated : accepted = (produce law current request).value ∧ work = (produce law current request).work

def compile (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) : Compilation law current request :=
  let made := produce law current request
  ⟨made.value,made.work,produce_exact law current request,⟨rfl,rfl⟩⟩
theorem work_bound (law : RawLaw Party Good Port Technology Instrument)
    (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (compile law current request).work.length ≤ budget law current request := produce_work law current request
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.Program.RawLaw.ValiditySource
