import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.SourceFamily

/-! A local title-transfer rule extends an existing production law.  Every
old request is preserved literally after erasing the new title coordinate;
the new possible revision changes authority, never stocks or old claims.
The port and possible counterparties are raw source code, not a C verdict. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.LawExtension

open Program
universe u
variable {Party Good Port Technology Instrument : Type u}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

abbrev Title (Party Technology : Type u) := Technology × Option Party

def liftOperation : Operation Party Good Technology Instrument →
    Operation Party Good (Title Party Technology) Instrument
  | .produce actor => .produce actor
  | .transfer sender recipient goods => .transfer sender recipient goods
  | .use bearer goods kind => .use bearer goods kind
  | .issue code issuer beneficiary quantity => .issue code issuer beneficiary quantity
  | .assign code issuer sender recipient quantity => .assign code issuer sender recipient quantity
  | .settle code debtor creditor quantity => .settle code debtor creditor quantity
  | .revise actor technology => .revise actor (technology, none)
  | .present => .present

def eraseOperation : Operation Party Good (Title Party Technology) Instrument →
    Operation Party Good Technology Instrument
  | .produce actor => .produce actor
  | .transfer sender recipient goods => .transfer sender recipient goods
  | .use bearer goods kind => .use bearer goods kind
  | .issue code issuer beneficiary quantity => .issue code issuer beneficiary quantity
  | .assign code issuer sender recipient quantity => .assign code issuer sender recipient quantity
  | .settle code debtor creditor quantity => .settle code debtor creditor quantity
  | .revise actor technology => .revise actor technology.1
  | .present => .present

def liftRequest (request : Request Party Good Port Technology Instrument) :
    Request Party Good Port (Title Party Technology) Instrument :=
  ⟨request.signer, request.consents, request.purpose, request.gates, liftOperation request.operation⟩

def eraseRequest (request : Request Party Good Port (Title Party Technology) Instrument) :
    Request Party Good Port Technology Instrument :=
  ⟨request.signer, request.consents, request.purpose, request.gates, eraseOperation request.operation⟩

def liftCurrent (current : RawCurrent Party Good Technology Instrument) :
    RawCurrent Party Good (Title Party Technology) Instrument :=
  ⟨current.stock, current.claims, (current.technology, none), current.clock, current.round⟩

def eraseCurrent (current : RawCurrent Party Good (Title Party Technology) Instrument) :
    RawCurrent Party Good Technology Instrument :=
  ⟨current.stock, current.claims, current.technology.1, current.clock, current.round⟩

def liftItem (item : ExecutionItem Party Good Port Technology Instrument) :
    ExecutionItem Party Good Port (Title Party Technology) Instrument :=
  ⟨item.index, liftCurrent item.before, liftRequest item.request⟩

variable (base : RawLaw Party Good Port Technology Instrument) (assetPort : Port)

def controller (technology : Title Party Technology) (port : Port) : Party :=
  if port = assetPort then technology.2.getD (base.controller technology.1 port)
  else base.controller technology.1 port

def law : RawLaw Party Good Port (Title Party Technology) Instrument where
  technique := fun technology => base.technique technology.1
  controller := controller base assetPort
  allowed := fun technology port actor =>
    if port = assetPort then match technology.2 with
      | none => base.allowed technology.1 port actor
      | some holder => decide (holder = actor)
    else base.allowed technology.1 port actor
  stockPort := fun technology => base.stockPort technology.1
  revisionPort := fun technology => base.revisionPort technology.1
  revisionCost := fun old target =>
    if old.2 = target.2 then base.revisionCost old.1 target.1 else []
  settlementUnit := base.settlementUnit
  settlementRate := base.settlementRate
  issuerPort := base.issuerPort
  necessities := fun current => base.necessities (eraseCurrent current)
  mandatoryMaintenance := fun current => base.mandatoryMaintenance (eraseCurrent current)
  policy := .opaque (fun current request => match request.operation with
    | .revise _ target =>
        if current.technology.2 = target.2 then
          base.operationAllowed (eraseCurrent current) (eraseRequest request)
        else decide (target.1 = current.technology.1 ∧
          request.signer = controller base assetPort current.technology assetPort ∧
          request.consents = [] ∧ target.2.isSome = true)
    | _ => base.operationAllowed (eraseCurrent current) (eraseRequest request))
  duration := fun current => base.duration (eraseCurrent current)

/-- The same finite source action grammar can be used at every generated
current.  It is checked locally and contains no successful future. -/
def localAttempts (counterparties : List Party)
    (current : RawCurrent Party Good (Title Party Technology) Instrument) :
    RawEvent Party Good Port (Title Party Technology) Instrument :=
  counterparties.map (fun nextHolder =>
    let holder := controller base assetPort current.technology assetPort
    ⟨holder, [], assetPort, [assetPort], .revise holder (current.technology.1, some nextHolder)⟩)

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Technology] [DecidableEq Instrument] in
@[simp] theorem erase_liftCurrent (current : RawCurrent Party Good Technology Instrument) :
    eraseCurrent (liftCurrent current) = current := rfl

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
@[simp] theorem erase_liftRequest (request : Request Party Good Port Technology Instrument) :
    eraseRequest (liftRequest request) = request := by
  cases request with
  | mk signer consents purpose gates operation => cases operation <;> rfl

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem controller_original (technology : Technology) (port : Port) :
    (law base assetPort).controller (technology, none) port = base.controller technology port := by
  simp [law, controller]

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem allowed_original (technology : Technology) (port : Port) (actor : Party) :
    (law base assetPort).allowed (technology, none) port actor = base.allowed technology port actor := by
  simp [law]

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem debit_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).debit (liftCurrent current) (liftRequest request) = base.debit current request := by
  cases request with
  | mk signer consents purpose gates operation =>
      cases operation <;> simp [RawLaw.debit, liftRequest, liftOperation, liftCurrent, law]

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem credit_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).credit (liftCurrent current) (liftRequest request) = base.credit current request := by
  cases request with
  | mk signer consents purpose gates operation => cases operation <;> rfl

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem requiredPorts_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).requiredPorts (liftCurrent current) (liftRequest request) =
      base.requiredPorts current request := by
  simp only [RawLaw.requiredPorts, debit_original]
  cases request with
  | mk signer consents purpose gates operation => cases operation <;> rfl

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem operationAllowed_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).operationAllowed (liftCurrent current) (liftRequest request) =
      base.operationAllowed current request := by
  cases request with
  | mk signer consents purpose gates operation =>
      cases operation <;> simp [RawLaw.operationAllowed, RawPolicy.eval, law,
        liftRequest, liftOperation, eraseRequest, eraseOperation,
        liftCurrent, eraseCurrent]

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
@[simp] theorem signerMatches_original (request : Request Party Good Port Technology Instrument) :
    RawLaw.SignerMatches (liftRequest request) ↔ RawLaw.SignerMatches request := by
  cases request with
  | mk signer consents purpose gates operation => cases operation <;> rfl

omit [DecidableEq Good] [DecidableEq Instrument] in
@[simp] theorem claimGuard_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).ClaimGuard (liftCurrent current) (liftRequest request) ↔
      base.ClaimGuard current request := by
  cases request with
  | mk signer consents purpose gates operation =>
      cases operation with
      | use _ _ kind => cases kind <;> rfl
      | _ => rfl

omit [DecidableEq Instrument] in
@[simp] theorem valid_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).Valid (liftCurrent current) (liftRequest request) ↔ base.Valid current request := by
  simp only [RawLaw.Valid, signerMatches_original, operationAllowed_original,
    requiredPorts_original, claimGuard_original, debit_original, credit_original]
  simp only [liftCurrent, liftRequest, allowed_original, controller_original]

omit [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] in
@[simp] theorem nextClaims_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    RawLaw.nextClaims (liftCurrent current) (liftRequest request) = RawLaw.nextClaims current request := by
  cases request with
  | mk signer consents purpose gates operation => cases operation <;> rfl

theorem paidStep_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).paidStep (liftCurrent current) (liftRequest request) =
      liftCurrent (base.paidStep current request) := by
  apply RawCurrent.ext
  · funext party good
    change current.stock party good -
      flowAt ((law base assetPort).debit (liftCurrent current) (liftRequest request)) party good +
      flowAt ((law base assetPort).credit (liftCurrent current) (liftRequest request)) party good = _
    rw [debit_original, credit_original]
    rfl
  · exact nextClaims_original current request
  · cases request with
    | mk signer consents purpose gates operation => cases operation <;> rfl
  · rfl
  · rfl

theorem step_original (current : RawCurrent Party Good Technology Instrument)
    (request : Request Party Good Port Technology Instrument) :
    (law base assetPort).step (liftCurrent current) (liftRequest request) =
      liftCurrent (base.step current request) := by
  by_cases accepted : base.Valid current request
  · simp only [RawLaw.step, valid_original, if_pos accepted, paidStep_original]
  · simp only [RawLaw.step, valid_original, if_neg accepted]

theorem execute_original (current : RawCurrent Party Good Technology Instrument)
    (index : Nat) (word : RawEvent Party Good Port Technology Instrument) :
    (law base assetPort).execute (liftCurrent current) index (word.map liftRequest) =
      ⟨liftCurrent (base.execute current index word).final,
        (base.execute current index word).items.map liftItem⟩ := by
  induction word generalizing current index with
  | nil => rfl
  | cons request tail ih =>
      simp only [List.map_cons, RawLaw.execute, step_original, ih]
      rfl

theorem next_original (current : RawCurrent Party Good Technology Instrument)
    (word : RawEvent Party Good Port Technology Instrument) :
    (law base assetPort).next (liftCurrent current) (word.map liftRequest) =
      liftCurrent (base.next current word) := by
  simp only [RawLaw.next, execute_original]
  rfl

omit [DecidableEq Good] [DecidableEq Instrument] in
theorem other_personal_authority_unchanged (port : Port) (other : port ≠ assetPort)
    (actor : Party) (fixed : ∀ technology, base.controller technology port = actor)
    (technology : Title Party Technology) :
    (law base assetPort).controller technology port = actor := by
  simp only [law, controller, if_neg other, fixed]

#print axioms execute_original
#print axioms next_original
#print axioms other_personal_authority_unchanged

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.AssetAuthority.LawExtension
