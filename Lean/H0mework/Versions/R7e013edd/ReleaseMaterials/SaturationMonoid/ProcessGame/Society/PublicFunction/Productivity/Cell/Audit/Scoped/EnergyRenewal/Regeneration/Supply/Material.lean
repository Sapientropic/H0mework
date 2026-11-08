import H0mework.Versions.Rac87df08.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Handoff.Runtime
import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UpstreamProductionControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
set_option linter.unusedSimpArgs false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
abbrev ProviderParty := Delegation.Funded.Party
abbrev ProviderGood := Repayment.Recovery.Good
abbrev ProviderPort := Delegation.Funded.Port
abbrev ProviderTechnology := Mandate.State ProviderParty Bool
abbrev ProviderCurrent := RawCurrent ProviderParty ProviderGood ProviderTechnology Unit
abbrev ProviderAction := Request ProviderParty ProviderGood ProviderPort ProviderTechnology Unit
abbrev providerLaw := Protocol.SymbolicAuthentication.UpstreamProductionLaw.law
abbrev providerOrigin : Protocol.SymbolicAuthentication.RoundEpisodeSource.State :=
  Protocol.SymbolicAuthentication.UpstreamProductionControls.second
abbrev providerSourceCurrent : ProviderCurrent := Protocol.SymbolicAuthentication.RoundEpisodeSource.current providerOrigin

/-- Source specialization emits kernel-checked terms, never caller balances. -/
syntax "source_value% " term : term
elab_rules : term
  | `(source_value% $value) => do
    let source ← Lean.Elab.Term.elabTerm value none
    Lean.Meta.withTransparency .all <| Lean.Meta.reduce source

def providerInitial : ProviderCurrent where
  stock := fun party good => match party.val with
    | 0 => match good with
      | .feedstock => source_value% (providerSourceCurrent.stock 0 .feedstock)
      | .service => source_value% (providerSourceCurrent.stock 0 .service)
      | .waste => source_value% (providerSourceCurrent.stock 0 .waste)
      | .energy => source_value% (providerSourceCurrent.stock 0 .energy)
      | .labor => source_value% (providerSourceCurrent.stock 0 .labor)
    | 1 => match good with
      | .feedstock => source_value% (providerSourceCurrent.stock 1 .feedstock)
      | .service => source_value% (providerSourceCurrent.stock 1 .service)
      | .waste => source_value% (providerSourceCurrent.stock 1 .waste)
      | .energy => source_value% (providerSourceCurrent.stock 1 .energy)
      | .labor => source_value% (providerSourceCurrent.stock 1 .labor)
    | _ => match good with
      | .feedstock => source_value% (providerSourceCurrent.stock 2 .feedstock)
      | .service => source_value% (providerSourceCurrent.stock 2 .service)
      | .waste => source_value% (providerSourceCurrent.stock 2 .waste)
      | .energy => source_value% (providerSourceCurrent.stock 2 .energy)
      | .labor => source_value% (providerSourceCurrent.stock 2 .labor)
  claims := fun _ debtor creditor => match debtor.val with
    | 0 => match creditor.val with
      | 0 => source_value% (providerSourceCurrent.claims () 0 0)
      | 1 => source_value% (providerSourceCurrent.claims () 0 1)
      | _ => source_value% (providerSourceCurrent.claims () 0 2)
    | 1 => match creditor.val with
      | 0 => source_value% (providerSourceCurrent.claims () 1 0)
      | 1 => source_value% (providerSourceCurrent.claims () 1 1)
      | _ => source_value% (providerSourceCurrent.claims () 1 2)
    | _ => match creditor.val with
      | 0 => source_value% (providerSourceCurrent.claims () 2 0)
      | 1 => source_value% (providerSourceCurrent.claims () 2 1)
      | _ => source_value% (providerSourceCurrent.claims () 2 2)
  technology := source_value% providerSourceCurrent.technology
  clock := source_value% providerSourceCurrent.clock
  round := source_value% providerSourceCurrent.round

elab "source_refl" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  Lean.Meta.withTransparency .all <| goal.refl
  Lean.Elab.Tactic.replaceMainGoal []

theorem provider_initial_is_its_entire_original_source_current : providerInitial=providerSourceCurrent := by
  apply RawCurrent.ext
  · funext party good
    fin_cases party <;> cases good <;> source_refl
  · funext instrument debtor creditor
    cases instrument;fin_cases debtor <;> fin_cases creditor <;> source_refl
  all_goals source_refl
attribute [irreducible] providerInitial

/-- This codec preserves native quantities. It is not a Joule conversion. -/
def material : ProviderGood → Good
  | .feedstock => .feed | .service => .life | .waste => .waste | .energy => .energy | .labor => .labor
def providerMaterial : Good → Option ProviderGood
  | .feed => some .feedstock | .life => some .service | .waste => some .waste
  | .energy => some .energy | .labor => some .labor | _ => none
theorem material_left_inverse (good : ProviderGood) : providerMaterial (material good) = some good := by cases good <;> rfl

abbrev Actor := Sum Party ProviderParty
structure Technology where
  audit : Mandate.State Party Cell.Technology
  provider : ProviderTechnology
  clockLag : ℚ
  roundLag : ℤ
  deriving DecidableEq
inductive Port where
  | audit (port : AuditPort) | provider (port : ProviderPort) | exchange
  deriving DecidableEq
inductive Instrument where
  | audit | provider | delivery
  deriving DecidableEq
abbrev Current := RawCurrent Actor Good Technology Instrument
abbrev JointAction := Request Actor Good Port Technology Instrument
abbrev customer : Actor := .inl 0
abbrev supplier : Actor := .inr 0
abbrev receiver : Actor := .inl 3

def audit (current : Current) : AuditCurrent :=
  ⟨fun p g => current.stock (.inl p) g,fun _ p q => current.claims .audit (.inl p) (.inl q),
    current.technology.audit,current.clock,current.round⟩
def provider (current : Current) : ProviderCurrent :=
  ⟨fun p g => current.stock (.inr p) (material g),fun _ p q => current.claims .provider (.inr p) (.inr q),
    current.technology.provider,current.clock-current.technology.clockLag,((current.round:ℤ)-current.technology.roundLag).toNat⟩

def join (legacy : AuditCurrent) (source : ProviderCurrent) : Current where
  stock := fun actor good => match actor with
    | .inl p => legacy.stock p good
    | .inr p => (providerMaterial good).elim 0 (source.stock p)
  claims := fun instrument debtor creditor => match instrument,debtor,creditor with
    | .audit,.inl p,.inl q => legacy.claims () p q
    | .provider,.inr p,.inr q => source.claims () p q
    | _,_,_ => 0
  technology := ⟨legacy.technology,source.technology,legacy.clock-source.clock,(legacy.round:ℤ)-source.round⟩
  clock := legacy.clock
  round := legacy.round

theorem join_keeps_the_entire_original_current (legacy : AuditCurrent) (source : ProviderCurrent) :
    audit (join legacy source) = legacy := by cases legacy; rfl
theorem join_keeps_every_provider_asset_and_native_claim (legacy : AuditCurrent) (source : ProviderCurrent) :
    (∀ actor good,(provider (join legacy source)).stock actor good=source.stock actor good) ∧
    (provider (join legacy source)).claims=source.claims ∧
    (provider (join legacy source)).technology=source.technology := by
  refine ⟨?_,?_,rfl⟩
  · intro actor good; simp [provider,join,material_left_inverse]
  · funext instrument debtor creditor; cases instrument; rfl

def liftAuditOperation (before : Current) : Operation Party Good (Mandate.State Party Cell.Technology) Unit →
    Operation Actor Good Technology Instrument
  | .produce p => .produce (.inl p)
  | .transfer p q goods => .transfer (.inl p) (.inl q) goods
  | .use p goods purpose => .use (.inl p) goods purpose
  | .issue _ p q amount => .issue .audit (.inl p) (.inl q) amount
  | .assign _ p q r amount => .assign .audit (.inl p) (.inl q) (.inl r) amount
  | .settle _ p q amount => .settle .audit (.inl p) (.inl q) amount
  | .revise p next => .revise (.inl p) {before.technology with audit := next}
  | .present => .present
def liftAudit (before : Current) (action : Action) : JointAction :=
  ⟨.inl action.signer,action.consents.map Sum.inl,.audit action.purpose,action.gates.map Port.audit,
    liftAuditOperation before action.operation⟩

def liftProviderOperation (before : Current) : Operation ProviderParty ProviderGood ProviderTechnology Unit →
    Operation Actor Good Technology Instrument
  | .produce p => .produce (.inr p)
  | .transfer p q goods => .transfer (.inr p) (.inr q) (goods.map fun (g,n) => (material g,n))
  | .use p goods purpose => .use (.inr p) (goods.map fun (g,n) => (material g,n)) purpose
  | .issue _ p q amount => .issue .provider (.inr p) (.inr q) amount
  | .assign _ p q r amount => .assign .provider (.inr p) (.inr q) (.inr r) amount
  | .settle _ p q amount => .settle .provider (.inr p) (.inr q) amount
  | .revise p next => .revise (.inr p) {before.technology with provider := next}
  | .present => .present
def liftProvider (before : Current) (action : ProviderAction) : JointAction :=
  ⟨.inr action.signer,action.consents.map Sum.inr,.provider action.purpose,action.gates.map Port.provider,
    liftProviderOperation before action.operation⟩

def auditParty : Actor → Option Party | .inl p => some p | _ => none
def providerParty : Actor → Option ProviderParty | .inr p => some p | _ => none
def auditPort : Port → Option AuditPort | .audit p => some p | _ => none
def providerPort : Port → Option ProviderPort | .provider p => some p | _ => none

def auditOperation (before : Current) : Operation Actor Good Technology Instrument →
    Option (Operation Party Good (Mandate.State Party Cell.Technology) Unit)
  | .produce p => return .produce (← auditParty p)
  | .transfer p q goods => return .transfer (← auditParty p) (← auditParty q) goods
  | .use p goods purpose => return .use (← auditParty p) goods purpose
  | .issue .audit p q amount => return .issue () (← auditParty p) (← auditParty q) amount
  | .assign .audit p q r amount => return .assign () (← auditParty p) (← auditParty q) (← auditParty r) amount
  | .settle .audit p q amount => return .settle () (← auditParty p) (← auditParty q) amount
  | .revise p target => if {before.technology with audit := target.audit}=target then return .revise (← auditParty p) target.audit else none
  | .present => some .present
  | _ => none
def auditAction (before : Current) (action : JointAction) : Option Action := do
  return ⟨← auditParty action.signer,← action.consents.mapM auditParty,← auditPort action.purpose,
    ← action.gates.mapM auditPort,← auditOperation before action.operation⟩

def providerBundle (goods : Bundle Good) : Option (Bundle ProviderGood) :=
  goods.mapM fun (g,n) => return (← providerMaterial g,n)
def providerOperation (before : Current) : Operation Actor Good Technology Instrument →
    Option (Operation ProviderParty ProviderGood ProviderTechnology Unit)
  | .produce p => return .produce (← providerParty p)
  | .transfer p q goods => return .transfer (← providerParty p) (← providerParty q) (← providerBundle goods)
  | .use p goods purpose => return .use (← providerParty p) (← providerBundle goods) purpose
  | .issue .provider p q amount => return .issue () (← providerParty p) (← providerParty q) amount
  | .assign .provider p q r amount => return .assign () (← providerParty p) (← providerParty q) (← providerParty r) amount
  | .settle .provider p q amount => return .settle () (← providerParty p) (← providerParty q) amount
  | .revise p target => if {before.technology with provider := target.provider}=target then return .revise (← providerParty p) target.provider else none
  | .present => some .present
  | _ => none
def providerAction (before : Current) (action : JointAction) : Option ProviderAction := do
  return ⟨← providerParty action.signer,← action.consents.mapM providerParty,← providerPort action.purpose,
    ← action.gates.mapM providerPort,← providerOperation before action.operation⟩

def feed : JointAction := ⟨customer,[],.exchange,[],.transfer customer supplier [(.feed,1)]⟩
def obligation : JointAction := ⟨supplier,[],.exchange,[],.issue .delivery supplier receiver 2⟩
def shipment (quantity : ℚ) : JointAction := ⟨supplier,[],.exchange,[],.settle .delivery supplier receiver quantity⟩

def exchangeAllowed (current : Current) (action : JointAction) : Bool :=
  let payment := match action.operation with
    | .settle .delivery debtor creditor quantity =>
      decide (0<quantity ∧ debtor=supplier ∧ creditor=receiver ∧ action=shipment quantity)
    | _ => false
  decide (action.consents=[] ∧ action.purpose=.exchange ∧ action.gates=[]) &&
    (decide (action=feed ∧ 0<current.claims .delivery supplier receiver) ||
     decide (action=obligation ∧ current.claims .delivery supplier receiver=0) || payment)

def law (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) :
    RawLaw Actor Good Port Technology Instrument where
  technique := fun technology actor => match actor with
    | .inl p => let t := (Mandate.law energyBase scope).technique technology.audit p
      ⟨t.inputs,t.outputs,t.maintenance,t.requiredPorts.map Port.audit⟩
    | .inr p => let t := providerLaw.technique technology.provider p
      ⟨t.inputs.map fun (g,n) => (material g,n),t.outputs.map fun (g,n) => (material g,n),
        t.maintenance.map fun (g,n) => (material g,n),t.requiredPorts.map Port.provider⟩
  controller := fun _ _ => customer
  allowed := fun _ _ _ => true
  stockPort := fun _ _ _ => .exchange
  revisionPort := fun _ => .exchange
  revisionCost := fun before after => if after.audit=before.audit then
      (providerLaw.revisionCost before.provider after.provider).map fun (g,n) => (material g,n) else scope.revisionCost
  settlementUnit := fun instrument => match instrument with | .delivery => .energy | _ => .life
  settlementRate := fun _ => 1
  issuerPort := fun _ => .exchange
  necessities := fun current actor => match actor with
    | .inl p => (Mandate.law energyBase scope).necessities (audit current) p
    | .inr p => (providerLaw.necessities (provider current) p).map fun (g,n) => (material g,n)
  mandatoryMaintenance := fun current actor => match actor with
    | .inl p => (Mandate.law energyBase scope).mandatoryMaintenance (audit current) p
    | .inr p => (providerLaw.mandatoryMaintenance (provider current) p).map fun (g,n) => (material g,n)
  policy := .opaque fun current action => match action.purpose with
    | .audit _ => (auditAction current action).any fun original => decide ((Mandate.law energyBase scope).Valid (audit current) original)
    | .provider _ => (providerAction current action).any fun original => decide (providerLaw.Valid (provider current) original)
    | .exchange => exchangeAllowed current action
  duration := fun _ => 1

theorem every_material_flow (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (word : List JointAction) (actor : Actor) (good : Good) :
    ((law scope).next current word).stock actor good+(law scope).totalDebit ((law scope).rawItems current word) actor good=
      current.stock actor good+(law scope).totalCredit ((law scope).rawItems current word) actor good :=
  (law scope).actual_next_material_balance _ _ _ _

theorem join_keeps_the_entire_provider_current (legacy : AuditCurrent) (source : ProviderCurrent) :
    provider (join legacy source) = source := by
  apply RawCurrent.ext
  · funext actor good; exact (join_keeps_every_provider_asset_and_native_claim legacy source).1 actor good
  · exact (join_keeps_every_provider_asset_and_native_claim legacy source).2.1
  · rfl
  · change legacy.clock-(legacy.clock-source.clock)=source.clock; ring
  · change ((legacy.round:ℤ)-((legacy.round:ℤ)-source.round)).toNat=source.round
    omega

@[simp] theorem auditParty_inl (party : Party) : auditParty (.inl party)=some party := rfl
@[simp] theorem auditPort_audit (port : AuditPort) : auditPort (.audit port)=some port := rfl

@[simp] theorem audit_roundtrip (current : Current) (action : Action) :
    auditAction current (liftAudit current action)=some action := by
  rcases action with ⟨signer,consents,purpose,gates,operation⟩
  have people : (consents.map Sum.inl).mapM auditParty=some consents := by
    induction consents with
    | nil => rfl
    | cons p rest ih => simp [ih]
  have ports : (gates.map Port.audit).mapM auditPort=some gates := by
    induction gates with
    | nil => rfl
    | cons p rest ih => simp [ih]
  cases operation <;> simp [auditAction,liftAudit,liftAuditOperation,auditOperation,people,ports]

/-- The joint admission consumes the original complete authority check. -/
theorem audit_admission (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (action : Action) (paid : (law scope).Valid current (liftAudit current action)) :
    (Mandate.law energyBase scope).Valid (audit current) action := by
  have accepted := paid.1.2
  change (auditAction current (liftAudit current action)).any
    (fun original => decide ((Mandate.law energyBase scope).Valid (audit current) original))=true at accepted
  rw [audit_roundtrip] at accepted
  simpa using accepted

def production (current : Current) : JointAction :=
  liftProvider current Protocol.SymbolicAuthentication.RenewedQuorumMaterial.renew

theorem provider_admission (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (paid : (law scope).Valid current (production current)) :
    providerLaw.Valid (provider current) Protocol.SymbolicAuthentication.RenewedQuorumMaterial.renew := by
  have accepted := paid.1.2
  simpa [law,RawLaw.operationAllowed,RawPolicy.eval,production,liftProvider,liftProviderOperation,
    providerAction,providerOperation,providerParty,providerPort,
    Protocol.SymbolicAuthentication.RenewedQuorumMaterial.renew] using accepted

/-- The conversion coefficients are the already-installed provider recipe, not a new balance. -/
theorem original_recipe_has_real_inputs_and_outputs
    (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) (current : Current) :
    flowAt ((law scope).debit current (production current)) supplier .feed=1 ∧
    flowAt ((law scope).debit current (production current)) supplier .labor=1 ∧
    flowAt ((law scope).credit current (production current)) supplier .energy=2 ∧
    flowAt ((law scope).credit current (production current)) supplier .labor=3 := by
  simp [RawLaw.debit,RawLaw.credit,law,production,liftProvider,liftProviderOperation,providerLaw,
    Protocol.SymbolicAuthentication.WorkerInputLaw.law,Protocol.SymbolicAuthentication.FuelMandateLaw.law,
    Protocol.SymbolicAuthentication.FuelMandateLaw.base,Protocol.SymbolicAuthentication.RenewedQuorumMaterial.base,
    Protocol.SymbolicAuthentication.RenewedQuorumMaterial.renew,Mandate.law,material,supplier,flowAt,locate,amount]

theorem paid_production_really_consumes_and_generates
    (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) (current : Current)
    (paid : (law scope).Valid current (production current)) :
    ((law scope).step current (production current)).stock supplier .feed=current.stock supplier .feed-1 ∧
    ((law scope).step current (production current)).stock supplier .energy=current.stock supplier .energy+2 ∧
    ((law scope).step current (production current)).stock supplier .labor=current.stock supplier .labor+2 := by
  rw [RawLaw.step,if_pos paid]
  simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,law,production,liftProvider,liftProviderOperation,
    providerLaw,Protocol.SymbolicAuthentication.WorkerInputLaw.law,Protocol.SymbolicAuthentication.FuelMandateLaw.law,
    Protocol.SymbolicAuthentication.FuelMandateLaw.base,Protocol.SymbolicAuthentication.RenewedQuorumMaterial.base,
    Protocol.SymbolicAuthentication.RenewedQuorumMaterial.renew,Mandate.law,material,supplier,flowAt,locate,amount]
  ring

/-- Delivery retires only its own obligation and moves the same native energy quantity. -/
theorem paid_shipment_is_material_settlement
    (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort)) (current : Current) (quantity : ℚ)
    (paid : (law scope).Valid current (shipment quantity)) :
    ((law scope).step current (shipment quantity)).stock supplier .energy=current.stock supplier .energy-quantity ∧
    ((law scope).step current (shipment quantity)).stock receiver .energy=current.stock receiver .energy+quantity ∧
    ((law scope).step current (shipment quantity)).claims .delivery supplier receiver=
      current.claims .delivery supplier receiver-quantity := by
  rw [RawLaw.step,if_pos paid]
  simp [RawLaw.paidStep,RawLaw.debit,RawLaw.credit,RawLaw.nextClaims,shipment,
    law,supplier,receiver,flowAt,locate,amount]

def Historical (action : JointAction) : Prop := match action.operation with
  | .issue instrument .. | .assign instrument .. | .settle instrument .. => instrument=.delivery
  | _ => True

theorem historical_claims_step (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (action : JointAction) (safe : Historical action)
    (instrument : Instrument) (old : instrument≠.delivery) :
    ((law scope).step current action).claims instrument=current.claims instrument := by
  unfold RawLaw.step
  split
  · change RawLaw.nextClaims current action instrument=current.claims instrument
    funext debtor creditor
    cases operation : action.operation <;>
      simp_all [Historical,RawLaw.nextClaims]
  · rfl

theorem historical_claims_execute (scope : Mandate.Scope (Party := Party) (Good := Good) (Port := AuditPort))
    (current : Current) (word : List JointAction) (index : Nat)
    (safe : ∀ action∈word,Historical action) (instrument : Instrument) (old : instrument≠.delivery) :
    ((law scope).execute current index word).final.claims instrument=current.claims instrument := by
  induction word generalizing current index with
  | nil => rfl
  | cons action rest ih =>
    change ((law scope).execute ((law scope).step current action) (index+1) rest).final.claims instrument=_
    rw [ih _ _ (fun a h => safe a (List.mem_cons_of_mem _ h)),historical_claims_step scope current action (safe action (by simp)) instrument old]

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply
