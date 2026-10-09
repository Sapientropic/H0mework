import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Genome

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ResourceExecution CPS1ReactiveSourceEntry CPS1LiveEditing

abbrev SourcePoint := Σ frame : CPS1Recycling.Frame, CPS1ReactiveNuclear.SourceCursor frame

structure NativeSample where
  frame : CPS1Recycling.Frame
  before : CPS1ReactiveNuclear.SourceCursor frame
  water : Nat
  raw : List RawSupply
  path : CPS1Recycling.SplitSite
  events : List CPS1Recycling.RawEvent
  feed : List CPS1Recycling.RawMaterial
  physical : PhysicalRaw
  depth : Nat
  event : NativeBiosyntheticEvent before water raw path events feed physical depth

def NativeSample.current (sample : NativeSample) : SourcePoint :=
  ⟨sample.event.physicalEvent.seed.translation.generatedFrame,sample.event.reached⟩
def NativeSample.missing (sample : NativeSample) : Option Species :=
  sample.event.physicalEvent.seed.translation.native.missing

structure RenewalSample where
  first : NativeSample
  supply : ContinuationRaw
  result : RenewedBiosynthesis first.event supply

def RenewalSample.returned (sample : RenewalSample) : NativeSample :=
  ⟨sample.first.event.physicalEvent.seed.translation.generatedFrame,
    sample.first.event.reached,sample.supply.water,sample.supply.translation,
    sample.supply.path,sample.supply.recycling,sample.supply.recycleFeed,sample.supply.physical,
    sample.supply.depth,sample.result.returned⟩

-- These accounts stay unsettled until their own actual source supplies an observation.
inductive IndependentDuty
  | tissueGovernance | abnormalLineage | catalysis | cancerSafety | learnedExperience
  | serviceCapacity | constitutionalAccess
  deriving DecidableEq

def independentDuties : List IndependentDuty :=
  [.tissueGovernance,.abnormalLineage,.catalysis,.cancerSafety,.learnedExperience,
    .serviceCapacity,.constitutionalAccess]

structure Body where
  origin : SourcePoint
  current : SourcePoint
  lastNative : Option NativeSample
  reopened : Option RenewalSample
  pending : List IndependentDuty

def initialBody (current : SourcePoint) : Body :=
  ⟨current,current,none,none,independentDuties⟩

structure DamageResidual where
  genomic : ProteinDamageRead
  nativeCut : Option Species
  independent : List IndependentDuty

def damageResidual (body : Body) : DamageResidual :=
  ⟨readProteinDamage body.current.2.native.current,
    body.lastNative.bind NativeSample.missing,body.pending⟩

def BiosyntheticCertified (body : Body) : Prop :=
  ∃ sample, body.lastNative = some sample ∧ body.current = sample.current ∧
    readProteinDamage body.current.2.native.current = .fullLength ∧
    sample.missing = none ∧ sample.event.newlyProduced = 1

def EndogenousRenewal (body : Body) : Prop :=
  BiosyntheticCertified body ∧ ∃ sample, body.reopened = some sample ∧
    body.current = sample.returned.current ∧ sample.result.returned.newlyProduced = 1

structure RepairRaw where
  water : Nat
  raw : List RawSupply
  path : CPS1Recycling.SplitSite
  events : List CPS1Recycling.RawEvent
  feed : List CPS1Recycling.RawMaterial
  physical : PhysicalRaw
  depth : Nat
  next : ContinuationRaw

def classifyWhole {frame : CPS1Recycling.Frame} {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw) :
    BiologicalDisposition before water raw path events feed physical depth supply :=
  match selected : consumeWhole whole with
  | .sourceResidual source => .originalResidual whole (.sourceResidual source)
  | .produced event => .localUpdate whole event selected (renewBiosynthesis event supply)

structure LocalRepairEvent (body : Body) where
  request : RepairRaw
  whole : WholeRun body.current.2 request.water request.raw request.path
    request.events request.feed request.physical request.depth
  result : BiologicalDisposition body.current.2 request.water request.raw request.path
    request.events request.feed request.physical request.depth request.next
  actual : result = classifyWhole whole request.next

def localRepairEvent (body : Body) (request : RepairRaw) : LocalRepairEvent body :=
  let whole := executeWhole body.current.2 request.water request.raw request.path request.events
    request.feed request.physical request.depth
  ⟨request,whole,classifyWhole whole request.next,rfl⟩

def afterRenewed (body : Body) (sample : RenewalSample) : Body :=
  ⟨body.origin,sample.returned.current,some sample.returned,some sample,body.pending⟩

def bodyWrite (body : Body) (event : LocalRepairEvent body) : Body :=
  match event.result with
  | .originalResidual _ _ => body
  | .localUpdate _ first _ result =>
    match result with
    | .residual _ _ => body
    | .renewed update =>
      afterRenewed body ⟨⟨body.current.1,body.current.2,event.request.water,event.request.raw,
        event.request.path,event.request.events,event.request.feed,event.request.physical,
        event.request.depth,first⟩,event.request.next,update⟩

def ResultSuccessful {frame : CPS1Recycling.Frame} {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat} {supply : ContinuationRaw}
    (result : BiologicalDisposition before water raw path events feed physical depth supply) : Prop :=
  match result with
  | .originalResidual _ _ => False
  | .localUpdate _ _ _ next => match next with
    | .residual _ _ => False
    | .renewed _ => True

def Successful (body : Body) (event : LocalRepairEvent body) : Prop :=
  ResultSuccessful event.result

instance (body : Body) (event : LocalRepairEvent body) : Decidable (Successful body event) := by
  unfold Successful ResultSuccessful
  cases event.result with
  | originalResidual _ _ => infer_instance
  | localUpdate _ _ _ result => cases result <;> infer_instance

def BodyUpdate (body : Body) (event : LocalRepairEvent body) (next : Body) : Prop :=
  Successful body event ∧ next = bodyWrite body event

def LocalInvariant (body : Body) (event : LocalRepairEvent body) (next : Body) : Prop :=
  BodyUpdate body event next ∧ EndogenousRenewal next

def Reopened (body : Body) (residual : DamageResidual) (event : LocalRepairEvent body) (next : Body) : Prop :=
  BodyUpdate body event next ∧ residual = damageResidual body ∧
    PrematureStop residual.genomic ∧ EndogenousRenewal next ∧
      next.origin = body.origin ∧ next.pending = residual.independent

private theorem after_renewed_certified (body : Body) (sample : RenewalSample) :
    BiosyntheticCertified (afterRenewed body sample) := by
  refine ⟨sample.returned,rfl,rfl,?_,sample.result.nextNative,sample.result.nextBirth⟩
  exact sample.result.nextRead

private theorem after_renewed_endogenous (body : Body) (sample : RenewalSample) :
    EndogenousRenewal (afterRenewed body sample) :=
  ⟨after_renewed_certified body sample,sample,rfl,rfl,sample.result.nextBirth⟩

structure BiosyntheticLocalCourt where
  agingDamageResidual : Body → DamageResidual
  LocalRepairEventAt : Body → Type 1
  SourceGeneratedBodyUpdateAt : (body : Body) → LocalRepairEventAt body → Body → Prop
  SourceGeneratedLocalInvariantCertificateAt : (body : Body) → LocalRepairEventAt body → Body → Prop
  ReopenedEndogenousRenewalAt : (body : Body) → DamageResidual → LocalRepairEventAt body → Body → Prop

def biosyntheticCourt : BiosyntheticLocalCourt :=
  ⟨damageResidual,LocalRepairEvent,BodyUpdate,LocalInvariant,Reopened⟩

theorem successful_local_repair (body : Body) (event : LocalRepairEvent body)
    (successful : Successful body event) :
    BodyUpdate body event (bodyWrite body event) ∧
    LocalInvariant body event (bodyWrite body event) ∧
    Reopened body (damageResidual body) event (bodyWrite body event) := by
  rcases event with ⟨request,sourceWhole,result,actual⟩
  cases result with
  | originalResidual whole readout => cases successful
  | localUpdate whole first selected result =>
    cases result with
    | residual continuation failure => cases successful
    | renewed update =>
      let sample : RenewalSample := ⟨⟨body.current.1,body.current.2,request.water,request.raw,
        request.path,request.events,request.feed,request.physical,request.depth,first⟩,request.next,update⟩
      have renewal := after_renewed_endogenous body sample
      refine ⟨⟨successful,rfl⟩,⟨⟨successful,rfl⟩,renewal⟩,
        ⟨⟨successful,rfl⟩,rfl,?_,renewal,rfl,rfl⟩⟩
      exact update.priorDamage

end
end CPS1BiologicalUpdate
