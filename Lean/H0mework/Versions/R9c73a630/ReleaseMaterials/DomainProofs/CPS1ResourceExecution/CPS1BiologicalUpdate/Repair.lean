import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.Court

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace CPS1BiologicalUpdate
noncomputable section
open CPS1ReactiveSourceEntry CPS1LiveEditing

structure LocalRepairReceipt (body : Body) where
  event : LocalRepairEvent body
  nextBody : Body
  update : biosyntheticCourt.SourceGeneratedBodyUpdateAt body event nextBody
  invariant : biosyntheticCourt.SourceGeneratedLocalInvariantCertificateAt body event nextBody
  reopened : biosyntheticCourt.ReopenedEndogenousRenewalAt body
    (biosyntheticCourt.agingDamageResidual body) event nextBody

inductive LocalRepairDisposition (body : Body)
  | residual (event : LocalRepairEvent body) (notSuccessful : ¬ Successful body event)
  | repaired (receipt : LocalRepairReceipt body)

def classifyRepair (body : Body) (event : LocalRepairEvent body) : LocalRepairDisposition body := by
  if paid : Successful body event then
    have actual := successful_local_repair body event paid
    exact .repaired ⟨event,bodyWrite body event,actual.1,actual.2.1,actual.2.2⟩
  else exact .residual event paid

def repairBody (current : SourcePoint) (request : RepairRaw) : LocalRepairDisposition (initialBody current) :=
  classifyRepair (initialBody current) (localRepairEvent (initialBody current) request)

def repairWhole {frame : CPS1Recycling.Frame} {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw) :
    LocalRepairDisposition (initialBody ⟨frame,before⟩) :=
  let body := initialBody ⟨frame,before⟩
  let request : RepairRaw := ⟨water,raw,path,events,feed,physical,depth,supply⟩
  let event : LocalRepairEvent body := ⟨request,whole,classifyWhole whole supply,rfl⟩
  classifyRepair body event

theorem classify_repair_of_success (body : Body) (event : LocalRepairEvent body)
    (successful : Successful body event) :
    ∃ receipt, classifyRepair body event = .repaired receipt := by
  unfold classifyRepair
  rw [dif_pos successful]
  exact ⟨_,rfl⟩

theorem repair_whole_renewed {frame : CPS1Recycling.Frame} {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw) :
    match classifyWhole whole supply with
    | .originalResidual _ _ => True
    | .localUpdate _ _ _ result => match result with
      | .residual _ _ => True
      | .renewed _ => ∃ receipt, repairWhole whole supply = .repaired receipt := by
  let body := initialBody ⟨frame,before⟩
  let request : RepairRaw := ⟨water,raw,path,events,feed,physical,depth,supply⟩
  let event : LocalRepairEvent body := ⟨request,whole,classifyWhole whole supply,rfl⟩
  have selected : ∀ result : BiologicalDisposition before water raw path events feed physical depth supply,
      result = classifyWhole whole supply →
      match result with
      | .originalResidual _ _ => True
      | .localUpdate _ _ _ next => match next with
        | .residual _ _ => True
        | .renewed _ => ∃ receipt, repairWhole whole supply = .repaired receipt := by
    intro result actual
    cases result with
    | originalResidual _ _ => trivial
    | localUpdate prior first chosen next =>
      cases next with
      | residual _ _ => trivial
      | renewed update =>
        have paid : Successful body event := by
          change ResultSuccessful (classifyWhole whole supply)
          exact Eq.mp (congrArg ResultSuccessful actual) True.intro

        exact classify_repair_of_success body event paid

  exact selected _ rfl

theorem repair_whole_of_success {frame : CPS1Recycling.Frame} {before : CPS1ReactiveNuclear.SourceCursor frame}
    {water : Nat} {raw : List RawSupply} {path : CPS1Recycling.SplitSite}
    {events : List CPS1Recycling.RawEvent} {feed : List CPS1Recycling.RawMaterial}
    {physical : PhysicalRaw} {depth : Nat}
    (whole : WholeRun before water raw path events feed physical depth) (supply : ContinuationRaw)
    (paid : ResultSuccessful (classifyWhole whole supply)) :
    ∃ receipt, repairWhole whole supply = .repaired receipt :=
  classify_repair_of_success (initialBody ⟨frame,before⟩)
    ⟨⟨water,raw,path,events,feed,physical,depth,supply⟩,whole,classifyWhole whole supply,rfl⟩ paid

theorem actualLocalRepair (body : Body) (receipt : LocalRepairReceipt body) :
    ∃ event : biosyntheticCourt.LocalRepairEventAt body,
      biosyntheticCourt.SourceGeneratedBodyUpdateAt body event receipt.nextBody ∧
      biosyntheticCourt.SourceGeneratedLocalInvariantCertificateAt body event receipt.nextBody ∧
      biosyntheticCourt.ReopenedEndogenousRenewalAt body (biosyntheticCourt.agingDamageResidual body)
        event receipt.nextBody :=
  ⟨receipt.event,receipt.update,receipt.invariant,receipt.reopened⟩

theorem nextEndogenousRenewal (body : Body) (receipt : LocalRepairReceipt body) :
    EndogenousRenewal receipt.nextBody := receipt.invariant.2

end
end CPS1BiologicalUpdate
