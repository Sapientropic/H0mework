import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.GrantTrace
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Service
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff.Challenge

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff

open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root ResponsibilityLifecycle
open Followup Institutions.Capitalism.Universal.Source.ProgrammeFace
variable {oldScope : Mandate.Scope (Party := Bool) (Good := Good) (Port := Mandate.Source.Port)}
  {bound : BoundSource base oldScope} {inputs : List (List Action)} (fresh : Handoff.Ready bound inputs)
noncomputable section

abbrev serviceHistories (index : (source fresh).Slot) :=
  OutstandingSource.History.NativeService.historyAt (source fresh) (epochInputs fresh) index 3

def grants := Mandate.Challenge.Cross.grantsBefore (newBound fresh) (epochInputs fresh)
def objections := Mandate.Challenge.Cross.residentsAt (newBound fresh) (epochInputs fresh)

variable {fuel : ℚ} {old : Followup.Joint.Inventory fuel} (authority : ScopeRevision.Ready old)
  {originInputs : List (List Action)} (inventory : Pending.Joint.Inventory authority originInputs)
  (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)

structure EpochDisposition where
  private mk ::
  prior : Future.Runtime.Disposition authority inventory .revision
  prior_exact : prior = Future.Runtime.generate authority inventory .revision
  reviewBirth : ActualBirth.At (originalInput (Pending.B authority) (Future.advance authority inventory .revision).inputs)
    (ProgrammeHistory.visitAt (originalInput (Pending.B authority) (Future.advance authority inventory .revision).inputs)
      (Future.advance authority inventory .revision).inputs.length) fresh.actor
  reviewBirth_exact : reviewBirth = fresh.birth
  legacy : Pending.Joint.Inventory authority originInputs
  legacy_exact : legacy = Future.advance authority inventory .revision
  initial_exact : (I fresh).initial = Pending.current authority legacy.inputs
  taskHomology : (Pending.B authority).source.Slot → (source fresh).Slot
  taskHomology_exact : ∀ index, taskHomology index = homologous fresh index
  slot_exact : ∀ index, (source fresh).seed.slot (taskHomology index) = (Pending.B authority).source.seed.slot index
  services : (index : (source fresh).Slot) → OutstandingSource.History.NativeService.Prefix (source fresh) (epochInputs fresh) index 3
  services_exact : ∀ index, services index = Handoff.serviceHistories fresh index
  grants : List (Mandate.Challenge.Cross.GrantResident (newBound fresh) (epochInputs fresh))
  grants_exact : grants = Handoff.grants fresh
  objections : List (Mandate.Challenge.Cross.Resident (newBound fresh) (epochInputs fresh))
  objections_exact : objections = Handoff.objections fresh
  oldGrantReceipts : List (Handoff.Grant.Receipt fresh)
  oldGrantReceipts_exact : oldGrantReceipts = Handoff.Grant.receipts fresh 0 4
  oldGrants : List (Handoff.Grant.Entry fresh 4)
  oldGrants_exact : oldGrants = Handoff.Grant.inventory fresh (Future.advance authority inventory .revision).grants 4
  oldServiceObservations : List (OutstandingSource.History.NativeService.ExpiredInput (Pending.B authority).source)
  oldServiceObservations_exact : oldServiceObservations = Handoff.Service.observations fresh 3
  oldServices : (index : (Pending.B authority).source.Slot) →
    OutstandingSource.History.NativeService.Expired.Continuation (Pending.B authority).source
      ((Future.advance authority inventory .revision).services index)
  oldServices_exact : ∀ index, oldServices index = Handoff.Service.continued fresh ((Future.advance authority inventory .revision).services index) 3
  oldChallengeReceipts : List (Mandate.Challenge.ScopeBoundary.Receipt (Handoff.Challenge.occurrence fresh))
  oldChallengeReceipts_exact : oldChallengeReceipts = Handoff.Challenge.receipts fresh 4
  oldChallenges : List (Handoff.Challenge.Entry fresh 4)
  oldChallenges_exact : oldChallenges = Handoff.Challenge.inventory fresh (Future.advance authority inventory .revision).objections 4
  plan : Handoff.Outcome fresh
  plan_exact : plan = Handoff.outcome fresh
  account : Pending.Joint.Finance.Account
  account_exact : account = Handoff.Finance.account authority inventory fresh 4
  financialRun : (Financial.Family.process Pending.Joint.Finance.sources).Run legacy.finance.current account.current
  migrations : ∀ index slot, legacy.finance.current.slots[index]? = some slot →
    Financial.Family.Migration.Follow Pending.Joint.Finance.sources financialRun index slot
  matrix : Financial.Family.ledgerClaims Pending.Joint.Finance.sources account.current = (current fresh 4).claims

def generateEpoch : EpochDisposition authority inventory fresh :=
  ⟨Future.Runtime.generate authority inventory .revision,rfl, fresh.birth,rfl, Future.advance authority inventory .revision,rfl,rfl,
    homologous fresh, fun _ => rfl, original_slot_content_is_preserved fresh,
    Handoff.serviceHistories fresh, fun _ => rfl, Handoff.grants fresh,rfl,Handoff.objections fresh,rfl,
    Handoff.Grant.receipts fresh 0 4,rfl, Handoff.Grant.inventory fresh (Future.advance authority inventory .revision).grants 4,rfl,
    Handoff.Service.observations fresh 3,rfl,
    (fun index => Handoff.Service.continued fresh ((Future.advance authority inventory .revision).services index) 3),fun _ => rfl,
    Handoff.Challenge.receipts fresh 4,rfl,
    Handoff.Challenge.inventory fresh (Future.advance authority inventory .revision).objections 4,rfl,
    Handoff.outcome fresh,rfl,Handoff.Finance.account authority inventory fresh 4,rfl,
    Handoff.Finance.run authority inventory fresh 4,
    fun index slot present => Financial.Family.Migration.follow _ _ index slot present,
    Handoff.Finance.matrix authority inventory fresh 4⟩

inductive Result where
  | private revised (fresh : Handoff.Ready (Pending.B authority) (Future.advance authority inventory .revision).inputs)
      (selected : Handoff.choose (Pending.B authority) (Future.advance authority inventory .revision).inputs = some fresh)
      (epoch : EpochDisposition authority inventory fresh) (exact : epoch = generateEpoch authority inventory fresh)
  | private blocked (absent : Handoff.choose (Pending.B authority) (Future.advance authority inventory .revision).inputs = none)
      (reason : Handoff.Blocked (Pending.B authority) (Future.advance authority inventory .revision).inputs)

def generate : Result authority inventory :=
  match selected : Handoff.choose (Pending.B authority) (Future.advance authority inventory .revision).inputs with
  | some fresh => .revised fresh selected (generateEpoch authority inventory fresh) rfl
  | none => .blocked selected (every_failed_handoff_has_an_actual_reason _ _ selected)

end
end SaturationMonoid.ProcessGame.Society.PublicFunction.Mandate.Financed.Continuing.Closure.Objection.Opening.ScopeRevision.Pending.Joint.Handoff
