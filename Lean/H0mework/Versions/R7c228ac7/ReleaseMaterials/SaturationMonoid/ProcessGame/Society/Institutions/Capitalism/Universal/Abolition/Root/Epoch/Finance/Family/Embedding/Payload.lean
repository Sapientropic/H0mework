import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Vocabulary

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding

open ResponsibilityLifecycle
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument Index : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (sources : Index → ProgrammeSource.Input Party Good Port Technology Instrument)
  (depths counts : Index → Nat) (index : Index)

local notation "OldV" => Finance.vocabulary (sources index) (depths index) (counts index)
local notation "NewV" => Family.vocabulary sources depths counts

def event (original : Finance.Event (sources index) (depths index) (counts index)) :
    Family.Event sources depths counts := .original index original

def origin {source : Finance.Event (sources index) (depths index) (counts index)}
    {claim : Finance.Claim (sources index) (depths index) (counts index)} :
    ObligationOrigin OldV source claim → ObligationOrigin NewV (event sources depths counts index source) ⟨index, claim⟩
  | .producerDemand demand .. => demand.obstruction.elim
  | .explicitCommitment receipt => .explicitCommitment ⟨claim, receipt, ⟨rfl⟩⟩
  | .standingMandate receipt | .acceptedTask receipt | .activeDependency receipt | .protectedRisk receipt => receipt.elim

def assumption {source : Finance.Event (sources index) (depths index) (counts index)}
    {bearer : Interface.Actors.Image (sources index) (depths index) (counts index)}
    {scope : Finance.Origin (sources index) (depths index) (counts index)} :
    BearerAssumption OldV source bearer scope →
      BearerAssumption NewV (event sources depths counts index source) ⟨index, bearer⟩ ⟨index, scope⟩
  | .accepted receipt => .accepted ⟨congrArg (Sigma.mk index) receipt.down.1, congrArg (Sigma.mk index) receipt.down.2⟩
  | .mandated receipt => receipt.elim

def payload (original : NativeAdmissionPayload OldV) : NativeAdmissionPayload NewV where
  sourceEvent := event sources depths counts index original.sourceEvent
  content := ⟨index, original.content⟩
  residual := original.residual
  bearer := ⟨index, original.bearer⟩
  beneficiary := ⟨index, original.beneficiary⟩
  scope := ⟨index, original.scope⟩
  lineage := ⟨index, original.lineage⟩
  anchor_scope_eq := congrArg (Sigma.mk index) original.anchor_scope_eq
  anchor_lineage_eq := congrArg (Sigma.mk index) original.anchor_lineage_eq
  origin := origin sources depths counts index original.origin
  authority := ⟨congrArg (Sigma.mk index) original.authority.down⟩
  assumption := assumption sources depths counts index original.assumption
  dischargeJurisdiction := ⟨congrArg (Sigma.mk index) original.dischargeJurisdiction.down⟩

def obligation (original : AdmittedObligation OldV) : AdmittedObligation NewV where
  content := ⟨index, original.content⟩
  residual := original.residual
  bearer := ⟨index, original.bearer⟩
  beneficiary := ⟨index, original.beneficiary⟩
  scope := ⟨index, original.scope⟩
  admission := {
    sourceEvent := event sources depths counts index original.admission.sourceEvent
    admittedBearer := ⟨index, original.admission.admittedBearer⟩
    admittedScope := ⟨index, original.admission.admittedScope⟩
    lineage := ⟨index, original.admission.lineage⟩
    anchor_scope_eq := congrArg (Sigma.mk index) original.admission.anchor_scope_eq
    anchor_lineage_eq := congrArg (Sigma.mk index) original.admission.anchor_lineage_eq
    origin := origin sources depths counts index original.admission.origin
    authority := ⟨congrArg (Sigma.mk index) original.admission.authority.down⟩
    assumption := assumption sources depths counts index original.admission.assumption }
  dischargeJurisdiction := ⟨congrArg (Sigma.mk index) original.dischargeJurisdiction.down⟩

#print axioms payload
#print axioms obligation

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Finance.Family.Embedding
