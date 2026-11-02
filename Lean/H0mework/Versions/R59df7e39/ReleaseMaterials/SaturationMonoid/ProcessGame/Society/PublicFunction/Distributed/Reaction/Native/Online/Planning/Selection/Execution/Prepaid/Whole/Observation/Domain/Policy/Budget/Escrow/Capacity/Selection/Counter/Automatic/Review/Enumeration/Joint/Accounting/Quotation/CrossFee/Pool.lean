import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Pool
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}

/-- The menu keeps its own dependent candidate family; no two inner ledgers are identified. -/
def Local {after : Prepared input} : DomainResult after → Type
  | .empty .. | .blocked .. => Empty
  | .ready _ _ _ all => Accounting.Candidate all

def captured {after : Prepared input} : (menu : DomainResult after) → (items : ReportsFor menu) →
    {units : Nat} → Prepayment.WorkFor menu items units → List (Local menu)
  | .empty ..,_,_,_ | .blocked ..,_,_,_ => []
  | .ready ..,_,_,parent => match Reference.fromCursor parent.endpoint with
    | none => []
    | some cache => cache.pool

def view {after : Prepared input} : (menu : DomainResult after) → Local menu →
    (index : Index after) → Automatic.Local after.saved[index].point
  | .empty ..,impossible,_ | .blocked ..,impossible,_ => impossible.elim
  | .ready ..,candidate,index => candidate.policy.policy.view index

def work {after : Prepared input} : (menu : DomainResult after) → Local menu → Index after → Nat
  | .empty ..,impossible,_ | .blocked ..,impossible,_ => impossible.elim
  | .ready ..,candidate,index => candidate.work index

def credit {after : Prepared input} : (menu : DomainResult after) → Local menu → Index after → Nat
  | .empty ..,impossible,_ | .blocked ..,impossible,_ => impossible.elim
  | .ready ..,candidate,index => candidate.credit index

def PolicyFor {units position : Nat} : Reference.Payment.Result prepared units position → Type
  | .empty .. | .unpaid .. => Empty
  | .ready made => Local made.parent.body.menu

def casePool {units position : Nat} : (payment : Reference.Payment.Result prepared units position) → List (PolicyFor payment)
  | .empty .. | .unpaid .. => []
  | .ready made => captured made.parent.body.menu made.parent.body.reports made.parent.run

def caseView {units position : Nat} : (payment : Reference.Payment.Result prepared units position) → PolicyFor payment →
    (index : Index prepared) → Automatic.Local prepared.saved[index].point
  | .empty ..,impossible,_ | .unpaid ..,impossible,_ => impossible.elim
  | .ready made,candidate,index => Automatic.paid_point made.parent.funding index ▸
      view made.parent.body.menu candidate (Automatic.paidIndex made.parent.funding index)

def caseWork {units position : Nat} : (payment : Reference.Payment.Result prepared units position) → PolicyFor payment → Index prepared → Nat
  | .empty ..,impossible,_ | .unpaid ..,impossible,_ => impossible.elim
  | .ready made,candidate,index => work made.parent.body.menu candidate (Automatic.paidIndex made.parent.funding index)

def caseCredit {units position : Nat} : (payment : Reference.Payment.Result prepared units position) → PolicyFor payment → Index prepared → Nat
  | .empty ..,impossible,_ | .unpaid ..,impossible,_ => impossible.elim
  | .ready made,candidate,index => credit made.parent.body.menu candidate (Automatic.paidIndex made.parent.funding index)

def invoiceWork {units position : Nat} : Reference.Payment.Result prepared units position → Nat
  | .empty .. | .unpaid .. => 0
  | .ready made => made.parent.spent+made.spent

def invoiceCredit {units position : Nat} : Reference.Payment.Result prepared units position → Nat
  | .empty .. | .unpaid .. => 0
  | .ready made => made.unused

structure Pick (prepared : Prepared input) (position : Nat) where
  private mk ::
  branch : CrossFee.Branch prepared position
  candidate : PolicyFor branch.alternative.2.payment
  listed : candidate ∈ casePool branch.alternative.2.payment

def Pick.fromListed {position : Nat} (branch : CrossFee.Branch prepared position)
    (candidate : PolicyFor branch.alternative.2.payment) (listed : candidate ∈ casePool branch.alternative.2.payment) : Pick prepared position :=
  ⟨branch,candidate,listed⟩

def picksFor {position : Nat} (branch : CrossFee.Branch prepared position) : List (Pick prepared position) :=
  (casePool branch.alternative.2.payment).attach.map fun entry => ⟨branch,entry.val,entry.property⟩
def collect {position : Nat} (audit : CrossFee.Result prepared position) : List (Pick prepared position) :=
  audit.branches.flatMap picksFor

namespace Pick
variable {position : Nat} (pick : Pick prepared position)
def view (index : Index prepared) : Automatic.Local prepared.saved[index].point :=
  Automatic.paid_point pick.branch.outer.funding index ▸ caseView pick.branch.alternative.2.payment pick.candidate
    (Automatic.paidIndex pick.branch.outer.funding index)
def work (index : Index prepared) := caseWork pick.branch.alternative.2.payment pick.candidate (Automatic.paidIndex pick.branch.outer.funding index)
def credit (index : Index prepared) := caseCredit pick.branch.alternative.2.payment pick.candidate (Automatic.paidIndex pick.branch.outer.funding index)
def invoiceWork := CrossFee.Pool.invoiceWork pick.branch.alternative.2.payment
def invoiceCredit := CrossFee.Pool.invoiceCredit pick.branch.alternative.2.payment
end Pick

variable {position : Nat} {after : Prepared input} {source : SourceQuota.Generated after}
  {catalogue : SourceQuota.Catalogue source.snapshot} {all : Candidates source catalogue}
theorem capture_reads_the_original_paid_cache (domain : source.result = .domain catalogue) (items : List (Accounting.Report all)) {units : Nat}
    (parent : Prepayment.WorkFor (.ready source catalogue domain all) items units)
    (cache : Reference.Cache items) (actual : Reference.fromCursor parent.endpoint = some cache) :
    captured (.ready source catalogue domain all) items parent = cache.pool := by
  simp only [captured,actual]

theorem every_captured_candidate_is_in_the_joint_pool (audit : CrossFee.Result prepared position)
    (branch : CrossFee.Branch prepared position) (original : branch ∈ audit.branches)
    (candidate : PolicyFor branch.alternative.2.payment) (listed : candidate ∈ casePool branch.alternative.2.payment) :
    (⟨branch,candidate,listed⟩ : Pick prepared position) ∈ collect audit :=
  List.mem_flatMap.mpr ⟨branch,original,List.mem_map.mpr ⟨⟨candidate,listed⟩,List.mem_attach _ _,rfl⟩⟩


namespace Payload
variable {after : Prepared input} {source : SourceQuota.Generated after} {catalogue : SourceQuota.Catalogue source.snapshot}
  {all : Candidates source catalogue} {Audit : Type} (audit : Audit) (candidate : Accounting.Candidate all) (index : Index after)
def law : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot candidate.report.2 index).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Audit
  project := fun _ {_} _ _ => audit
end Payload

noncomputable def menuNext {after : Prepared input} {Audit : Type} (audit : Audit) :
    (menu : DomainResult after) → Local menu → Index after → AuthorityCurrent
  | .empty ..,impossible,_ | .blocked ..,impossible,_ => impossible.elim
  | .ready ..,candidate,index => Reference.Payment.Audit.CandidateSupport.next audit candidate index (Payload.law audit candidate index)
noncomputable def caseNext {units position : Nat} {Audit : Type} (audit : Audit) :
    (payment : Reference.Payment.Result prepared units position) → PolicyFor payment → Index prepared → AuthorityCurrent
  | .empty ..,impossible,_ | .unpaid ..,impossible,_ => impossible.elim
  | .ready made,candidate,index => menuNext audit made.parent.body.menu candidate (Automatic.paidIndex made.parent.funding index)
noncomputable def Pick.next {position : Nat} {Audit : Type} (audit : Audit) (pick : Pick prepared position) (index : Index prepared) : AuthorityCurrent :=
  caseNext audit pick.branch.alternative.2.payment pick.candidate (Automatic.paidIndex pick.branch.outer.funding index)

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Quotation.CrossFee.Pool
