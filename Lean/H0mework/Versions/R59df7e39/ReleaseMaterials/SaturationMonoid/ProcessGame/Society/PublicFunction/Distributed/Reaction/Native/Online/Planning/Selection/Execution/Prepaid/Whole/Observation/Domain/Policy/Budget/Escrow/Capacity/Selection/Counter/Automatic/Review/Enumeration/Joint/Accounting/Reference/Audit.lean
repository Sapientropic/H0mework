import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Accounting.Reference
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Reference.Payment.Audit
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input}


namespace CandidateSupport
noncomputable section
variable {after : Prepared input} {Audit : Type} (audit : Audit)
  {activeSource : SourceQuota.Generated after} {activeCatalogue : SourceQuota.Catalogue activeSource.snapshot}
  {activeAll : Candidates activeSource activeCatalogue} (chosen : Candidate activeAll) (index : Index after)
  (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot chosen.report.2 index).toAuthoritativeRoot.toLedgerRoot.source)

def auditLaw : SourceNativeProjectionLaw
    (Responsibility.Canonical.Payment.Runtime.root chosen.report.2 index chosen.first (chosen.paid index) component).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Audit
  project := fun _ {_} _ _ => audit

def root :=
  (Responsibility.Canonical.Payment.Runtime.root chosen.report.2 index chosen.first (chosen.paid index) component).withProjectionCoface
    (auditLaw audit chosen index component)

def visitAt : (tick : Nat) → RootVisit (root audit chosen index component).toAuthoritativeRoot.toRoot
  | 0 => (root audit chosen index component).toAuthoritativeRoot.toRoot.initialVisit
  | tick+1 => (visitAt tick).next rfl
theorem visit_current (tick : Nat) : (visitAt audit chosen index component tick).current = tick := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg Nat.succ ih
def stateAt (tick : Nat) : SourceNativeLivingRootCurrentAt (Responsibility.Canonical.N chosen.report.2 index) :=
  ⟨Responsibility.Canonical.V chosen.report.2 index,root audit chosen index component,.finite (visitAt audit chosen index component tick)⟩
def process : SourceNativeLivingRootProcess (Responsibility.Canonical.N chosen.report.2 index) where
  State := Nat
  stateAt := stateAt audit chosen index component
  stateAt_injective := by
    intro left right same
    have labels := congrArg (fun state : SourceNativeLivingRootCurrentAt (Responsibility.Canonical.N chosen.report.2 index) =>
      (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents := eq_of_heq (Sigma.mk.inj labels).2
    change (visitAt audit chosen index component left).current = (visitAt audit chosen index component right).current at currents
    simpa only [visit_current] using currents
  initial := 0
  successorAt := fun tick => ⟨tick+1,rfl,HEq.rfl⟩
def facade : SourceNativeLivingRuntimeFacade (Responsibility.Canonical.N chosen.report.2 index) where
  process := process audit chosen index component
  FaceAt := fun _ => (root audit chosen index component).toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun _ _ => (root audit chosen index component).toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => SourceNativeProjectionLaw.InstallationAt.refl _
  projectionAt := fun _ face => face
abbrev active := (facade audit chosen index component).seed
def read : Audit :=
  match (facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()) with
  | .inl value => value.2
  | .inr impossible => impossible.elim
theorem the_actual_payload_is_active_with_whole_ledger_and_next :
    read audit chosen index component = audit ∧
    HEq ((facade audit chosen index component).readoutAt (active audit chosen index component) (.component ()))
      ((active audit chosen index component).tick.generated.projectionOutcome (.component ())) ∧
    HEq (active audit chosen index component).tick.generated.wholeLedgerWriteBack
      ((root audit chosen index component).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt 0) ∧
    (active audit chosen index component).tick.nextCurrent = stateAt audit chosen index component 1 := by
  have rooted := (facade audit chosen index component).readoutAt_factorizes (active audit chosen index component) (.component ())
  exact ⟨rfl,rooted.2.2.2.1,HEq.rfl,rooted.2.2.2.2⟩
def next : AuthorityCurrent :=
  ⟨Responsibility.Canonical.N chosen.report.2 index,(active audit chosen index component).tick.nextCurrent⟩
end
end CandidateSupport
namespace Support
noncomputable section
variable {after : Prepared input} {Audit : Type} (audit : Audit)
  {activeSource : SourceQuota.Generated after} {activeCatalogue : SourceQuota.Catalogue activeSource.snapshot}
  {activeAll : Candidates activeSource activeCatalogue} {activeItems : List (Report activeAll)} (chosen : Selected activeItems) (index : Index after)
  (component : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot chosen.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source)
abbrev auditLaw := CandidateSupport.auditLaw audit chosen.policy index component
abbrev root := CandidateSupport.root audit chosen.policy index component
abbrev visitAt := CandidateSupport.visitAt audit chosen.policy index component
abbrev visit_current := CandidateSupport.visit_current audit chosen.policy index component
abbrev stateAt := CandidateSupport.stateAt audit chosen.policy index component
abbrev process := CandidateSupport.process audit chosen.policy index component
abbrev facade := CandidateSupport.facade audit chosen.policy index component
abbrev active := CandidateSupport.active audit chosen.policy index component
abbrev read := CandidateSupport.read audit chosen.policy index component
abbrev the_actual_payload_is_active_with_whole_ledger_and_next := CandidateSupport.the_actual_payload_is_active_with_whole_ledger_and_next audit chosen.policy index component
abbrev next := CandidateSupport.next audit chosen.policy index component
end
end Support

def law {Audit : Type} (audit : Audit) {units position : Nat} (result : Result prepared units position) (index : Index result.after) :
    SourceNativeProjectionLaw (Online.Runtime.root (result.cursor index)).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Audit
  project := fun _ {_} _ _ => audit

private noncomputable def nextFor {Audit : Type} (audit : Audit) {original : Prepared input} {units position : Nat}
    (result : Result original units position) (menu : DomainResult result.after) (items : ReportsFor menu) {oldUnits : Nat}
    (parent : Prepayment.WorkFor menu items oldUnits) {capacity : Nat} (tail : WorkFor menu items parent position capacity) (index : Index result.after)
    (component : SourceNativeProjectionLaw (Online.Runtime.root (endpointFor menu items parent tail index)).toAuthoritativeRoot.toLedgerRoot.source) : AuthorityCurrent := by
  cases menu with
  | empty => exact originalNext (endpointFor _ items parent tail index) component
  | blocked => exact originalNext (endpointFor _ items parent tail index) component
  | ready source catalogue generated all =>
    cases chosen : tail.endpoint.selection items position with
    | none => exact originalNext (endpointFor _ items parent tail index) component
    | some answer =>
      have same : endpointFor (.ready source catalogue generated all) items parent tail index = answer.selected.policy.report.2.endpoint index := by
        dsimp only [endpointFor];rw [chosen]
      let original : SourceNativeProjectionLaw (Responsibility.Canonical.oldRoot answer.selected.policy.report.2 index).toAuthoritativeRoot.toLedgerRoot.source :=
        Eq.mp (congrArg (fun value : Binding.NativeCursor result.after.saved[index].point =>
          SourceNativeProjectionLaw (Online.Runtime.root value).toAuthoritativeRoot.toLedgerRoot.source) same) component
      exact Support.next audit answer.selected index original
/-- The root is selected by this result's own tail, never supplied by the payload caller. -/
noncomputable def next {Audit : Type} (audit : Audit) {units position : Nat} (result : Result prepared units position) (index : Index result.after) : AuthorityCurrent := by
  cases result with
  | empty absent => exact originalNext ((Result.empty absent).cursor index) (law audit (Result.empty absent) index)
  | unpaid funding generated failedAt failed => exact originalNext ((Result.unpaid funding generated failedAt failed).cursor index) (law audit (Result.unpaid funding generated failedAt failed) index)
  | ready made => exact nextFor audit (Result.ready made) made.parent.body.menu made.parent.body.reports made.parent.run made.tail index (law audit (Result.ready made) index)
end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Accounting.Reference.Payment.Audit
