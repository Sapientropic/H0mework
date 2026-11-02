import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Living

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open DebtActivationWorld DebtActivationLedger DebtAdmissionFirstWrite
open Distributed.Recall.Information.Agency.Protocol
variable {P G O T I : Type} [DecidableEq P] [DecidableEq G] [DecidableEq O] [DecidableEq T] [DecidableEq I]
  {seed : Authority.Bound (Party := P) (Good := G) (Port := O) (Technology := T) (Instrument := I)}
  {input : Input seed} {prepared : Prepared input} {generatedSource : SourceQuota.Generated prepared}
  {catalogue : SourceQuota.Catalogue generatedSource.snapshot} {all : Candidates generatedSource catalogue} {owner : Ready all}
  (made : Generated owner) (index : Index prepared) (first : First made)

noncomputable section
variable (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source)

def visitAt : Nat → RootVisit (livingRoot made index first component).toAuthoritativeRoot.toRoot
  | 0 => (livingRoot made index first component).toAuthoritativeRoot.toRoot.initialVisit
  | tick+1 => (visitAt tick).next rfl

theorem visit_current (tick : Nat) : (visitAt made index first component tick).current = tick := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg Nat.succ ih

def stateAt (tick : Nat) : SourceNativeLivingRootCurrentAt (N made index) :=
  ⟨V made index,livingRoot made index first component,.finite (visitAt made index first component tick)⟩

def process : SourceNativeLivingRootProcess (N made index) where
  State := Nat
  stateAt := stateAt made index first component
  stateAt_injective := by
    intro left right same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (N made index) => (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have current := eq_of_heq (Sigma.mk.inj labels).2
    change (visitAt made index first component left).current = (visitAt made index first component right).current at current
    simpa only [visit_current] using current
  initial := 0
  successorAt := fun tick => ⟨tick+1,rfl,HEq.rfl⟩

def facade : SourceNativeLivingRuntimeFacade (N made index) where
  process := process made index first component
  FaceAt := fun _ => Projection made index component
  componentAt := fun _ _ => projectionLaw made index first component
  installationAt := fun _ _ => SourceNativeProjectionLaw.InstallationAt.refl (projectionLaw made index first component)
  projectionAt := fun _ face => face

abbrev active := (facade made index first component).seed

def readBook : Book made :=
  match (facade made index first component).readoutAt (active made index first component) (.inr .computation) with
  | .inl value => value.2
  | .inr impossible => impossible.elim

theorem the_initial_born_row_has_living_causal_authority :
    Nonempty (SourceNativeLivingTemporalCausalEntryAuthorityAt (livingRoot made index first component)
      (initialVisit made index first component) (initialBornEntry made index)) :=
  ⟨bornAuthority made index first component⟩

theorem the_complete_canonical_patch_and_born_row_generate_this_next :
    let active := active made index first component
    (readBook made index first component).entries = (generate made).entries ∧
    HEq ((facade made index first component).readoutAt active (.inr .computation))
      (active.tick.generated.projectionOutcome (.inr .computation)) ∧
    HEq active.tick.generated.wholeLedgerWriteBack (initialGenerated made index first component).wholeLedgerWriteBack ∧
    active.tick.nextCurrent = stateAt made index first component 1 := by
  have rooted := (facade made index first component).readoutAt_factorizes (active made index first component) (.inr .computation)
  exact ⟨rfl,rooted.2.2.2.1,HEq.rfl,rooted.2.2.2.2⟩

end

structure Installed where
  private mk ::
  scope : Index prepared
  scope_exact : scope = index
  first : First made
  generated : first? made = some first

def install? : Option (Installed made index) :=
  match generated : first? made with
  | none => none
  | some first => some ⟨index,rfl,first,generated⟩

namespace Installed
variable {made index} (installed : Installed made index)
noncomputable def root (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source) :=
  livingRoot made index installed.first component
noncomputable def next (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source) :
    SourceNativeLivingRootCurrentAt (N made index) :=
  (active made index installed.first component).tick.nextCurrent
noncomputable def initialRow (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source) :=
  initialBornRow made index installed.first component
end Installed

theorem empty_work_keeps_original_authority (empty : made.execution.work = []) : install? made index = none := by
  unfold install?
  have no_birth : first? made = none := by simpa only [generate] using empty_work_has_no_birth made empty
  split
  · rfl
  · rename_i first born
    rw [no_birth] at born
    cases born

theorem every_paid_nonempty_report_has_a_canonical_installation (positive : 0 < made.execution.work.length) :
    ∃ installed,install? made index = some installed := by
  obtain ⟨first,born,_⟩ := every_nonempty_paid_run_generates_its_first_write made positive
  change first? made = some first at born
  unfold install?
  split
  · rename_i absent
    rw [absent] at born
    cases born
  · exact ⟨_,rfl⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical
