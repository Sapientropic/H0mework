import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.Budget.Escrow.Capacity.Selection.Counter.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment.Runtime
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
variable (paid : Built made index first)

def patchAt : (tick : Nat) → FiniteGeneratedLedgerWritePatchAt (rowSource made index first)
    (emitted made index first tick) ⟨supportAt made index (tick+1)⟩
  | 0 => paid.patch
  | tick+1 => Canonical.patch made index first (tick+1)

theorem patchAt_exact (tick : Nat) : patchAt made index first paid tick = Canonical.patch made index first tick := by
  cases tick with
  | zero => exact paid.patch_exact
  | succ tick => rfl

private def fromPatches (patches : (tick : Nat) → FiniteGeneratedLedgerWritePatchAt (rowSource made index first)
    (emitted made index first tick) ⟨supportAt made index (tick+1)⟩) : SourceNativeLedgerCompiler (source made index first) where
  IncidenceTransitionAt := fun _ _ _ => Unit
  ExactTransitionAt := RawRowAt made index first
  exact_incidence := fun _ => ()
  exact_lineage := fun _ => rfl
  writeRowSource := rowSource made index first
  terminalRowSource := terminalRowSource made index first
  compile := by
    intro tick occurrence
    cases occurrence_eq_emitted made index first occurrence
    exact .nativeWrite () rfl (emitted made index first (tick+1)) (patches tick).toLedgerWriteEvolution
  compilePatch := by
    intro tick occurrence
    cases occurrence_eq_emitted made index first occurrence
    exact ⟨patches tick,rfl⟩


def compiler : SourceNativeLedgerCompiler (source made index first) :=
  fromPatches made index first (patchAt made index first paid)

theorem compiler_exact : compiler made index first paid = Canonical.ledgerCompiler made index first := by
  have same : patchAt made index first paid = Canonical.patch made index first := funext (patchAt_exact made index first paid)
  unfold compiler
  rw [same]
  rfl

def ledgerSource : SourceNativeLedgerSource (N made index) (V made index) where
  source := source made index first
  ledgerCompiler := compiler made index first paid

def restructuringSource : SourceNativeRestructuringLedgerSource (N made index) (V made index) where
  source := source made index first
  compiler := {
    ledgerCompiler := compiler made index first paid
    restructuringLaw := Canonical.restructuringLaw made index first
    certifyRestructuring := by
      intro tick occurrence
      rw [compiler_exact]
      exact (Canonical.restructuringSource made index first).compiler.certifyRestructuring occurrence }

variable (component : SourceNativeProjectionLaw (oldRoot made index).toAuthoritativeRoot.toLedgerRoot.source)

def projectionLaw : SourceNativeProjectionLaw (ledgerSource made index first paid) where
  Projection := Canonical.Projection made index component
  ActiveAt := Canonical.ActiveAt made index first component
  InactiveAt := Canonical.InactiveAt made index first component
  classify := Canonical.classify made index first component
  PayloadAt := fun projection {tick} occurrence active => match projection with
    | .inl old => (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.PayloadAt old (parentOccurrence made index component tick) active.2
    | .inr .ledger => SourceNativeLedgerEvolutionAt (source made index first) occurrence
    | .inr .computation => Book made
  project := fun projection {tick} occurrence active => match projection with
    | .inl old => (parentRoot made index component).toAuthoritativeRoot.source.projectionLaw.project old (parentOccurrence made index component tick) active.2
    | .inr .ledger => (compiler made index first paid).compile occurrence
    | .inr .computation => generate made

def authoritySource : SourceNativeAuthoritySource (N made index) (V made index) where
  restructuringSource := restructuringSource made index first paid
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource made index first paid)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N made index)
  projectionLaw := projectionLaw made index first paid component

def baseRoot : SourceNativeLivingRootClosure (N made index) (V made index) where
  source := {
    base := authoritySource made index first paid component
    terminalHandoff := (authoritySource made index first paid component).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted made index first
  compiler_commutes := fun _ => rfl

def constructionLaw : SourceNativeProjectionLaw (baseRoot made index first paid component).toAuthoritativeRoot.toLedgerRoot.source where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {_} _ _ => Built made index first
  project := fun _ {_} _ _ => paid

def root := (baseRoot made index first paid component).withProjectionCoface (constructionLaw made index first paid component)

def visitAt : Nat → RootVisit (root made index first paid component).toAuthoritativeRoot.toRoot
  | 0 => (root made index first paid component).toAuthoritativeRoot.toRoot.initialVisit
  | tick+1 => (visitAt tick).next rfl

theorem visit_current (tick : Nat) : (visitAt made index first paid component tick).current = tick := by
  induction tick with
  | zero => rfl
  | succ tick ih => exact congrArg Nat.succ ih

def stateAt (tick : Nat) : SourceNativeLivingRootCurrentAt (N made index) :=
  ⟨V made index,root made index first paid component,.finite (visitAt made index first paid component tick)⟩

def process : SourceNativeLivingRootProcess (N made index) where
  State := Nat
  stateAt := stateAt made index first paid component
  stateAt_injective := by
    intro left right same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (N made index) => (⟨state.V.Current,state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have current := eq_of_heq (Sigma.mk.inj labels).2
    change (visitAt made index first paid component left).current = (visitAt made index first paid component right).current at current
    simpa only [visit_current] using current
  initial := 0
  successorAt := fun tick => ⟨tick+1,rfl,HEq.rfl⟩

def facade : SourceNativeLivingRuntimeFacade (N made index) where
  process := process made index first paid component
  FaceAt := fun _ => (root made index first paid component).toAuthoritativeRoot.source.projectionLaw.Projection
  componentAt := fun _ _ => (root made index first paid component).toAuthoritativeRoot.source.projectionLaw
  installationAt := fun _ _ => SourceNativeProjectionLaw.InstallationAt.refl _
  projectionAt := fun _ face => face

abbrev active := (facade made index first paid component).seed

def read : Built made index first :=
  match (facade made index first paid component).readoutAt (active made index first paid component) (.component ()) with
  | .inl value => value.2
  | .inr impossible => impossible.elim

def initialGenerated := (active made index first paid component).tick.generated

theorem the_paid_cached_patch_is_the_initial_compiler_patch :
    (compiler made index first paid).compilePatch (emitted made index first 0) = ⟨paid.patch,rfl⟩ := rfl

theorem the_actual_construction_and_cached_complete_patch_reach_this_root_and_next :
    let active := active made index first paid component
    (read made index first paid component).construction = execute made index first ∧
    (read made index first paid component).patch = paid.patch ∧
    HEq ((facade made index first paid component).readoutAt active (.component ()))
      (active.tick.generated.projectionOutcome (.component ())) ∧
    HEq active.tick.generated.wholeLedgerWriteBack
      ((root made index first paid component).toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt 0) ∧
    active.tick.nextCurrent = stateAt made index first paid component 1 := by
  have rooted := (facade made index first paid component).readoutAt_factorizes (active made index first paid component) (.component ())
  exact ⟨paid.generated,rfl,rooted.2.2.2.1,HEq.rfl,rooted.2.2.2.2⟩

end

inductive Installation where
  | empty (absent : first? made = none)
  | shortfall (first : First made) (generated : first? made = some first)
      (construction : Cursor made index first) (actual : construction = execute made index first)
      (unassembled : construction.output = none) (short : made.unused < units made index)
  | ready (first : First made) (generated : first? made = some first) (paid : Built made index first)

def install : Installation made index :=
  match generated : first? made with
  | none => .empty generated
  | some first => match produce made index first with
    | .ready paid => .ready first generated paid
    | .shortfall construction actual absent short => .shortfall first generated construction actual absent short

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Native.Online.Planning.Selection.Execution.Prepaid.Whole.Observation.Domain.Policy.SourceQuota.PublicPolicy.Counter.Paid.Automatic.Review.Enumeration.Joint.Responsibility.Canonical.Payment.Runtime
