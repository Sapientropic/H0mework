import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission.Keys

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {proposal : Compile.RawInput Party Good Port Technology Instrument} {sourcePosition : Nat}
  {review : Option (ReviewPhase.ContextAt input)}
  (frame : NativeFrame (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
  {origin : frame.V.Current}
  (registered : HeadRegistration (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition frame origin)

inductive OwnProjection
  | ledger | account | admission

abbrev Projection := frame.root.toAuthoritativeRoot.source.projectionLaw.Projection ⊕ OwnProjection

def ActiveAt (projection : Projection frame) {current : Current frame registered}
    (_occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt old (frame.root.emitted current.1)
  | .inr _ => Unit

def InactiveAt (projection : Projection frame) {current : Current frame registered}
    (_occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) : Type :=
  match projection with
  | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.InactiveAt old (frame.root.emitted current.1)
  | .inr _ => PEmpty

def classify (projection : Projection frame) {current : Current frame registered}
    (occurrence : (source frame registered).toRootSource.actual.OccurrenceAt current) :
    ActiveAt frame registered projection occurrence ⊕ InactiveAt frame registered projection occurrence :=
  match projection with
  | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.classify old (frame.root.emitted current.1)
  | .inr _ => .inl ()

def projectionLaw : SourceNativeProjectionLaw (ledgerSource frame registered) where
  Projection := Projection frame
  ActiveAt := ActiveAt frame registered
  InactiveAt := InactiveAt frame registered
  classify := classify frame registered
  PayloadAt := fun projection {current} occurrence active => match projection with
    | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.PayloadAt old (frame.root.emitted current.1) active
    | .inr .ledger => SourceNativeLedgerEvolutionAt (source frame registered) occurrence
    | .inr .account => (Epoch.Finance.process input depth count).GeneratedState × (Epoch.Finance.process input depth count).GeneratedState
    | .inr .admission => registered.law.DebtState
  project := fun projection {current} occurrence active => match projection with
    | .inl old => frame.root.toAuthoritativeRoot.source.projectionLaw.project old (frame.root.emitted current.1) active
    | .inr .ledger => (ledgerCompiler frame registered).compile occurrence
    | .inr .account => ⟨frame.account current.1, frame.account (frame.next current.1)⟩
    | .inr .admission => state frame registered current.2

def authoritySource : SourceNativeAuthoritySource (N frame registered) (V frame registered) where
  restructuringSource := restructuringSource frame registered
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource frame registered)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N frame registered)
  projectionLaw := projectionLaw frame registered

def livingRoot : SourceNativeLivingRootClosure (N frame registered) (V frame registered) where
  source := {
    base := authoritySource frame registered
    terminalHandoff := (authoritySource frame registered).emptyFaithfulTerminalHandoff (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted frame registered
  compiler_commutes := by
    intro current
    change ((ledgerCompiler frame registered).compile (emitted frame registered current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

theorem inherited_projection_is_the_original_source (projection : frame.root.toAuthoritativeRoot.source.projectionLaw.Projection)
    (current : Current frame registered)
    (active : frame.root.toAuthoritativeRoot.source.projectionLaw.ActiveAt projection (frame.root.emitted current.1)) :
    HEq ((projectionLaw frame registered).project (.inl projection) (emitted frame registered current) active)
      (frame.root.toAuthoritativeRoot.source.projectionLaw.project projection (frame.root.emitted current.1) active) := HEq.rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Admission
