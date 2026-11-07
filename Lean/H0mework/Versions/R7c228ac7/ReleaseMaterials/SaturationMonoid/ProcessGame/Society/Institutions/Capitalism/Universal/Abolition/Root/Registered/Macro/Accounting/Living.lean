import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit sourceDepth sourceCount : Nat)
  (start : Physical.Cursor Party Good Port Technology Instrument)
  (proposal : Compile.RawInput Party Good Port Technology Instrument) (sourcePosition : Nat)
  (review : Option (ReviewPhase.ContextAt input) := none)

local notation "W" => N (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "V₀" => V (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "src" => source (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "emit" => emitted (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "lc" => ledgerCompiler (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "lsrc" => ledgerSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "advance" => next (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "queue" => pending (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
local notation "material" => physical (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

inductive Projection
  | ledger | account | pending | physical | sourceInput | sourceExecution

def projectionLaw : SourceNativeProjectionLaw lsrc where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_current} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt src occurrence
    | .account => (Epoch.Finance.process input depth count).GeneratedState ×
        (Epoch.Finance.process input depth count).GeneratedState
    | .pending => List (Epoch.Finance.ActualItem input depth count) × List (Epoch.Finance.ActualItem input depth count)
    | .physical => Source.Program.RawCurrent Party Good Technology Instrument
    | .sourceInput => Mandatory.Report (review := review) input depth count prefixLimit renewalLimit start proposal
    | .sourceExecution => Source.Program.ExecutionResult Party Good Port Technology Instrument
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (lc).compile occurrence
    | .account => ⟨current.account, (advance current).account⟩
    | .pending => ⟨queue current, queue (advance current)⟩
    | .physical => (material current).raw
    | .sourceInput => Mandatory.produce (review := review) input depth count prefixLimit renewalLimit start proposal
    | .sourceExecution => Physical.execution input depth count prefixLimit renewalLimit
        (Inventory.eventCursor (review := review) input depth count prefixLimit renewalLimit start proposal)

def authoritySource : SourceNativeAuthoritySource W V₀ where
  restructuringSource := restructuringSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (restructuringSource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic W
  projectionLaw := projectionLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition

def livingRoot : SourceNativeLivingRootClosure W V₀ where
  source := {
    base := authoritySource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition
    terminalHandoff := (authoritySource (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emit
  compiler_commutes := by
    intro current
    change ((lc).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

theorem root_account_is_the_computed_native_next (current : (V₀).Current) :
    ((projectionLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).project
      .account (emit current) ()).2 = (advance current).account := rfl

theorem root_retains_original_proposal_and_pending (current : (V₀).Current) :
    ((projectionLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).project
      .sourceInput (emit current) ()).originalProposal = proposal ∧
    ((projectionLaw (review := review) input depth count prefixLimit renewalLimit sourceDepth sourceCount start proposal sourcePosition).project
      .pending (emit current) ()).1 = queue current := ⟨rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Accounting
