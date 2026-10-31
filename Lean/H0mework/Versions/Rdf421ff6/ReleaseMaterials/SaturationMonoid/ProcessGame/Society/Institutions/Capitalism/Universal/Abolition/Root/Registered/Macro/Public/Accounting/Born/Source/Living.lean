import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (prior : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)
  (origin : Accounting.Current input depth count anchor)
  (registered : Registration input depth count prefixLimit renewalLimit oldPast start origin)


local notation "N₀" => Born.N prior origin registered
local notation "V₀" => V prior origin registered
local notation "src" => source prior origin registered
local notation "emit" => emitted prior origin registered
local notation "advance" => next origin registered
local notation "lc" => ledgerCompiler prior origin registered
local notation "lsrc" => ledgerSource prior origin registered
inductive Projection
  | ledger | account | pending | physical | sourceInput | sourceExecution | sourceResult | interpreter

def projectionLaw : SourceNativeProjectionLaw lsrc where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {_current} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt src occurrence
    | .account => (Epoch.Finance.process input depth count).GeneratedState ×
        (Epoch.Finance.process input depth count).GeneratedState
    | .pending => List (Epoch.Finance.ActualItem input depth count)
    | .physical => Actual.Current (Party := Party) (Good := Good) (Port := Port)
        (Technology := Technology) (Instrument := Instrument)
    | .sourceInput => Epoch.Interface.Tag input depth count
    | .sourceExecution => Source.Program.ExecutionResult Party Good Port Technology Instrument
    | .sourceResult => Physical.Public.ResultAt input
        (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past) start.incoming
    | .interpreter => Source.Program.RawLaw Party Good Port Technology Instrument
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (lc).compile occurrence
    | .account => ⟨account origin registered current, account origin registered (advance current)⟩
    | .pending => (Accounting.items input depth count prefixLimit renewalLimit oldPast start).drop (position origin registered current)
    | .physical => physical origin registered current
    | .sourceInput => Accounting.tag input depth count prefixLimit renewalLimit oldPast start
    | .sourceExecution => Physical.Public.execution input depth count prefixLimit renewalLimit oldPast start
    | .sourceResult => Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast start
    | .interpreter => Physical.Public.interpreter input

def authoritySource : SourceNativeAuthoritySource N₀ V₀ where
  restructuringSource := restructuringSource prior origin registered
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (restructuringSource prior origin registered) (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic N₀
  projectionLaw := projectionLaw prior origin registered

def livingRoot : SourceNativeLivingRootClosure N₀ V₀ where
  source := {
    base := authoritySource prior origin registered
    terminalHandoff := (authoritySource prior origin registered).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emit
  compiler_commutes := by
    intro current
    change ((lc).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

#print axioms livingRoot

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Accounting.Born.Source
