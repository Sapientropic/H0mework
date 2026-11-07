import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source.Authority

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (depth count prefixLimit renewalLimit : Nat)
  (oldPast : List (Compile.RawInput Party Good Port Technology Instrument))
  (start : Physical.Cursor Party Good Port Technology Instrument)
  {world : WorldRelationNetwork} {anchor : (Epoch.Finance.process input depth count).GeneratedState}
  (family : Epoch.Finance.Future.Continuation.AccountFamily input depth count world anchor)

local notation "C" => Accounting.Current input depth count anchor
local notation "supp" => Accounting.support input depth count family
local notation "advance" => Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start
local notation "evolution" => Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start family

local notation "src" => source input depth count prefixLimit renewalLimit oldPast start family
local notation "emit" => emitted input depth count prefixLimit renewalLimit oldPast start family
local notation "Seed" => RowSeed input depth count prefixLimit renewalLimit oldPast start family
local notation "beforeRow" => sourceRow input depth count prefixLimit renewalLimit oldPast start family
local notation "afterRow" => targetRow input depth count prefixLimit renewalLimit oldPast start family
local notation "enumerate" => rowEnum input depth count prefixLimit renewalLimit oldPast start family

local notation "V₀" => V input depth count prefixLimit renewalLimit oldPast start family
local notation "rawRows" => RawRowAt input depth count prefixLimit renewalLimit oldPast start family
local notation "rowCompiler" => rowSource input depth count prefixLimit renewalLimit oldPast start family
local notation "wholePatch" => patch input depth count prefixLimit renewalLimit oldPast start family
local notation "sourceWrites" => writes input depth count prefixLimit renewalLimit oldPast start

local notation "lc" => ledgerCompiler input depth count prefixLimit renewalLimit oldPast start family
local notation "lsrc" => ledgerSource input depth count prefixLimit renewalLimit oldPast start family

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
    | .physical => Abolition.Root.Actual.Current (Party := Party) (Good := Good) (Port := Port)
        (Technology := Technology) (Instrument := Instrument)
    | .sourceInput => Epoch.Interface.Tag input depth count
    | .sourceExecution => Source.Program.ExecutionResult Party Good Port Technology Instrument
    | .sourceResult => Physical.Public.ResultAt input
        (Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast start.past) start.incoming
    | .interpreter => Source.Program.RawLaw Party Good Port Technology Instrument
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (lc).compile occurrence
    | .account => ⟨current.account, (advance current).account⟩
    | .pending => (Accounting.items input depth count prefixLimit renewalLimit oldPast start).drop current.position
    | .physical => Accounting.physical input depth count prefixLimit renewalLimit oldPast start current
    | .sourceInput => Accounting.tag input depth count prefixLimit renewalLimit oldPast start
    | .sourceExecution => Physical.Public.execution input depth count prefixLimit renewalLimit oldPast start
    | .sourceResult => Physical.Public.resultAt input depth count prefixLimit renewalLimit oldPast start
    | .interpreter => Physical.Public.interpreter input

def authoritySource : SourceNativeAuthoritySource world V₀ where
  restructuringSource := restructuringSource input depth count prefixLimit renewalLimit oldPast start family
  eventInventoryAdmission := .reflOfNoFaithfulTerminal
    (restructuringSource input depth count prefixLimit renewalLimit oldPast start family)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic world
  projectionLaw := projectionLaw input depth count prefixLimit renewalLimit oldPast start family

def livingRoot : SourceNativeLivingRootClosure world V₀ where
  source := {
    base := authoritySource input depth count prefixLimit renewalLimit oldPast start family
    terminalHandoff := (authoritySource input depth count prefixLimit renewalLimit oldPast start family).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emit
  compiler_commutes := by
    intro current
    change ((lc).compile (emit current)).CommutesWith _
    dsimp only [ledgerCompiler, sourcePacket]
    split <;> rfl

#print axioms livingRoot

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Source
