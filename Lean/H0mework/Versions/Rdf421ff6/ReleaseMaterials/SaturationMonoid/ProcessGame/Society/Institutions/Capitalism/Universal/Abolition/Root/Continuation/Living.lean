import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation.Compiler

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument)
  (frame : Financial.Installation.Runtime.Frame input)
  (request : Request Party Good Port Technology Instrument)

structure ExecutionAt (current : (V input frame request).Current) where
  before : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  instruction : Request Party Good Port Technology Instrument
  after : Data (Party := Party) (Good := Good) (Technology := Technology) (Instrument := Instrument)
  before_exact : before = current
  instruction_exact : instruction = request
  actual_target : after = input.law.step current request

def execution (current : (V input frame request).Current) : ExecutionAt input frame request current :=
  ⟨current, request, next input request current, rfl, rfl, rfl⟩

inductive Projection
  | ledger | execution | account | pending | originalHistory

def projectionLaw : SourceNativeProjectionLaw (ledgerSource input frame request) where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => PEmpty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} occurrence _ => match projection with
    | .ledger => SourceNativeLedgerEvolutionAt (source input frame request) occurrence
    | .execution => ExecutionAt input frame request current
    | .account => (Financial.process input).GeneratedState
    | .pending => Financial.Installation.Cursor.PendingInventory input (frame.cursor input)
    | .originalHistory => RootVisit frame.native.root.toAuthoritativeRoot.toRoot
  project := fun projection {current} occurrence _ => match projection with
    | .ledger => (ledgerCompiler input frame request).compile occurrence
    | .execution => execution input frame request current
    | .account => (frame.cursor input).account
    | .pending => Financial.Installation.Cursor.pendingInventory input (frame.cursor input)
    | .originalHistory => frame.visit

def authoritySource : SourceNativeAuthoritySource (N input frame) (V input frame request) where
  restructuringSource := restructuringSource input frame request
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource input frame request)
    (fun _ => ⟨fun impossible => impossible.elim⟩)
  lawSurface := TheoryState.rootSemantic (N input frame)
  projectionLaw := projectionLaw input frame request

def livingRoot : SourceNativeLivingRootClosure (N input frame) (V input frame request) where
  source := {
    base := authoritySource input frame request
    terminalHandoff := (authoritySource input frame request).emptyFaithfulTerminalHandoff
      (fun _ => ⟨fun impossible => impossible.elim⟩) }
  emitted := emitted input frame request
  compiler_commutes := fun _ => rfl

theorem actual_execution_and_account_share_the_original_root
    (current : (V input frame request).Current) :
    ((projectionLaw input frame request).project .execution (emitted input frame request current) ()).after =
        (V input frame request).nativeTarget (current := current) () ∧
      (projectionLaw input frame request).project .account (emitted input frame request current) () =
        (frame.cursor input).account ∧
      (projectionLaw input frame request).project .pending (emitted input frame request current) () =
        Financial.Installation.Cursor.pendingInventory input (frame.cursor input) ∧
      (projectionLaw input frame request).project .originalHistory (emitted input frame request current) () =
        frame.visit := ⟨rfl, rfl, rfl, rfl⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Continuation
