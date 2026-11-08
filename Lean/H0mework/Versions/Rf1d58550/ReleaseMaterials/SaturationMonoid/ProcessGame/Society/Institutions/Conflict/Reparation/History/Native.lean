import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Birth.Flow
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Quantities.Execution.Step

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Root.Registered.Macro
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]

local notation "C" => Root.Cut Party Good Port Technology Instrument
local notation "Proposal" => Option (Compile.RawInput Party Good Port Technology Instrument)

abbrev cutSupport (cut : C) := cut.native.frame.sourceSupport cut.native.visit.current

def nativeWrite {input : ProgrammeSource.Input Party Good Port Technology Instrument}
    {depth count prefixLimit renewalLimit oldPast start}
    (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
    (current : frame.V.Current) :
    {whole : LedgerWriteEvolutionAt frame.N ⟨frame.sourceSupport current⟩
      ⟨frame.sourceSupport (frame.successor current).targetCurrent⟩ // Financial.Installation.KeepsKeys whole} := by
  have target := congrArg (fun event => frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf event)
    (frame.target_occurrence current)
  change frame.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
    (frame.successor current).targetOccurrence = frame.sourceSupport (frame.successor current).targetCurrent at target
  exact target ▸ ⟨(frame.successor current).ledgerEvolution, frame.successor_keys current⟩

def hasWrite {input : ProgrammeSource.Input Party Good Port Technology Instrument}
    {depth count prefixLimit renewalLimit oldPast start}
    (frame : Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
    (current : frame.V.Current) : Bool :=
  match frame.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt current with
  | .nativeWrite .. | .relationWrite .. => true
  | _ => false

/-- Only an actual finance admission changes the native network type. -/
def NoFinancialBirth (source : C) : Prop :=
  ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual ∨
    Public.Accounting.registration? source.native.input source.native.depth source.native.count
      source.native.prefixLimit source.native.renewalLimit source.native.oldPast source.native.start
      source.native.actual.actual = none

structure NativeEdge (source target : C) where
  sameNetwork : target.native.frame.N = source.native.frame.N
  whole : LedgerWriteEvolutionAt source.native.frame.N ⟨cutSupport source⟩
    ⟨sameNetwork ▸ cutSupport target⟩
  keys : Financial.Installation.KeepsKeys whole
  writes : Bool

private def ordinaryEdge (source : C) : NativeEdge source source.ordinary where
  sameNetwork := rfl
  whole := (nativeWrite source.native.frame source.native.visit.current).val
  keys := (nativeWrite source.native.frame source.native.visit.current).property
  writes := hasWrite source.native.frame source.native.visit.current

private def transitionEdge (source : C)
    (complete : ¬ Public.Inquiry.HasWork source.native.frame source.native.actual.actual) :
    NativeEdge source (Evolving.Epoch.Transition.next source complete) := by
  let frame := Evolving.Epoch.Transition.fullFrame source
  let initial := (Evolving.Epoch.Transition.initial source).current
  let body := nativeWrite frame initial
  have same : frame.sourceSupport initial = cutSupport source :=
    Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Direct.the_target_starts_with_the_same_whole_source_support
      source.native.full source.native.sourceActual source.executionReader
  have aligned :
      {whole : LedgerWriteEvolutionAt frame.N ⟨cutSupport source⟩
        ⟨frame.sourceSupport (frame.successor initial).targetCurrent⟩ // Financial.Installation.KeepsKeys whole} :=
    same ▸ body
  exact ⟨rfl, aligned.val, aligned.property, hasWrite frame initial⟩

def selectedEdge (source : C) (safe : NoFinancialBirth source) : NativeEdge source source.advance := by
  by_cases work : Public.Inquiry.HasWork source.native.frame source.native.actual.actual
  · have absent := safe.resolve_left (fun complete => complete work)
    have selected : source.advance = source.ordinary := by
      unfold Evolving.Epoch.Current.advance
      rw [dif_pos work, absent]
    exact selected.symm ▸ ordinaryEdge source
  · exact (source.advance_eq_epoch work).symm ▸ transitionEdge source work

def originalEdge (source : C) (proposal : Proposal)
    (safe : NoFinancialBirth (Quantities.Execution.query source proposal)) :
    NativeEdge source (Quantities.Execution.next source proposal) := by
  cases proposal with
  | none => exact selectedEdge source safe
  | some raw =>
    let queried := Quantities.Execution.query source (some raw)
    let edge := selectedEdge queried safe
    exact ⟨edge.sameNetwork, edge.whole, edge.keys, edge.writes⟩

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
