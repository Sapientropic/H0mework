import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix.Root

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

private theorem castDestination {N : WorldRelationNetwork} {α : Type}
    (support : α → N.Support) {before : N.Support} {left right : α} (same : left = right)
    (effect : LedgerWriteEvolutionAt N ⟨before⟩ ⟨support left⟩) :
    HEq (Eq.mp (congrArg (fun value => LedgerWriteEvolutionAt N ⟨before⟩ ⟨support value⟩) same) effect).destination effect.destination := by
  cases same
  rfl

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (cut : frame.V.Current)

theorem wholeDestination_is_the_original_effect (current : frame.V.Current) :
    HEq (frame.wholeEvolution current).destination (frame.successor current).ledgerEvolution.destination :=
  castDestination _ (frame.target_occurrence current) (frame.successor current).ledgerEvolution

private def ImageKeys (phase : Option frame.V.Current)
    (image : SourceNativeLedgerEvolutionAt (Sparse.Compiler.source (code frame cut)) (Sparse.Compiler.emitted (code frame cut) phase)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (Sparse.Compiler.emitted (code frame cut) phase) image,
    Financial.Installation.KeepsKeys actual.ledgerEvolution

theorem successor_keys (phase : Option frame.V.Current) :
    Financial.Installation.KeepsKeys (Sparse.Compiler.successor (code frame cut) phase).ledgerEvolution := by
  have same : ImageKeys frame cut phase
      ((Sparse.Compiler.ledgerCompiler (code frame cut)).compile (Sparse.Compiler.emitted (code frame cut) phase)) := by
    dsimp only [Sparse.Compiler.ledgerCompiler,Sparse.Compiler.sourcePacket,Sparse.Compiler.emitted,Sparse.Compiler.represented]
    split <;> intro actual
    all_goals
      change Financial.Installation.KeepsKeys ((Sparse.Compiler.patch (code frame cut) phase (code frame cut).emission).toLedgerWriteEvolution)
      have keep : Financial.Installation.KeepsKeys ((code frame cut).evolution phase (code frame cut).emission) := by
        cases phase with
        | none => exact ⟨fun _ => rfl,fun _ => rfl⟩
        | some current => exact frame.whole_keys current
      exact Eq.mp (congrArg Financial.Installation.KeepsKeys
        (Sparse.Compiler.patch_is_the_complete_original_transport (code frame cut) phase (code frame cut).emission).symm) keep
  exact same _

def cursor : Option frame.V.Current → Option (Public.Accounting.Current input depth count frame.anchor)
  | none => none
  | some current => frame.cursor current

theorem live_cursor_next (current : frame.V.Current)
    (actual : Public.Accounting.Current input depth count frame.anchor) (aligned : frame.cursor current = some actual) :
    cursor frame (Sparse.Compiler.successor (code frame cut) (some current)).targetCurrent =
      some (Public.Accounting.nativeNext input depth count prefixLimit renewalLimit oldPast start actual) :=
  (congrArg (cursor frame) (Sparse.Compiler.successor_current (code frame cut) (some current))).trans
    (frame.cursor_next current actual aligned)

theorem live_destination (current : frame.V.Current)
    (actual : Public.Accounting.Current input depth count frame.anchor) (aligned : frame.cursor current = some actual) :
    HEq (Sparse.Compiler.successor (code frame cut) (some current)).ledgerEvolution.destination
      (Public.Accounting.nativeEvolution input depth count prefixLimit renewalLimit oldPast start frame.family actual).destination :=
  (Sparse.Compiler.successor_destination (code frame cut) (some current)).trans
    ((wholeDestination_is_the_original_effect frame current).trans (frame.successor_destination current actual aligned))

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Suffix
