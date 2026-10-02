import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaPrograms.TerminalCoverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherArenaCompiler
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

def TerminalEncoding.ofTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {rows : LedgerTerminalRowSourceAt source} (encode : TerminalTotal rows ↪ B) : TerminalEncoding (rank := rank) rows where
  row := ⟨fun event => encode (.inl event), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  settlement := ⟨fun event => encode (.inr event), fun _ _ same => Sum.inr.inj (encode.injective same)⟩

theorem every_terminal_program (parent : M) (value : MotherArenaCompiler.SourceValue) (compiled : CompilationSection value.2.2)
    (formed : MotherArenaCompiler.formCompilation parent = some ⟨value, compiled⟩) (rows : LedgerTerminalRowSourceAt value.2.2)
    (encode : TerminalTotal rows ↪ B) :
    ∃ material : M, ∃ generated : LedgerTerminalRowSourceAt value.2.2,
      formTerminalSource material = some ⟨value, compiled, generated⟩ ∧ Nonempty (TerminalPresentation rows generated) := by
  let coordinates := coordinatesOfCompilation parent value compiled formed
  let ledgerCoordinates := ledgerCoordinatesOfCompilation parent value compiled formed
  let code := TerminalEncoding.ofTotal encode
  obtain ⟨material, hm⟩ := (MotherArenaHigher.read_surjective rank)
    (TerminalEncoding.reader coordinates ledgerCoordinates rows code)
  let checked := TerminalEncoding.checked coordinates ledgerCoordinates rows code hm
  exact ⟨(MotherArenaHigher.pack rank) (parent, material), terminalRows coordinates ledgerCoordinates material checked,
    terminal_source_formed parent material value compiled formed checked,
    ⟨TerminalEncoding.presentation coordinates ledgerCoordinates rows code hm⟩⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaPrograms
