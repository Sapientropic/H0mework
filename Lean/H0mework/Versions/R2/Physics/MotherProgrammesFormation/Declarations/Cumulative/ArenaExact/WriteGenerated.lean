import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaExact.WriteFormation
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteGenerated

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

theorem formed_write_consumes_original_generators (parent : M) (value : TransitionValue)
    (formed : formTransitions parent = some value)
    (rows : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt) (encode : WriteTotal rows ↪ B) :
    ∃ material : M, ∃ generated : LedgerWriteRowSourceAt value.1.2.2 value.2.2.2.exactTransitionAt,
      ∃ p : WritePresentation rows generated,
        formWritePrograms material = some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2, generated⟩ ∧
        (∀ context : WriteContext value.1.2.2,
          ∀ row : GeneratedLedgerWriteRowAt rows context.2.1 context.2.2.2.1 context.2.2.2.2,
            (generatedRowEquiv p context).symm (generatedRowEquiv p context row) = row ∧
            (generatedRowEquiv p context row).evolution = row.evolution ∧
            (generatedRowEquiv p context row).exact = row.exact) ∧
        (∀ (point : Point value.1.2.2) (target : CompleteLiveLedgerAt value.1.1),
          Option.map (generatedRemainder p point target) (rows.generateTransportedRemainder? point.2 target) =
            generated.generateTransportedRemainder? point.2 target) ∧
        (∀ (point : Point value.1.2.2) (target : CompleteLiveLedgerAt value.1.1)
          (rest : GeneratedLedgerTransportedRemainderAt rows point.2 target),
          (⟨(generatedRemainder p point target rest).evolution, (generatedRemainder p point target rest).exact⟩ :
            Sigma (WriteEncoding.Certification value.2.2.2 (point, target.support))) = ⟨rest.evolution, rest.exact⟩) := by
  obtain ⟨material, generated, produced, ⟨p⟩⟩ := every_write_program parent value formed rows encode
  exact ⟨material, generated, p, produced,
    fun context row => ⟨(generatedRowEquiv p context).symm_apply_apply row,
      generatedRow_evolution p context row, generatedRow_exact p context row⟩,
    generatedRemainder_generate p, generatedRemainder_compile p⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaExact
