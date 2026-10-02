import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteFormation

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    {operations : Transitions source} {old generated : LedgerWriteRowSourceAt source operations.exactTransitionAt}
    (p : WritePresentation old generated)

def generatedRowEquiv (context : WriteContext source) :
    GeneratedLedgerWriteRowAt old context.2.1 context.2.2.2.1 context.2.2.2.2 ≃
      GeneratedLedgerWriteRowAt generated context.2.1 context.2.2.2.1 context.2.2.2.2 :=
  (writeSealEquiv old context).trans ((p.row context).trans (writeSealEquiv generated context).symm)

theorem generatedRow_event (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt old context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (generatedRowEquiv p context row).event = p.row context row.event := rfl

theorem generatedRow_evolution (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt old context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (generatedRowEquiv p context row).evolution = row.evolution :=
  (p.row_evolution context row.event).trans row.evolution_eq

theorem generatedRow_exact (context : WriteContext source)
    (row : GeneratedLedgerWriteRowAt old context.2.1 context.2.2.2.1 context.2.2.2.2) :
    (generatedRowEquiv p context row).exact = row.exact :=
  (p.row_exact context row.event).trans row.exact_eq

theorem remainderSeal_eq {point : Point source} {target : CompleteLiveLedgerAt N}
    (left right : GeneratedLedgerTransportedRemainderAt old point.2 target) : left = right := by
  have same := Option.some.inj (left.selected.symm.trans right.selected)
  cases left
  cases right
  cases same
  rfl

theorem remainder_generated {point : Point source} {target : CompleteLiveLedgerAt N}
    (value : GeneratedLedgerTransportedRemainderAt old point.2 target) :
    old.generateTransportedRemainder? point.2 target = some value := by
  unfold LedgerWriteRowSourceAt.generateTransportedRemainder?
  split
  · rename_i absent
    cases value.selected.symm.trans absent
  · congr 1
    exact remainderSeal_eq _ _

def generatedRemainder (point : Point source) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt old point.2 target) :
    GeneratedLedgerTransportedRemainderAt generated point.2 target :=
  generated.generateTransportedRemainder point.2 target (p.remainder (point, target.support) value.event)
    ((p.remainder_emit (point, target.support)).symm.trans
      (congrArg (Option.map (p.remainder (point, target.support))) value.selected))

theorem generatedRemainder_event (point : Point source) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt old point.2 target) :
    (generatedRemainder p point target value).event = p.remainder (point, target.support) value.event := rfl

theorem generatedRemainder_compile (point : Point source) (target : CompleteLiveLedgerAt N)
    (value : GeneratedLedgerTransportedRemainderAt old point.2 target) :
    (⟨(generatedRemainder p point target value).evolution, (generatedRemainder p point target value).exact⟩ :
      Sigma (WriteEncoding.Certification operations (point, target.support))) = ⟨value.evolution, value.exact⟩ :=
  p.remainder_compile (point, target.support) value.event

theorem generatedRemainder_generate (point : Point source) (target : CompleteLiveLedgerAt N) :
    Option.map (generatedRemainder p point target) (old.generateTransportedRemainder? point.2 target) =
      generated.generateTransportedRemainder? point.2 target := by
  cases selected : old.generateTransportedRemainder? point.2 target with
  | some value =>
      exact (remainder_generated (generatedRemainder p point target value)).symm
  | none =>
      have absent : old.transportedRemainderSource.emit? point.2 target.support = none := by
        by_cases emitted : old.transportedRemainderSource.emit? point.2 target.support = none
        · exact emitted
        · obtain ⟨event, eventEq⟩ := Option.ne_none_iff_exists'.mp emitted
          have produced := remainder_generated (old.generateTransportedRemainder point.2 target event eventEq)
          rw [selected] at produced
          cases produced
      have transported : generated.transportedRemainderSource.emit? point.2 target.support = none :=
        (p.remainder_emit (point, target.support)).symm.trans
          (congrArg (Option.map (p.remainder (point, target.support))) absent)
      unfold LedgerWriteRowSourceAt.generateTransportedRemainder?
      split
      · rfl
      · rename_i event eventEq
        cases transported.symm.trans eventEq

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
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
