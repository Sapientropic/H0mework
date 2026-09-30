import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Root.Transport

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherFullPatches MotherPatchInventory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    (root : SourceNativeLedgerRootClosure N V) {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v root.source.source generated)
    (compiler : SourceNativeLedgerCompiler generated)
    (recover : ∀ point : Point root.source.source,
      (fullCompilationEquiv p point.2).symm (compiler.compile (pointEquiv p point).2) = root.source.ledgerCompiler.compile point.2)

include recover in
theorem representedCompiler_commutes (current : W.Current) :
    (compiler.compile (emitterEquiv p root.emitted current)).CommutesWith (emitterEquiv p root.emitted) := by
  obtain ⟨current, rfl⟩ := v.current.surjective current
  let point : Point root.source.source := ⟨current, root.emitted current⟩
  have commutes := fullCompilation_commutes p root.emitted point (root.generatedLedgerAt current) (root.compiler_commutes current)
  have compiledEq := (congrArg (fullCompilationEquiv p point.2) (recover point)).symm.trans
    ((fullCompilationEquiv p point.2).apply_symm_apply _)
  have compiledCommutes := Eq.mp (congrArg
    (fun value : SourceNativeLedgerEvolutionAt generated (pointEquiv p point).2 => value.CommutesWith (emitterEquiv p root.emitted))
      compiledEq) commutes
  exact Eq.mpr (congrArg (fun event : generated.toRootSource.actual.OccurrenceAt (v.current current) =>
    (compiler.compile event).CommutesWith (emitterEquiv p root.emitted)) (emitter_at p root.emitted current)) compiledCommutes

def representedRoot : SourceNativeLedgerRootClosure G W where
  source := ⟨generated, compiler⟩
  emitted := emitterEquiv p root.emitted
  compiler_commutes := representedCompiler_commutes root p compiler recover

/-- The event and entire original ledger compilation are recovered together;
all casts below come from the actual emitter equality. -/
theorem generatedLedgerAt_pair (current : V.Current) :
    (⟨(representedRoot root p compiler recover).emitted (v.current current),
       (representedRoot root p compiler recover).generatedLedgerAt (v.current current)⟩ :
        Σ event : generated.toRootSource.actual.OccurrenceAt (v.current current), SourceNativeLedgerEvolutionAt generated event) =
      ⟨p.event current (root.emitted current), fullCompilationEquiv p (root.emitted current) (root.generatedLedgerAt current)⟩ := by
  have image := (congrArg (fullCompilationEquiv p (root.emitted current)) (recover ⟨current, root.emitted current⟩)).symm.trans
    ((fullCompilationEquiv p (root.emitted current)).apply_symm_apply _)
  exact (congrArg (fun event : generated.toRootSource.actual.OccurrenceAt (v.current current) =>
    (⟨event, compiler.compile event⟩ : Σ event : generated.toRootSource.actual.OccurrenceAt (v.current current),
      SourceNativeLedgerEvolutionAt generated event)) (emitter_at p root.emitted current)).trans
    (congrArg (fun value : SourceNativeLedgerEvolutionAt generated (p.event current (root.emitted current)) =>
      (⟨p.event current (root.emitted current), value⟩ : Σ event : generated.toRootSource.actual.OccurrenceAt (v.current current),
        SourceNativeLedgerEvolutionAt generated event)) image.symm)

theorem generated_next (current : V.Current) :
    ((representedRoot root p compiler recover).toRoot.evolutionAt (v.current current)).nextCurrent? =
      Option.map v.current (root.toRoot.evolutionAt current).nextCurrent? :=
  (congrArg (fun value : EvolutionAt W (v.current current) => value.nextCurrent?)
    ((congrArg generated.toRootSource.actual.compile (emitter_at p root.emitted current)).trans
      (p.compile_eq current (root.emitted current)))).trans (v.evolution_next _).symm

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLedgerRoot
