import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler.Entry

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot

noncomputable section

theorem canonical_key {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
    (root : SourceNativeLedgerRootClosure N V) (current next : V.Current)
    (nextEq : (root.toRoot.evolutionAt current).nextCurrent? = some next)
    (successor : SourceNativeLedgerGeneratedSuccessorAt (root.emitted current) (root.generatedLedgerAt current))
    (entry : OpenResponsibilityAt N (root.source.source.toRootSource.account.supportOf (root.emitted current)))
    (expected : N.Responsibility)
    (key : (successor.ledgerEvolution.destination entry).1.1 = expected) :
    (root.canonicalTargetEntryAtNext nextEq entry).1 = expected := by
  revert key successor
  unfold SourceNativeLedgerRootClosure.canonicalTargetEntryAtNext
  dsimp only [SourceNativeLedgerRootClosure.generatedLedgerAt] at *
  generalize_proofs at *
  generalize imageEq : root.source.ledgerCompiler.compile (root.emitted current) = image at *
  cases image with
  | nativeWrite write structural target evolution =>
    intro successor key
    have targetEq : V.nativeTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact key
  | relationWrite write structural target evolution =>
    intro successor key
    have targetEq : V.relationTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact key
  | continuedTransport write structural target evolution =>
    intro successor key
    have targetEq : V.continuedTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact key
  | borromeanRedirect write structural target evolution =>
    intro successor key
    have targetEq : V.redirectTarget write = next := by
      change (root.source.source.toRootSource.actual.compile (root.emitted current)).nextCurrent? = some next at nextEq
      rw [structural] at nextEq
      exact Option.some.inj nextEq
    have commutes := root.compiler_commutes current
    rw [imageEq] at commutes
    cases targetEq
    cases commutes
    exact key
  | faithfulTerminal terminal structural evolution =>
    intro successor _
    exact successor.elim

variable {N : WorldRelationNetwork} (F : Flow N)

theorem nextEq (current : F.Current) :
    ((livingRoot F).toAuthoritativeRoot.toLedgerRoot.toRoot.evolutionAt current).nextCurrent? = some (F.next current) := by
  change ((source F).toRootSource.actual.compile (emitted F current)).nextCurrent? = _
  rw [source_choice]
  split <;> rfl

private def ImageKey {current : F.Current}
    (entry : OpenResponsibilityAt N (F.support current)) (expected : N.Responsibility)
    (image : SourceNativeLedgerEvolutionAt (source F) (emitted F current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (emitted F current) image,
    (actual.ledgerEvolution.destination entry).1.1 = expected

theorem canonical_key_of_flow (current : F.Current)
    (entry : OpenResponsibilityAt N (F.support current)) (expected : N.Responsibility)
    (key : ((F.evolution current).destination entry).1.1 = expected) :
    ((livingRoot F).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext (nextEq F current) entry).1 = expected := by
  have actualKey : ImageKey F entry expected ((ledgerCompiler F).compile (emitted F current)) := by
    dsimp only [ledgerCompiler,sourcePacket]
    split <;> intro actual <;>
      change ((patch F current).toLedgerWriteEvolution.destination entry).1.1 = expected
    all_goals rw [patch_destination]; exact key
  exact canonical_key (livingRoot F).toAuthoritativeRoot.toLedgerRoot current (F.next current)
    (nextEq F current) (successor F current) entry expected (actualKey _)

#print axioms canonical_key_of_flow

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Root.Compiler
