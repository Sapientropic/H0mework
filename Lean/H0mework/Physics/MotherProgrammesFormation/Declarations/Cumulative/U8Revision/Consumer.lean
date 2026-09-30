import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Revision.Source

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {oldTheory : TheoryState N} {Query : Type} {query : Query}
    {Event : Type 1} {event : Event}
    {entry : OpenResponsibilityAt N (MotherInquiryAnswerOperands.Support root visit)}
    {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}
    {obstruction : N.ObstructionAt (MotherInquiryAnswerOperands.Support root visit)}
    {gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1}
    {failure : ActualExpressibilityFailure oldTheory obstruction}
    (core : SourceGeneratedInquiryU8RevisionCoreAt root visit U7 calculus oldTheory query event entry authority obstruction gate failure)
    {rank : Ordinal.{0}}
    (origin : SourceOrigin (⟨V, root, visit⟩ : SourceNativeLivingRootCurrentAt N) core.revision (rank := rank))

/-- Direct consumption retains the complete original requiresU8 value at
its fixed frontier, including the field-grounded revised source and all rows. -/
theorem complete_branch_recovers :
    (SourceNativeInquiryCompilationAt.requiresU8 obstruction gate failure
      ⟨core.frontier, origin.read⟩ : SourceNativeInquiryCompilationAt root visit U7 calculus oldTheory query event entry authority) =
      .requiresU8 obstruction gate failure core := by
  rw [origin.read_eq]

/-- A single source material recovers the original revision in the exact
compiler branch. The frontier's material formation is handled separately. -/
theorem every_original_revision_consumed :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ origin : SourceOrigin (⟨V, root, visit⟩ : SourceNativeLivingRootCurrentAt N) core.revision (rank := rank),
        origin.material = material ∧
        (SourceNativeInquiryCompilationAt.requiresU8 obstruction gate failure
          ⟨core.frontier, origin.read⟩ : SourceNativeInquiryCompilationAt root visit U7 calculus oldTheory query event entry authority) =
          .requiresU8 obstruction gate failure core := by
  obtain ⟨rank, material, origin, packed, _same, _original⟩ := every_revision_source
    (⟨V, root, visit⟩ : SourceNativeLivingRootCurrentAt N) core.revision
  exact ⟨rank, material, origin, packed, complete_branch_recovers core origin⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Revision
