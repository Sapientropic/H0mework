import H0mework.Foundation.Inquiry.Protocol

/-! Eliminate the original canonical event at fixed complete dependency indices.
The complete compilation value recovers the complete program. This is an
eliminator and assembler, not a source for an unformed compilation value. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeProgram

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
  {oldTheory : TheoryState N} {Query : Type u} {query : Query}
  {InquiryEvent : Type (u + 1)} {event : InquiryEvent}
  {entry : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Program" => SourceNativeInquiryCompilationProgramAt
  root visit U7 calculus oldTheory query event entry authority

local notation "Output" => SourceNativeInquiryCompilationAt
  root visit U7 calculus oldTheory query event entry authority

theorem compile_eq_generate (program : Program)
    (exactEvent : ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit) :
    program.compile exactEvent = program.generate.output :=
  congrArg program.compile (SourceNativeTemporalVisitGeneratedEvolutionAt.eq_generated exactEvent)

/-- Assemble the original program record from its complete canonical output. -/
def restore (output : Output) : Program :=
  ⟨fun _ => output⟩

theorem generate_restore (output : Output) :
    (restore output).generate.output = output := rfl

theorem restore_generate (program : Program) :
    restore program.generate.output = program := by
  exact congrArg (fun compiled => (⟨compiled⟩ : Program))
    (funext fun exactEvent => (compile_eq_generate program exactEvent).symm)

theorem program_eq_iff_output_eq (first last : Program) :
    first = last ↔ first.generate.output = last.generate.output := by
  constructor
  · intro same
    cases same
    rfl
  · intro same
    exact (restore_generate first).symm.trans
      ((congrArg restore same).trans (restore_generate last))

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeProgram
