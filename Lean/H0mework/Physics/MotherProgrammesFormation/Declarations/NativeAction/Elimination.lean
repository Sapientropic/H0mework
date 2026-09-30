import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeProgram.Elimination

/-! The actual-action branch has the same canonical event domain, but its
target type depends on that event. Elimination retains the complete target
record; it supplies no source for an unformed target root or ledger. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeAction

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

universe u

variable {N : WorldRelationNetwork.{u}} {V : ConstructiveRoot.Vocabulary.{u}}
  {root : SourceNativeLivingRootClosure N V}
  {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
  {entry : OpenResponsibilityAt N
    (root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.account.supportOf
      (root.emitted visit.current))}
  {authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry}

local notation "Event" => ExactTemporalCausalRootEventAt root.toAuthoritativeRoot.toLedgerRoot visit
local notation "canonical" => root.toAuthoritativeRoot.toLedgerRoot.generatedAtTemporalVisit visit
local notation "Program" => SourceNativeSequentialActualActionProgramAt root visit entry authority
local notation "Target" => SourceNativeSequentialActualActionTargetAt root visit canonical entry authority

def read (program : Program) : Target :=
  (program.generate canonical).target

def restore (target : Target) : Program where
  targetAt exactEvent :=
    (SourceNativeTemporalVisitGeneratedEvolutionAt.eq_generated exactEvent).symm ▸ target

theorem read_restore (target : Target) : read (restore target) = target := rfl

theorem restore_read (program : Program) : restore (read program) = program := by
  apply congrArg (fun targetAt => (⟨targetAt⟩ : Program))
  funext exactEvent
  cases exactEvent
  rfl

/-- Heterogeneous equality comes from equality of the exact event, not an equivalence of types. -/
theorem targetAt_heq_read (program : Program) (exactEvent : Event) :
    HEq (program.targetAt exactEvent) (read program) := by
  cases SourceNativeTemporalVisitGeneratedEvolutionAt.eq_generated exactEvent
  rfl

theorem program_eq_iff_target_eq (first last : Program) :
    first = last ↔ read first = read last := by
  constructor
  · intro same
    cases same
    rfl
  · intro same
    exact (restore_read first).symm.trans
      ((congrArg restore same).trans (restore_read last))

variable {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
  {oldTheory : TheoryState N} {Query : Type u} {query : Query}
  {InquiryEvent : Type (u + 1)} {event : InquiryEvent}

local notation "Output" => SourceNativeInquiryCompilationAt
  root visit U7 calculus oldTheory query event entry authority

theorem complete_compilation_recovers (program : Program) (exactEvent : Event)
    (generated : SourceGeneratedSequentialActualActionAt program exactEvent) :
    (SourceNativeInquiryCompilationAt.actualAction
      ((restore (read program)).generate exactEvent) : Output) =
      .actualAction generated := by
  rw [restore_read]

end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeAction
