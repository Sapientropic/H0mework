import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.Transport
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteConsumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
open MotherNetworkFactory MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)

def formedIncidenceMember (context : IncidenceContext original) :
    old.Incidence context ≃ formed.Incidence (incidenceContextEquiv p context) :=
  (incidenceMemberEquiv p old context).trans (q.incidence (incidenceContextEquiv p context))

def formedExactMember (context : WriteContext original) :
    old.Exact context ≃ formed.Exact (writeContextEquiv p context) :=
  (exactMemberEquiv p old context).trans (q.exact (writeContextEquiv p context))

def formedIncidenceAtWrite (context : WriteContext original) :
    old.Incidence (incidenceContext context) ≃ formed.Incidence (incidenceContext (writeContextEquiv p context)) :=
  (incidenceAtWriteEquiv p old context).trans (q.incidence (incidenceContext (writeContextEquiv p context)))

theorem formed_project (context : WriteContext original) (value : old.Exact context) :
    formed.project (writeContextEquiv p context) (formedExactMember p q context value) =
      formedIncidenceAtWrite p q context (old.project context value) :=
  (q.project (writeContextEquiv p context) (exactMemberEquiv p old context value)).trans
    (congrArg (q.incidence (incidenceContext (writeContextEquiv p context))) (transported_project p old context value))

abbrev SourceTransitionTotal {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}
    (compiler : SourceNativeLedgerCompiler source) :=
  SourceTerminalTotal compiler ⊕ TransitionTotal (Transitions.ofCompiler compiler)

/-- The original compiler appears only in coverage. Complete member types
and their dependent operation are restored on the very same formed source. -/
theorem formed_transitions_recover_original_operations (N : WorldRelationNetwork.{0}) (V : Vocabulary.{0})
    (original : SourceNativeSource N V) (compiler : SourceNativeLedgerCompiler original)
    (encode : SourceTransitionTotal compiler ↪ B) :
    ∃ material : M, ∃ G : WorldRelationNetwork.{0}, ∃ W : Vocabulary.{0}, ∃ generated : SourceNativeSource G W,
      ∃ compiled : CompilationSection generated, ∃ rows : LedgerTerminalRowSourceAt generated,
      ∃ operations : Transitions generated,
      ∃ n : MotherNetworkOrigin.Presentation N G, ∃ v : MotherVocabularyOrigin.Presentation V W,
      ∃ p : MotherNativeSourceOrigin.Presentation n v original generated,
      ∃ _q : TerminalPresentation (transportedTerminal p compiler.terminalRowSource) rows,
      ∃ r : TransitionPresentation (transportedTransitions p (Transitions.ofCompiler compiler)) operations,
        formTransitions material = some ⟨⟨G, W, generated⟩, compiled, rows, operations⟩ ∧
        (∀ point : Point original,
          (fullCompilationEquiv p point.2).symm (compiled (pointEquiv p point)) = compiler.compile point.2) ∧
        (∀ context : WriteContext original, ∀ value : (Transitions.ofCompiler compiler).Exact context,
          (formedIncidenceAtWrite p r context).symm
            (operations.project (writeContextEquiv p context) (formedExactMember p r context value)) =
              compiler.exact_incidence value) := by
  let parentCode : SourceTerminalTotal compiler ↪ B :=
    ⟨fun value => encode (.inl value), fun _ _ same => Sum.inl.inj (encode.injective same)⟩
  let operationCode : TransitionTotal (Transitions.ofCompiler compiler) ↪ B :=
    ⟨fun value => encode (.inr value), fun _ _ same => Sum.inr.inj (encode.injective same)⟩
  obtain ⟨parent, G, W, generated, compiled, rows, n, v, p, q, parentFormed, recover⟩ :=
    formed_terminal_recovers_original_programs N V original compiler parentCode
  let generatedCode := (transitionTotalEquiv p (Transitions.ofCompiler compiler)).symm.toEmbedding.trans operationCode
  obtain ⟨material, operations, operationFormed, ⟨r⟩⟩ := every_transition_program parent ⟨G, W, generated⟩ compiled rows
    parentFormed (transportedTransitions p (Transitions.ofCompiler compiler)) generatedCode
  refine ⟨material, G, W, generated, compiled, rows, operations, n, v, p, q, r, operationFormed, recover, ?_⟩
  intro context value
  exact (congrArg (formedIncidenceAtWrite p r context).symm (formed_project p r context value)).trans
    ((formedIncidenceAtWrite p r context).symm_apply_apply (compiler.exact_incidence value))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherExactPrograms
