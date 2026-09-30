import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Raw
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerClause

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface TypedSemanticWorldNetworkU8
open MotherInquiryAnswerOperands MotherU8Revision
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeLivingRootClosure N V)
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

structure Operand : Type where
  seed : MotherNativeAuthority.InventorySeed root
  steps : Nat
  obstruction : N.ObstructionAt (Support root visit)
  failureProjection : Projection root
  compilationProjection : Projection root

variable {root visit} {U7 : U7ProducerCalculus N}
    (calculus : U7ObstructionEvolutionCalculus N U7) {Query : Type} (query : Query)
    (faceCalculus : U7ObstructionEvolutionCalculus N U7)
    (header : LivingHeader) {rank : Ordinal.{0}}
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : ∀ current, root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank)
    (newCoordinates : HeaderCoordinates rank header)
local notation "M" => MotherArenaHigher.Material rank

def formClause (operand : Operand root visit) (material : M) :
    Option (MotherNativeClause.Clause root visit U7 calculus query) :=
  (MotherNativeAuthority.formAtVisit root visit operand.seed operand.steps).bind (fun authority =>
  (form calculus query authority.1 authority.2 operand.obstruction faceCalculus operand.failureProjection
    header oldCoordinates oldOccurrence newCoordinates material).bind (fun compiled =>
      MotherInquiryAnswerClause.formAtAuthority calculus query compiled operand.compilationProjection))

omit faceCalculus header oldCoordinates oldOccurrence newCoordinates in
theorem every_clause_at_core (clause : MotherNativeClause.Clause root visit U7 calculus query)
    (obstruction : N.ObstructionAt (Support root visit))
    (gate : SourceNativeU7TheoryAuditAt calculus (calculus.generated obstruction).1)
    (failure : ActualExpressibilityFailure (Theory root) obstruction)
    (core : SourceGeneratedInquiryU8RevisionCoreAt root visit U7 calculus (Theory root) query
      (InquiryEvent (root := root) (visit := visit)) clause.entry clause.authority obstruction gate failure)
    (compiledSame : clause.program.generate.output = .requiresU8 obstruction gate failure core)
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : ∀ current, root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank)
    (newCoordinates : HeaderCoordinates rank
      ⟨core.revision.generate.NewN, core.revision.generate.NewV, core.revision.generate.newLivingRoot⟩) :
    ∃ operand : Operand root visit, ∃ material : M,
      formClause calculus query core.frontier.face.calculus
        ⟨core.revision.generate.NewN, core.revision.generate.NewV, core.revision.generate.newLivingRoot⟩
        oldCoordinates oldOccurrence newCoordinates operand material = some clause := by
  obtain ⟨seed, steps, authorityFormed⟩ := MotherNativeAuthority.every_authority_at_visit root visit
    ⟨clause.entry, clause.authority⟩
  obtain ⟨material, formed⟩ := every_core calculus query clause.entry clause.authority obstruction gate failure core
    oldCoordinates oldOccurrence newCoordinates
  refine ⟨⟨seed, steps, obstruction, core.frontier.face.projection, clause.face.projection⟩, material, ?_⟩
  rw [formClause, authorityFormed]
  dsimp only [Option.bind_some]
  erw [formed]
  dsimp only [Option.bind_some]
  rw [← compiledSame]
  exact MotherInquiryAnswerClause.formAtAuthority_recovers calculus query clause

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
