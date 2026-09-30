import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Clause

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherInquiryAnswerOperands MotherU8Revision
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} (query : Query) (faceCalculus : U7ObstructionEvolutionCalculus N U7)
    (schema actual : LivingHeader) (headerSame : actual = schema)
    (actualCalculus : U7ObstructionEvolutionCalculus N U7) (calculusSame : actualCalculus = calculus)
    {rank : Ordinal.{0}}
    (oldCoordinates : Coordinates (rank := rank) N)
    (oldOccurrence : ∀ current, root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current ↪ MotherArenaHigher.Base rank)
    (coordinates : HeaderCoordinates rank schema)
    (operand : Operand root visit) (material : MotherArenaHigher.Material rank)

def formOnContexts : Option (MotherNativeClause.Clause root visit U7 calculus query) :=
  (formClause actualCalculus query faceCalculus actual oldCoordinates oldOccurrence
    (Eq.mp (congrArg (HeaderCoordinates rank) headerSame.symm) coordinates) operand material).map (fun clause =>
      Eq.mp (congrArg (fun calculus => MotherNativeClause.Clause root visit U7 calculus query) calculusSame) clause)

theorem formOnContexts_eq :
    formOnContexts calculus query faceCalculus schema actual headerSame actualCalculus calculusSame
      oldCoordinates oldOccurrence coordinates operand material =
    formClause calculus query faceCalculus schema oldCoordinates oldOccurrence coordinates operand material := by
  cases headerSame
  cases calculusSame
  exact congrFun Option.map_id _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
