import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Consumer
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query Index : Type}
    (label : Index → Query)
    (clauses : (index : Index) → MotherNativeClause.Clause root visit U7 calculus (label index))
    {rank : Ordinal.{0}}
    (queryCode : Query ↪ MotherArenaHigher.Base rank)
    (indexCode : Index ↪ MotherArenaHigher.Base rank)

/-- Assemble only already formed clause outputs. The selector is an actual
material graph; query labels are checked, never inferred from target compile. -/
def formSection (material : MotherArenaHigher.Material rank) :
    Option ((query : Query) → MotherNativeClause.Clause root visit U7 calculus query) :=
  (MotherArenaReceipts.NativeSection.form queryCode (fun _ => indexCode) material).bind (fun selection =>
    if aligned : ∀ query, label (selection query) = query then
      some (fun query => Eq.mp (congrArg (fun q => MotherNativeClause.Clause root visit U7 calculus q)
        (aligned query)) (clauses (selection query)))
    else none)

theorem formSection_recovers (selection : Query → Index)
    (aligned : ∀ query, label (selection query) = query)
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (same : ∀ query, Eq.mp (congrArg (fun q => MotherNativeClause.Clause root visit U7 calculus q)
        (aligned query)) (clauses (selection query)) = original query) :
    ∃ material : MotherArenaHigher.Material rank,
      formSection label clauses queryCode indexCode material = some original := by
  obtain ⟨material, formed⟩ := MotherArenaReceipts.NativeSection.every_section queryCode (fun _ => indexCode) selection
  refine ⟨material, ?_⟩
  simp only [formSection, formed, Option.bind_some, dif_pos aligned]
  exact congrArg some (funext same)

private theorem clause_cast {q r : Query} (same : q = r)
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query) :
    Eq.mp (congrArg (fun q => MotherNativeClause.Clause root visit U7 calculus q) same) (original q) = original r := by
  cases same
  rfl

/-- Complete equality of each formed parent clause suffices for the selector
assembly. This does not replace any parent's source responsibility. -/
theorem formSection_of_parent_recovery (selection : Query → Index)
    (aligned : ∀ query, label (selection query) = query)
    (original : (query : Query) → MotherNativeClause.Clause root visit U7 calculus query)
    (recovered : ∀ index, clauses index = original (label index)) :
    ∃ material : MotherArenaHigher.Material rank,
      formSection label clauses queryCode indexCode material = some original :=
  formSection_recovers label clauses queryCode indexCode selection aligned original (fun query => by
    rw [recovered]
    exact clause_cast (aligned query) original)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherCompleteInquiry
