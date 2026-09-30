import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerClause
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquiryQuery.Coverage

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}

structure Operand (root : SourceNativeLivingRootClosure N V) where
  seed : MotherNativeAuthority.InventorySeed root
  steps : Nat
  projection : MotherInquiryAnswerOperands.Projection root

variable {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query Index : Type} {rank : Ordinal.{0}}

def formInputs (base : MotherArenaHigher.Material rank)
    (operandAddress : Operand root ↪ MotherArenaHigher.Base rank)
    (material : MotherArenaHigher.Material rank) :
    Option (MotherAuthorityFamilies.Member base → Operand root) :=
  MotherArenaReceipts.NativeSection.form
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member base ↪ MotherArenaHigher.Base rank)
    (fun _ => operandAddress) material

theorem every_inputs (label : Index → Query) (clauses : (query : Index) → MotherNativeClause.Clause root visit U7 calculus (label query))
    (base : MotherArenaHigher.Material rank) (queries : Index ≃ MotherAuthorityFamilies.Member base)
    (operandAddress : Operand root ↪ MotherArenaHigher.Base rank) :
    ∃ material : MotherArenaHigher.Material rank,
      ∃ available : (formInputs base operandAddress material).isSome,
        let inputs := (formInputs base operandAddress material).get available
        (∀ query, MotherNativeAuthority.formAtVisit root visit (inputs (queries query)).seed
          (inputs (queries query)).steps = some ⟨(clauses query).entry, (clauses query).authority⟩) ∧
        ∀ query, (inputs (queries query)).projection = (clauses query).face.projection := by
  have origins := fun query => MotherNativeAuthority.every_authority_at_visit root visit
    ⟨(clauses query).entry, (clauses query).authority⟩
  choose seeds steps formed using origins
  let values : MotherAuthorityFamilies.Member base → Operand root :=
    fun query => ⟨seeds (queries.symm query), steps (queries.symm query), (clauses (queries.symm query)).face.projection⟩
  obtain ⟨material, materialFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member base ↪ MotherArenaHigher.Base rank)
    (fun _ => operandAddress) values
  have inputFormed : formInputs base operandAddress material = some values := materialFormed
  have available : (formInputs base operandAddress material).isSome := by rw [inputFormed]; rfl
  have selected : (formInputs base operandAddress material).get available = values :=
    Option.some.inj ((Option.some_get available).trans inputFormed)
  refine ⟨material, available, ?_, ?_⟩
  · intro query
    simp only [selected, values, queries.symm_apply_apply]
    exact formed query
  · intro query
    simp only [selected, values]
    exact congrArg (fun q => (clauses q).face.projection) (queries.symm_apply_apply query)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
