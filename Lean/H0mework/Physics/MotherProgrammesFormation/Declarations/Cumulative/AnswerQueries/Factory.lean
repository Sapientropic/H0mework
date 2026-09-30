import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.AnswerFormation
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityFamilies.Coverage

/-! The complete query carrier and branch-index carrier are separate
material types. The label map itself is a formed total section; clauses
retain the original full-query label through its inverse interpretation. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherInquiryAnswerClause
open scoped Classical
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} (calculus : U7ObstructionEvolutionCalculus N U7)
    {Query : Type} {rank : Ordinal.{0}}
    (queryBase indexBase : MotherArenaHigher.Material rank)
    (queries : Query ≃ MotherAuthorityFamilies.Member queryBase)

abbrev Labels := MotherAuthorityFamilies.Member indexBase → MotherAuthorityFamilies.Member queryBase
abbrev ClauseSection (labels : Labels queryBase indexBase) :=
  (index : MotherAuthorityFamilies.Member indexBase) →
    MotherNativeClause.Clause root visit U7 calculus (queries.symm (labels index))
abbrev Value := Σ labels : Labels queryBase indexBase, ClauseSection (root := root) (visit := visit) calculus queryBase indexBase queries labels

variable (operand : Operand root visit ↪ MotherArenaHigher.Base rank)
local notation "M" => MotherArenaHigher.Material rank

def formClauses (labels : Labels queryBase indexBase) (material : M) :
    Option (ClauseSection (root := root) (visit := visit) calculus queryBase indexBase queries labels) :=
  (MotherArenaReceipts.NativeSection.form
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member indexBase ↪ MotherArenaHigher.Base rank)
    (fun _ => operand) material).bind (fun inputs =>
      if complete : ∀ index, (MotherInquiryAnswerClause.form calculus (queries.symm (labels index)) (inputs index)).isSome then
        some (fun index => (MotherInquiryAnswerClause.form calculus (queries.symm (labels index)) (inputs index)).get (complete index))
      else none)

def form (material : M) : Option (Value (root := root) (visit := visit) calculus queryBase indexBase queries) :=
  let parts := MotherArenaHigher.split rank material
  (MotherArenaReceipts.NativeSection.form
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member indexBase ↪ MotherArenaHigher.Base rank)
    (fun _ => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member queryBase ↪ MotherArenaHigher.Base rank)) parts.1).bind
      (fun labels => (formClauses calculus queryBase indexBase queries operand labels parts.2).map (Sigma.mk labels))

theorem every_clause_section (labels : Labels queryBase indexBase)
    (clauses : ClauseSection (root := root) (visit := visit) calculus queryBase indexBase queries labels)
    (answering : ∀ index, Answering calculus (queries.symm (labels index)) (clauses index).program.generate.output) :
    ∃ material : M, formClauses calculus queryBase indexBase queries operand labels material = some clauses := by
  have allInputs := fun index => every_answering_clause calculus (queries.symm (labels index)) (clauses index) (answering index)
  choose inputs formed using allInputs
  obtain ⟨material, selected⟩ := MotherArenaReceipts.NativeSection.every_section
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member indexBase ↪ MotherArenaHigher.Base rank)
    (fun _ => operand) inputs
  have complete : ∀ index, (MotherInquiryAnswerClause.form calculus (queries.symm (labels index)) (inputs index)).isSome := by
    intro index
    rw [formed]
    rfl
  refine ⟨material, ?_⟩
  simp only [formClauses, selected, Option.bind_some, dif_pos complete]
  apply congrArg some
  funext index
  exact Option.some.inj ((Option.some_get (complete index)).trans (formed index))

theorem every_labelled (labels : Labels queryBase indexBase)
    (clauses : ClauseSection (root := root) (visit := visit) calculus queryBase indexBase queries labels)
    (answering : ∀ index, Answering calculus (queries.symm (labels index)) (clauses index).program.generate.output) :
    ∃ material : M, form calculus queryBase indexBase queries operand material = some ⟨labels, clauses⟩ := by
  obtain ⟨labelsM, labelsFormed⟩ := MotherArenaReceipts.NativeSection.every_section
    (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member indexBase ↪ MotherArenaHigher.Base rank)
    (fun _ => (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ : MotherAuthorityFamilies.Member queryBase ↪ MotherArenaHigher.Base rank)) labels
  obtain ⟨clausesM, clausesFormed⟩ := every_clause_section calculus queryBase indexBase queries operand labels clauses answering
  refine ⟨MotherArenaHigher.pack rank (labelsM, clausesM), ?_⟩
  simp only [form, MotherArenaHigher.split_pack, labelsFormed, Option.bind_some, clausesFormed, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
