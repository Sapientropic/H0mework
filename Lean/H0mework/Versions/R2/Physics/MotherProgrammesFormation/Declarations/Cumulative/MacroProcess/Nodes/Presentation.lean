import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Nodes.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

private theorem create_base {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryEngineStateAt N V) : RootInquiryEngineStateAt.create state.base = state := by
  cases state
  rfl

variable (original : RootInquiryStatePresentation.{0})
    (origin : MotherCompleteInquiry.Origin original.state.base)

theorem presentation_recovers : origin.readWorld = original := by
  rw [origin.readWorld_eq, create_base]

/-- Complete actual Query fibres acquire their addresses from the full
Query material, then transport across the true recovered presentation Eq. -/
def queryCode : origin.readWorld.Query ↪ MotherArenaHigher.Base origin.answerRank :=
  (Equiv.cast (congrArg RootInquiryStatePresentation.Query (presentation_recovers original origin))).toEmbedding.trans
    (origin.answer.queries.toEmbedding.trans
      (⟨Subtype.val, fun _ _ same => Subtype.ext same⟩ :
        MotherAuthorityFamilies.Member origin.answer.materials.queries ↪ MotherArenaHigher.Base origin.answerRank))

private theorem every_selection_on_same {rank : Ordinal.{0}}
    (actual : RootInquiryStatePresentation.{0}) (same : actual = original)
    (query : actual.Query ↪ MotherArenaHigher.Base rank) (selection : Selection original) :
    ∃ material : MotherArenaHigher.Material rank,
      form actual query material = some (nodeAt original selection) := by
  cases same
  exact every_selection original query selection

theorem node_on_formed_presentation (selection : Selection original) :
    ∃ material : MotherArenaHigher.Material origin.answerRank,
      form origin.readWorld (queryCode original origin) material = some (nodeAt original selection) :=
  every_selection_on_same original origin.readWorld (presentation_recovers original origin) (queryCode original origin) selection

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroNodes
