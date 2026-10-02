import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.MacroProcess.Operations.Assembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

set_option backward.dsimp.proofs true in
/-- Local whole-process coverage on a formed node family. The literal node
identity preserves all query laws; the state equivalence retains every
answered and duplicate registry index. No index is inferred from erasure. -/
theorem every_original_on_nodes {rank : Ordinal.{0}}
    (domain : MotherArenaHigher.Material rank) (nodes : Nodes domain)
    (event : Event nodes ↪ MotherArenaHigher.Base rank)
    (original : SourceNativeInquiryEngineProcess.{0}) (state : State domain ≃ original.State)
    (nodeSame : ∀ current, nodes current = original.stateAt (state current)) :
    ∃ material : MotherArenaHigher.Material rank,
      formProcess domain nodes event material = some (MotherRegistryRecovery.rechart original state) := by
  have same : nodes = fun current => original.stateAt (state current) := funext nodeSame
  subst nodes
  let target := MotherRegistryRecovery.rechart original state
  let fields : Fields (domain := domain) target.stateAt :=
    ⟨target.initial, fun current query => (target.successorAt current query).val⟩
  have checked : Admissible domain target.stateAt fields := by
    refine ⟨target.erase_injective, ?_⟩
    intro current query
    refine ⟨?_, (target.successorAt current query).property.2⟩
    apply (target.successorAt current query).property.1.trans
    generalize source_eq : target.stateAt current = source at query ⊢
    cases source with
    | active prior => rfl
    | answered prior oldQuery => exact nomatch query
  obtain ⟨material, formed⟩ := every_process_fields domain target.stateAt event fields checked
  exact ⟨material, formed⟩

/-- All State and legal (state,query) addresses are paid together. This is
only the operations layer over an already supplied complete node family;
it does not assert that such nodes have been source-produced. -/
theorem every_indexed_fields (Carrier : Type) (nodes : Carrier → RootInquiryProcessNode.{0})
    (initial : Carrier) (next : (state : Carrier) → (nodes state).Query → Carrier) :
    ∃ rank : Ordinal.{0}, ∃ domain : MotherArenaHigher.Material rank,
      ∃ state : State domain ≃ Carrier,
      ∃ event : (Σ current : State domain, (nodes (state current)).Query) ↪ MotherArenaHigher.Base rank,
      ∃ material : MotherArenaHigher.Material rank,
        formFields domain (fun current => nodes (state current)) event material =
          some ⟨state.symm initial, fun current query => state.symm (next (state current) query)⟩ := by
  let Events := Σ current : Carrier, (nodes current).Query
  let Total := Carrier ⊕ Events
  let rank := MotherArenaHigher.carrierRank Total
  let shared := MotherArenaHigher.carrierAddress Total
  let stateCode : Carrier ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let eventCode : Events ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr value), fun _ _ same => Sum.inr.inj (shared.injective same)⟩
  obtain ⟨domain, ⟨indices⟩⟩ := MotherAuthorityFamilies.every_index Carrier stateCode
  let state : State domain ≃ Carrier := indices.symm
  let event : (Σ current : State domain, (nodes (state current)).Query) ↪ MotherArenaHigher.Base rank :=
    (Equiv.sigmaCongrLeft (β := fun current => (nodes current).Query) state).toEmbedding.trans eventCode
  let fields : Fields (domain := domain) (fun current => nodes (state current)) :=
    ⟨state.symm initial, fun current query => state.symm (next (state current) query)⟩
  obtain ⟨material, formed⟩ := every_fields domain _ event fields
  exact ⟨rank, domain, state, event, material, formed⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherMacroOperations
