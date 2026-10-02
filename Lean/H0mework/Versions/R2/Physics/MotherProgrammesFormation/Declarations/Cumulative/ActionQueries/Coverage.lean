import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Origin

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open MotherHandoffRestriction MotherHandoffSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

/-- Complete actual-action query families, their heterogeneous target living
roots, full U7 header and all receipt fibres form at one lower/upper pair.
All address operands are chosen internally from the original complete data. -/
theorem every_action_source (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) (Index : Type) (label : Index → state.Query)
    (actions : ∀ query, IsAction state.calculus (label query) (state.compileInquiry (label query))) :
    ∃ lower : Ordinal.{0}, ∃ upper : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material upper,
      ∃ targets : Targets state label, ∃ origin : Origin lower upper state label targets,
        readLower origin.originalAddress material = packLower origin.materials ∧
        (∀ query, readChild material (origin.originalAddress (origin.queries query).val) = origin.targetMaterials query) ∧
        origin.readClauses = (fun query => MotherNativeClause.ofState state (label query)) ∧
        Function.LeftInverse (MotherReceiptHigher.restrictArena lower upper origin.originalAddress)
          (MotherReceiptHigher.includeArena lower upper origin.originalAddress) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base lower,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal lower originalAddress)
            (MotherArenaHigher.includeOriginal lower originalAddress) := by
  have allTargets := fun query => action_target state.calculus (label query)
    (MotherNativeClause.ofState state (label query)).program.generate.output (actions query)
  choose targets targetCompilationEq using allTargets
  let worlds := currentNetworks state label targets
  let currents := currentValues state label targets
  have schemas : ∀ index : Unit ⊕ Index,
      ∃ events : EventFamily (currents index).root.source.base,
      ∃ declaration : Declaration (currents index).root.source.base events,
        assembleLaw declaration = (currents index).root.source.terminalHandoff := fun index =>
    exists_declaration (currents index).root.source.terminalHandoff
  choose events declarations lawSame using schemas
  let RootTotal := Σ index, JointAddress (currents index).root.toAuthoritativeRoot (events index) (declarations index)
  let LowerTotal := (Unit ⊕ Index) ⊕ RootTotal ⊕
    MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ⊕ Index ⊕ Operand state.root ⊕ MotherNetworkFactory.B
  let lower := MotherArenaHigher.carrierRank LowerTotal
  let shared := MotherArenaHigher.carrierAddress LowerTotal
  let currentCode : (Unit ⊕ Index) ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let rootCode : RootTotal ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let headerCode : MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let queryCode : Index ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr (.inr (.inr (.inl value)))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same))))⟩
  let operandCode : Operand state.root ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inl value))))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  let oldCode : MotherNetworkFactory.B ↪ MotherArenaHigher.Base lower :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inr value))))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  obtain ⟨rootMaterial, indices, ⟨currentOrigins⟩⟩ :=
    current_family_at (Unit ⊕ Index) worlds currents events declarations lawSame currentCode rootCode
  obtain ⟨header⟩ := MotherInquirySource.header_origin_at state.U7 state.calculus headerCode
  obtain ⟨queryMaterial, ⟨queries⟩⟩ := MotherAuthorityFamilies.every_index Index queryCode
  obtain ⟨inputMaterial, inputAvailable, authorityFormed, projectionRecovered⟩ :=
    every_inputs label (fun query => MotherNativeClause.ofState state (label query)) queryMaterial queries operandCode
  let parts : LowerParts lower :=
    ⟨rootMaterial, (header.demandMaterial, header.eventMaterial, header.compilerMaterial), queryMaterial, inputMaterial⟩
  let AnswerTotal := Σ query : Index, ULift.{3, 0} (targets query).Answer
  let ReceiptTotal := Σ query : Index, Sigma (targets query).Receipt
  let UpperTotal := AnswerTotal ⊕ ReceiptTotal ⊕ ULift.{3, 0} (MotherArenaHigher.Base lower)
  let upper := MotherReceiptHigher.carrierRank UpperTotal
  let upperShared := MotherReceiptHigher.carrierAddress UpperTotal
  let answerCode : AnswerTotal ↪ MotherReceiptHigher.Base upper :=
    ⟨fun value => upperShared (.inl value), fun _ _ same => Sum.inl.inj (upperShared.injective same)⟩
  let receiptCode : ReceiptTotal ↪ MotherReceiptHigher.Base upper :=
    ⟨fun value => upperShared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (upperShared.injective same))⟩
  let originalAddress : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper :=
    ⟨fun value => upperShared (.inr (.inr (ULift.up value))),
      fun _ _ same => congrArg ULift.down (Sum.inr.inj (Sum.inr.inj (upperShared.injective same)))⟩
  let oneAnswer (query : Index) : (targets query).Answer ↪ MotherReceiptHigher.Base upper :=
    (Equiv.ulift.symm.toEmbedding.trans (Function.Embedding.sigmaMk (β := fun query => ULift.{3, 0} (targets query).Answer) query)).trans answerCode
  let oneReceipt (query : Index) : (Sigma (targets query).Receipt) ↪ MotherReceiptHigher.Base upper :=
    (Function.Embedding.sigmaMk query).trans receiptCode
  have allActions : ∀ query, ∃ actionMaterial : MotherReceiptHigher.Material upper,
      Nonempty (TargetOrigin (currentOrigins (.inl ())) (targets query) (currentOrigins (.inr query)) originalAddress actionMaterial) :=
    fun query => target_origin_at (currentOrigins (.inl ())) (targets query) (currentOrigins (.inr query))
      originalAddress (oneAnswer query) (oneReceipt query)
  choose actionMaterials actionOrigins using allActions
  let origin : Origin lower upper state label targets := {
    materials := parts
    indices := indices
    currents := currentOrigins
    header := header
    header_materials := rfl
    queries := queries
    operandAddress := operandCode
    inputsAvailable := inputAvailable
    authorityFormed := authorityFormed
    projectionRecovered := projectionRecovered
    originalAddress := originalAddress
    targetMaterials := actionMaterials
    targetOrigin := fun query => Classical.choice (actionOrigins query)
    targetCompilation_eq := targetCompilationEq }
  let upperQuery : Index ↪ MotherReceiptHigher.Base upper :=
    ⟨fun query => originalAddress (queries query).val,
      fun _ _ same => queries.injective (Subtype.ext (originalAddress.injective same))⟩
  obtain ⟨material, lowerRecovered, childrenRecovered⟩ :=
    every_material_bundle originalAddress (packLower parts) upperQuery actionMaterials
  exact ⟨lower, upper, material, targets, origin, lowerRecovered, childrenRecovered, origin.readClauses_eq,
    MotherReceiptHigher.restrict_includeArena lower upper originalAddress,
    oldCode, MotherArenaHigher.restrict_includeOriginal lower oldCode⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
