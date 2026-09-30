import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Origin

set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open MotherHandoffRestriction MotherHandoffSource MotherU8Revision
open scoped Classical
noncomputable section

/-- Every labelled U8 clause, both complete U7 calculi, the source and all
revised roots enter one sufficient rank and one mother material together. -/
theorem every_u8_source {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (state : RootInquiryStateAt N V) (Index : Type) (label : Index → state.Query)
    (u8 : ∀ index, IsU8 (MotherNativeClause.ofState state (label index)).program.generate.output) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ data : (index : Index) → Data (MotherNativeClause.ofState state (label index)),
      ∃ origin : Origin rank state label data,
        unpackParts material = origin.parts ∧
        (∀ index, origin.readClause index = MotherNativeClause.ofState state (label index)) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  let data : (index : Index) → Data (MotherNativeClause.ofState state (label index)) :=
    fun index => Classical.choice (exists_data _ (u8 index))
  have schemas : ∀ index : Unit ⊕ Index, ∃ events : EventFamily (currents state label data index).root.source.base,
      ∃ declaration : Declaration (currents state label data index).root.source.base events,
        assembleLaw declaration = (currents state label data index).root.source.terminalHandoff :=
    fun index => exists_declaration (currents state label data index).root.source.terminalHandoff
  choose events declarations lawSame using schemas
  let AllAddresses := (Unit ⊕ Index) ⊕
    (Σ index, JointAddress (currents state label data index).root.toAuthoritativeRoot (events index) (declarations index)) ⊕
    MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ⊕
    (Σ index, MotherInquiryU7Header.AddressTotal ⟨state.U7, (data index).core.frontier.face.calculus⟩) ⊕
    Operand state.root state.visit ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let rootIndexCode : (Unit ⊕ Index) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let rootCode : (Σ index, JointAddress (currents state label data index).root.toAuthoritativeRoot
      (events index) (declarations index)) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let headerCode : MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let faceCode : (Σ index, MotherInquiryU7Header.AddressTotal
      ⟨state.U7, (data index).core.frontier.face.calculus⟩) ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inl value)))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same))))⟩
  let operandCode : Operand state.root state.visit ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inl value))))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  let originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inr value))))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  obtain ⟨rootsMaterial, rootIndices, ⟨roots⟩⟩ := MotherActionQueries.current_family_at
    (Unit ⊕ Index) (networks state label data) (currents state label data) events declarations lawSame rootIndexCode rootCode
  obtain ⟨header⟩ := MotherInquirySource.header_origin_at state.U7 state.calculus headerCode
  have faces : ∀ index, Nonempty (MotherInquirySource.HeaderOrigin (rank := rank)
      state.U7 (data index).core.frontier.face.calculus) := fun index =>
    MotherInquirySource.header_origin_at state.U7 (data index).core.frontier.face.calculus
      ((Function.Embedding.sigmaMk index).trans faceCode)
  let face := fun index => Classical.choice (faces index)
  let indexCode : Index ↪ MotherArenaHigher.Base rank :=
    ⟨fun index => rootIndexCode (.inr index), fun _ _ same => Sum.inr.inj (rootIndexCode.injective same)⟩
  obtain ⟨indexMaterial, ⟨indices⟩⟩ := MotherAuthorityFamilies.every_index Index indexCode
  let actualIndexCode := indices.toEmbedding.trans (memberCode indexMaterial)
  have clauses : ∀ index, ∃ operand : Operand state.root state.visit,
      ∃ body : MotherArenaHigher.Material rank,
        formAtContext state label data (roots (.inl ())) header index (roots (.inr index)) (face index) operand body =
          some (MotherNativeClause.ofState state (label index)) := by
    intro index
    obtain ⟨operand, body, formed⟩ := every_clause_at_core state.calculus (label index)
      (MotherNativeClause.ofState state (label index)) (data index).obstruction (data index).gate
      (data index).failure (data index).core (data index).compiled_eq
      (currentCoordinates (roots (.inl ()))) (currentOccurrence (roots (.inl ())))
      ⟨currentCoordinates (roots (.inr index)), currentOccurrence (roots (.inr index))
        (data index).core.revision.generate.newLivingRoot.toAuthoritativeRoot.toRoot.source.initial⟩
    exact ⟨operand, body, (formAtContext_eq state label data (roots (.inl ())) header index
      (roots (.inr index)) (face index) operand body).trans formed⟩
  choose operands bodies clauseFormed using clauses
  obtain ⟨inputMaterial, inputsFormed⟩ := every_inputs indexMaterial operandCode (fun index => operands (indices.symm index))
  have inputsAvailable : (formInputs indexMaterial operandCode inputMaterial).isSome := by rw [inputsFormed]; rfl
  have inputsEq : (formInputs indexMaterial operandCode inputMaterial).get inputsAvailable =
      fun index => operands (indices.symm index) := Option.some.inj ((Option.some_get _).trans inputsFormed)
  let children : Index → Child rank := fun index =>
    ⟨((face index).demandMaterial, (face index).eventMaterial, (face index).compilerMaterial), bodies index⟩
  obtain ⟨childrenMaterial, childrenFormed⟩ := every_children actualIndexCode children rootsMaterial
  let parts : Parts rank :=
    ⟨rootsMaterial, (header.demandMaterial, header.eventMaterial, header.compilerMaterial), indexMaterial, inputMaterial, childrenMaterial⟩
  have faceMaterials : ∀ index, (childAt parts.children (indices index).val).face =
      ((face index).demandMaterial, (face index).eventMaterial, (face index).compilerMaterial) := by
    intro index
    exact congrArg Child.face (childrenFormed index)
  have formed : ∀ index, formAtContext state label data (roots (.inl ())) header index (roots (.inr index)) (face index)
      ((formInputs parts.indices operandCode parts.inputs).get inputsAvailable (indices index))
      (childAt parts.children (indices index).val).body = some (MotherNativeClause.ofState state (label index)) := by
    intro index
    have bodyEq : (childAt parts.children (indices index).val).body = bodies index := congrArg Child.body (childrenFormed index)
    rw [inputsEq]
    dsimp only
    erw [Equiv.symm_apply_apply, bodyEq]
    exact clauseFormed index
  let origin : Origin rank state label data :=
    ⟨parts, rootIndices, roots, header, rfl, indices, operandCode, inputsAvailable, face, faceMaterials, formed⟩
  exact ⟨rank, origin.material, data, origin, origin.material_parts, origin.readClause_eq,
    originalAddress, MotherArenaHigher.restrict_includeOriginal rank originalAddress⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
