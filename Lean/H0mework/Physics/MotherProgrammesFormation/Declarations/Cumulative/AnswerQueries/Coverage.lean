import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AnswerQueries.Origin

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
open MotherHandoffRestriction MotherHandoffSource
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section

/-- All branch operands, the complete original Query carrier, actual label
map, full source current and outer U7 calculus share one internally selected
rank and one material. No fixed-carrier condition is a caller premise. -/
theorem every_answering_source (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) (Index : Type) (label : Index → state.Query)
    (answering : ∀ index, MotherInquiryAnswerClause.Answering state.calculus (label index) (state.compileInquiry (label index))) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ origin : Origin (rank := rank) state label,
        unpack material = origin.materials ∧
        origin.readClauses = (fun index => MotherNativeClause.ofState state (label index)) ∧
        (∀ index, origin.readLabel index = label index) ∧
        origin.readWorldCurrent = ⟨N, MotherInquirySource.currentOf state⟩ ∧
        origin.header.read = ⟨state.U7, state.calculus⟩ ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨events, declaration, lawSame⟩ := exists_declaration state.root.source.terminalHandoff
  let AllAddresses := JointAddress state.root.toAuthoritativeRoot events declaration ⊕
    MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ⊕ state.Query ⊕ Index ⊕
    MotherInquiryAnswerClause.Operand state.root state.visit ⊕ MotherNetworkFactory.B
  let rank := MotherArenaHigher.carrierRank AllAddresses
  let shared := MotherArenaHigher.carrierAddress AllAddresses
  let sourceCode : JointAddress state.root.toAuthoritativeRoot events declaration ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inl value), fun _ _ same => Sum.inl.inj (shared.injective same)⟩
  let headerCode : MotherInquiryU7Header.AddressTotal ⟨state.U7, state.calculus⟩ ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inl value)), fun _ _ same => Sum.inl.inj (Sum.inr.inj (shared.injective same))⟩
  let queryCode : state.Query ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inl value))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))⟩
  let indexCode : Index ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inl value)))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same))))⟩
  let operandCode : MotherInquiryAnswerClause.Operand state.root state.visit ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inl value))))),
      fun _ _ same => Sum.inl.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  let oldCode : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank :=
    ⟨fun value => shared (.inr (.inr (.inr (.inr (.inr value))))),
      fun _ _ same => Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (shared.injective same)))))⟩
  obtain ⟨currentMaterials, currentFormed⟩ :=
    MotherNativeCurrent.current_at_rank (MotherInquirySource.currentOf state) events declaration lawSame sourceCode
  obtain ⟨current⟩ := MotherNativeCurrent.CurrentFormationAt.restriction currentFormed
  obtain ⟨header⟩ := MotherInquirySource.header_origin_at state.U7 state.calculus headerCode
  obtain ⟨queryMaterial, ⟨queries⟩⟩ := MotherAuthorityFamilies.every_index state.Query queryCode
  obtain ⟨indexMaterial, ⟨indices⟩⟩ := MotherAuthorityFamilies.every_index Index indexCode
  obtain ⟨clauseMaterial, available, labelsRecovered, clausesRecovered⟩ :=
    labelled_at_rank state.calculus queryMaterial indexMaterial queries indices label
      (MotherNativeClause.ofState state) answering operandCode
  let materials : Materials rank :=
    ⟨currentMaterials, (header.demandMaterial, header.eventMaterial, header.compilerMaterial), queryMaterial, indexMaterial, clauseMaterial⟩
  let origin : Origin (rank := rank) state label :=
    ⟨materials, current, header, rfl, queries, indices, operandCode, available, labelsRecovered, clausesRecovered⟩
  exact ⟨rank, pack materials, origin, unpack_pack materials, origin.readClauses_eq, origin.readLabel_eq,
    origin.readWorldCurrent_eq, origin.header.read_eq, oldCode, MotherArenaHigher.restrict_includeOriginal rank oldCode⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAnswerQueries
