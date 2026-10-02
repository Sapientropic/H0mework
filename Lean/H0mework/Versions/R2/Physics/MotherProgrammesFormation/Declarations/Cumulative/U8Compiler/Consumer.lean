import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.U8Compiler.Coverage
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.Assembly

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {Index : Type}
    {rank : Ordinal.{0}} {state : RootInquiryStateAt N V} {label : Index → state.Query}
    {data : (index : Index) → Data (MotherNativeClause.ofState state (label index))}
    (origin : Origin rank state label data)

private theorem clause_compile_heq {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query : Type} {query : Query}
    {first last : MotherNativeClause.Clause root visit U7 calculus query} (same : first = last) :
    HEq first.program.generate.output last.program.generate.output := by cases same; rfl

theorem Origin.compile_recovers (index : Index) :
    HEq (origin.readClause index).program.generate.output (state.compileInquiry (label index)) :=
  clause_compile_heq (origin.readClause_eq index)

abbrev U8Index (state : RootInquiryStateAt N V) :=
  {query : state.Query // IsU8 (state.compileInquiry query)}

/-- The whole U8 subfamily is covered at original Query labels. No branch
or address condition is added to the admitted original inquiry state. -/
theorem every_u8_fragment (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ rank : Ordinal.{0}, ∃ material : MotherArenaHigher.Material rank,
      ∃ data : (index : U8Index state) → Data (MotherNativeClause.ofState state index.val),
      ∃ origin : Origin rank state Subtype.val data,
        unpackParts material = origin.parts ∧
        (∀ index : U8Index state, HEq (origin.readClause index).program.generate.output (state.compileInquiry index.val)) ∧
        ∃ originalAddress : MotherNetworkFactory.B ↪ MotherArenaHigher.Base rank,
          Function.LeftInverse (MotherArenaHigher.restrictOriginal rank originalAddress)
            (MotherArenaHigher.includeOriginal rank originalAddress) := by
  obtain ⟨rank, material, data, origin, packed, _clauses, originalAddress, originalRecovered⟩ :=
    every_u8_source state (U8Index state) Subtype.val (fun index => index.property)
  exact ⟨rank, material, data, origin, packed, origin.compile_recovers, originalAddress, originalRecovered⟩

variable {data : (query : state.Query) → Data (MotherNativeClause.ofState state query)}

/-- Identity labels recover the complete U8 inquiry with actual current and
whole U7 header; mixed declarations use the three formed branch subfamilies. -/
def Origin.readInquiry (origin : Origin rank state id data) :
    Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary :=
  MotherInquirySource.assembleCurrent state (origin.roots (.inl ())).read (origin.roots (.inl ())).read_eq
    (MotherInquirySource.fieldsWithHeader state origin.header.read origin.header.read_eq origin.readClause)

theorem Origin.readInquiry_eq (origin : Origin rank state id data) : origin.readInquiry = ⟨V, state⟩ :=
  MotherInquirySource.assembleCurrent_recovers state (origin.roots (.inl ())).read (origin.roots (.inl ())).read_eq _
    (MotherInquirySource.fieldsWithHeader_eq state origin.header.read origin.header.read_eq origin.readClause
      (funext origin.readClause_eq))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherU8Compiler
