import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Coverage

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {Index : Type}
    {state : RootInquiryStateAt N V} {label : Index → state.Query}
    {targets : Targets state label} {lower : Ordinal.{0}} {upper : Ordinal.{3}}
    (origin : Origin lower upper state label targets)

private theorem clause_compile_heq {root : SourceNativeLivingRootClosure N V}
    {visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot}
    {U7 : U7ProducerCalculus N} {calculus : U7ObstructionEvolutionCalculus N U7}
    {Query : Type} {query : Query}
    {first last : MotherNativeClause.Clause root visit U7 calculus query} (same : first = last) :
    HEq first.program.generate.output last.program.generate.output := by
  cases same
  rfl

/-- The full original compiled value, including every internal action
field, is read from the formed clause at the unchanged original label. -/
theorem Origin.compile_recovers (index : Index) :
    HEq (origin.readClauses index).program.generate.output (state.compileInquiry (label index)) :=
  clause_compile_heq (congrFun origin.readClauses_eq index)

/-- Actual target network, vocabulary and whole living root come from the
same material current family, including all unselected targets. -/
theorem Origin.targetContext_recovers (index : Index) :
    (⟨(origin.targetOrigin index).read.TargetN, (origin.targetOrigin index).read.TargetV,
      (origin.targetOrigin index).read.targetRoot⟩ : Context) = context (origin.currents (.inr index)) := rfl

abbrev ActionIndex (state : RootInquiryStateAt N V) :=
  {query : state.Query // IsAction state.calculus query (state.compileInquiry query)}

/-- No branch premise is imposed on the original state: the entire action
subfamily is selected in coverage and keeps its original query labels. The
full mixed Query carrier is assembled separately by the five-branch source. -/
theorem every_action_fragment (N : WorldRelationNetwork.{0}) (V : ConstructiveRoot.Vocabulary.{0})
    (state : RootInquiryStateAt N V) :
    ∃ lower : Ordinal.{0}, ∃ upper : Ordinal.{3}, ∃ material : MotherReceiptHigher.Material upper,
      ∃ targets : Targets state (Subtype.val : ActionIndex state → state.Query),
      ∃ origin : Origin lower upper state Subtype.val targets,
        readLower origin.originalAddress material = packLower origin.materials ∧
        (∀ index, readChild material (origin.originalAddress (origin.queries index).val) = origin.targetMaterials index) ∧
        (∀ index : ActionIndex state,
          HEq (origin.readClauses index).program.generate.output (state.compileInquiry index.val)) ∧
        Function.LeftInverse (MotherReceiptHigher.restrictArena lower upper origin.originalAddress)
          (MotherReceiptHigher.includeArena lower upper origin.originalAddress) := by
  obtain ⟨lower, upper, material, targets, origin, parentRecovered, childrenRecovered, _clauses,
    retains, _original⟩ := every_action_source N V state (ActionIndex state) Subtype.val (fun index => index.property)
  exact ⟨lower, upper, material, targets, origin, parentRecovered, childrenRecovered, origin.compile_recovers, retains⟩

variable {targets : Targets state id}

/-- Identity labels give the complete original inquiry declaration.
Its current and U7/calculus are actual material readouts as well. -/
def Origin.readInquiry (origin : Origin lower upper state id targets) :
    Σ vocabulary : ConstructiveRoot.Vocabulary.{0}, RootInquiryStateAt N vocabulary :=
  MotherInquirySource.assembleCurrent state (origin.currents (.inl ())).read (origin.currents (.inl ())).read_eq
    (MotherInquirySource.fieldsWithHeader state origin.header.read origin.header.read_eq origin.readClauses)

theorem Origin.readInquiry_eq (origin : Origin lower upper state id targets) : origin.readInquiry = ⟨V, state⟩ :=
  MotherInquirySource.assembleCurrent_recovers state (origin.currents (.inl ())).read (origin.currents (.inl ())).read_eq _
    (MotherInquirySource.fieldsWithHeader_eq state origin.header.read origin.header.read_eq origin.readClauses origin.readClauses_eq)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
