import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Clause
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Target
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Family
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Layout
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ActionQueries.Label
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.HeaderOrigin
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.InquirySource.Assembly

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
open MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open scoped Classical
noncomputable section
variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {Index : Type}

abbrev Targets (state : RootInquiryStateAt N V) (label : Index → state.Query) := (query : Index) →
  TargetAt (root := state.root) (visit := state.visit)
    ⟨(MotherNativeClause.ofState state (label query)).entry, (MotherNativeClause.ofState state (label query)).authority⟩

def currentNetworks (state : RootInquiryStateAt N V) (label : Index → state.Query) (targets : Targets state label) : Unit ⊕ Index → WorldRelationNetwork.{0}
  | .inl _ => N
  | .inr query => (targets query).TargetN

def currentValues (state : RootInquiryStateAt N V) (label : Index → state.Query) (targets : Targets state label) :
    (index : Unit ⊕ Index) → SourceNativeLivingRootCurrentAt (currentNetworks state label targets index)
  | .inl _ => sourceCurrent (root := state.root) (visit := state.visit)
  | .inr query => initialCurrent (targets query).targetRoot

/-- These are coverage witnesses over actual material outputs. No original
program or target field table is an input to a material factory. -/
structure Origin (lower : Ordinal.{0}) (upper : Ordinal.{3})
    (state : RootInquiryStateAt N V) (label : Index → state.Query) (targets : Targets state label) where
  materials : LowerParts lower
  indices : (Unit ⊕ Index) ≃ MotherCurrentFamilies.Member materials.roots
  currents : ∀ index, MotherNativeCurrent.Restriction lower (currentValues state label targets index)
    (MotherCurrentFamilies.atMember materials.roots (indices index))
  header : MotherInquirySource.HeaderOrigin (rank := lower) state.U7 state.calculus
  header_materials : materials.header = (header.demandMaterial, header.eventMaterial, header.compilerMaterial)
  queries : Index ≃ MotherAuthorityFamilies.Member materials.queries
  operandAddress : Operand state.root ↪ MotherArenaHigher.Base lower
  inputsAvailable : (formInputs materials.queries operandAddress materials.inputs).isSome
  authorityFormed : ∀ query,
    let operand := (formInputs materials.queries operandAddress materials.inputs).get inputsAvailable (queries query)
    MotherNativeAuthority.formAtVisit state.root state.visit operand.seed operand.steps =
      some ⟨(MotherNativeClause.ofState state (label query)).entry, (MotherNativeClause.ofState state (label query)).authority⟩
  projectionRecovered : ∀ query,
    ((formInputs materials.queries operandAddress materials.inputs).get inputsAvailable (queries query)).projection =
      (MotherNativeClause.ofState state (label query)).face.projection
  originalAddress : MotherArenaHigher.Base lower ↪ MotherReceiptHigher.Base upper
  targetMaterials : Index → MotherReceiptHigher.Material upper
  targetOrigin : ∀ query, TargetOrigin (currents (.inl ())) (targets query) (currents (.inr query))
    originalAddress (targetMaterials query)
  targetCompilation_eq : ∀ query, targetCompilation state.calculus (label query) (targets query) =
    (MotherNativeClause.ofState state (label query)).program.generate.output

variable {lower : Ordinal.{0}} {upper : Ordinal.{3}} {state : RootInquiryStateAt N V} {label : Index → state.Query} {targets : Targets state label}
    (origin : Origin lower upper state label targets)

def Origin.input (query : Index) : Operand state.root :=
  (formInputs origin.materials.queries origin.operandAddress origin.materials.inputs).get origin.inputsAvailable (origin.queries query)

theorem Origin.authorityAvailable (query : Index) :
    (MotherNativeAuthority.formAtVisit state.root state.visit (origin.input query).seed (origin.input query).steps).isSome := by
  rw [show MotherNativeAuthority.formAtVisit state.root state.visit (origin.input query).seed (origin.input query).steps = _
    from origin.authorityFormed query]
  rfl

def Origin.authority (query : Index) : MotherNativeAuthority.AuthorityTotal state.root state.visit :=
  (MotherNativeAuthority.formAtVisit state.root state.visit (origin.input query).seed (origin.input query).steps).get
    (origin.authorityAvailable query)

theorem Origin.authority_eq (query : Index) : origin.authority query =
    ⟨(MotherNativeClause.ofState state (label query)).entry, (MotherNativeClause.ofState state (label query)).authority⟩ :=
  Option.some.inj ((Option.some_get _).trans (origin.authorityFormed query))

def Origin.clauseResult (query : Index) :
    Option (MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label query)) :=
  formClauseWithAuthority state.calculus (label query) (origin.authority query) (origin.authority_eq query)
    (origin.targetOrigin query).read (origin.input query).projection

theorem Origin.clauseFormed (query : Index) : origin.clauseResult query = some (MotherNativeClause.ofState state (label query)) := by
  apply formClauseWithAuthority_recovers state.calculus (label query)
  · rw [(origin.targetOrigin query).read_eq]
    exact origin.targetCompilation_eq query
  · exact origin.projectionRecovered query

def Origin.readClause (query : Index) : MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label query) :=
  (origin.clauseResult query).get (by rw [origin.clauseFormed query]; rfl)

theorem Origin.readClause_eq (query : Index) : origin.readClause query = MotherNativeClause.ofState state (label query) :=
  Option.some.inj ((Option.some_get _).trans (origin.clauseFormed query))

def Origin.formedClauses (query : MotherAuthorityFamilies.Member origin.materials.queries) :
    MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label (origin.queries.symm query)) :=
  origin.readClause (origin.queries.symm query)

theorem Origin.formedClauses_eq : origin.formedClauses =
    indexClauseEquiv state.calculus label origin.queries (fun query => MotherNativeClause.ofState state (label query)) := by
  funext query
  rw [indexClause_at]
  exact origin.readClause_eq (origin.queries.symm query)

def Origin.readClauses : (query : Index) →
    MotherNativeClause.Clause state.root state.visit state.U7 state.calculus (label query) :=
  (indexClauseEquiv state.calculus label origin.queries).symm origin.formedClauses

theorem Origin.readClauses_eq : origin.readClauses = fun query => MotherNativeClause.ofState state (label query) := by
  unfold Origin.readClauses
  rw [origin.formedClauses_eq, Equiv.symm_apply_apply]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherActionQueries
