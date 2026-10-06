import H0mework.Versions.AB.Realization.Operations.Tree.Consumer
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry
import H0mework.Versions.AB.Foundation.Responsibility.JointSource.OwnerFree.Payment

/-! A supplied source occurrence determines its entire tree before the
emitter. The original inquiry installer executes its constructor programme
and preserves the original compilation and complete source material. -/

set_option autoImplicit false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Installation
open ArithmeticGeneration SourceOperationEffects SourceOperationExecution RootInquiryCompletion
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry
  (query state root visit resultFace result_value result_history compiles presentation answered_next
   original_compilation_preserved CalculationQuery)
end I
end O
variable {N : WorldRelationNetwork} {V : Vocabulary}
variable (old : RootInquiryStateAt N V)
abbrev Occurrence (current : V.Current) :=
  old.root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

structure TreeReadAt {current : V.Current} (occurrence : Occurrence old current) : Type where
  projection : old.root.source.base.projectionLaw.Projection
  active : old.root.source.base.projectionLaw.ActiveAt projection occurrence
  classifier_eq : old.root.source.base.projectionLaw.classify projection occurrence = .inl active
  payload_eq : old.root.source.base.projectionLaw.PayloadAt projection occurrence active =
    RootedAccountedUnfolding UnitHistory

variable (source : {current : V.Current} → (occurrence : Occurrence old current) → TreeReadAt old occurrence)

def treeAt {current : V.Current} (occurrence : Occurrence old current) : RootedAccountedUnfolding UnitHistory :=
  Eq.mp (source occurrence).payload_eq (old.root.source.base.projectionLaw.project
    (source occurrence).projection occurrence (source occurrence).active)

def reader {current : V.Current} (occurrence : Occurrence old current) :
    O.Raw (Value := Value) (Var := Var) (sort := .result) :=
  ⟨environment, program (treeAt old source occurrence)⟩

variable (incidence : SourceNativeRootInquiryInputAt old.root old.visit old.Query)

abbrev query := O.I.query old (reader old source) incidence.query
abbrev inquiry := O.I.state old (reader old source)
abbrev resultFace := O.I.resultFace old (reader old source)

theorem actual_value : (resultFace old source).rootRead.2.2.1 =
    Finsupp.single (CanonicalUnitArithmeticRoot.nativeActionTarget
      (treeAt old source (old.root.emitted old.visit.current))) 1 :=
  (O.I.result_value old (reader old source)).trans (program_source _)

theorem actual_cost : (resultFace old source).rootRead.2.1.2.length =
    budget (treeAt old source (old.root.emitted old.visit.current)) :=
  (O.I.result_history old (reader old source)).trans (program_budget _)

def queryLaw : SourceNativeProjectionLaw (inquiry old source).root.source.base.restructuringSource.toLedgerSource where
  Projection := Bool
  ActiveAt := fun projection {_current} occurrence => match projection with
    | false => PLift (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.exactOccurrence old occurrence)
    | true => PUnit
  InactiveAt := fun projection {_current} occurrence => match projection with
    | false => PLift (¬ RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.exactOccurrence old occurrence)
    | true => PEmpty
  classify := by
    classical
    intro projection current occurrence
    cases projection with
    | false => exact if same : RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.exactOccurrence old occurrence
      then .inl ⟨same⟩ else .inr ⟨same⟩
    | true => exact .inl PUnit.unit
  PayloadAt := fun projection {_current} _ _ => match projection with
    | false => O.I.CalculationQuery old (reader old source)
    | true => RootedAccountedUnfolding UnitHistory
  project := fun projection {_current} occurrence _ => match projection with
    | false => query old source incidence
    | true => treeAt old source occurrence

abbrev inputRoot := (inquiry old source).root.withProjectionCoface (queryLaw old source incidence)
abbrev inputVisit : SourceNativeTemporalVisitAt (inputRoot old source incidence).toAuthoritativeRoot.toLedgerRoot :=
  (inquiry old source).visit

def queryInput : SourceNativeRootInquiryInputAt (inputRoot old source incidence) (inputVisit old source incidence)
    (O.I.CalculationQuery old (reader old source)) where
  projection := .component false
  active := ⟨rfl⟩
  classifier_eq := by
    classical
    change (queryLaw old source incidence).classify false (old.root.emitted old.visit.current) = .inl ⟨rfl⟩
    change (if same : RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.exactOccurrence old
      (old.root.emitted old.visit.current) then Sum.inl (PLift.up same) else Sum.inr (PLift.up same)) = _
    exact dif_pos (show RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.exactOccurrence old
      (old.root.emitted old.visit.current) from rfl)
  queryType_eq := rfl

theorem query_from_source : (queryInput old source incidence).query = query old source incidence := rfl

def inputResultFace : SourceNativeRootSemanticFaceAt (inputRoot old source incidence)
    (inputVisit old source incidence) where
  projection := .inherited (resultFace old source).projection
  active := (resultFace old source).active
  classifier_eq := (resultFace old source).classifier_eq

def inputConsumer (candidate : O.I.CalculationQuery old (reader old source)) :
    SourceNativeInquiryAnswerConsumerAt (root := inputRoot old source incidence) (visit := inputVisit old source incidence)
      candidate (ULift.up ((inputRoot old source incidence).emitted (inputVisit old source incidence).current))
      (old.entryAt candidate.incidence) (inputResultFace old source incidence) where
  projection := .inherited (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer
    old (reader old source) candidate).projection
  active := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer
    old (reader old source) candidate).active
  classifier_eq := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer
    old (reader old source) candidate).classifier_eq
  project_heq := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.consumer
    old (reader old source) candidate).project_heq

def inputAuthority (candidate : O.I.CalculationQuery old (reader old source)) :=
  ((inquiry old source).authorityAt candidate).withProjectionCoface (queryLaw old source incidence)

def inputCompilation (candidate : O.I.CalculationQuery old (reader old source)) :
    SourceNativeInquiryCompilationProgramAt (inputRoot old source incidence) (inputVisit old source incidence)
      old.U7 old.calculus old.root.source.base.lawSurface candidate
      (ULift.up ((inputRoot old source incidence).emitted (inputVisit old source incidence).current))
      (old.entryAt candidate.incidence) (inputAuthority old source incidence candidate) where
  compile := fun _ => .answered (inputResultFace old source incidence) (inputConsumer old source incidence candidate)

def inputState : RootInquiryStateAt N V where
  root := inputRoot old source incidence
  visit := inputVisit old source incidence
  U7 := old.U7
  calculus := old.calculus
  Query := O.I.CalculationQuery old (reader old source)
  entryAt := fun candidate => old.entryAt candidate.incidence
  authorityAt := inputAuthority old source incidence
  compilationProgramAt := inputCompilation old source incidence
  compilationFaceAt := fun candidate => {
    projection := .inherited ((inquiry old source).compilationFaceAt candidate).projection
    active := ((inquiry old source).compilationFaceAt candidate).active
    classifier_eq := ((inquiry old source).compilationFaceAt candidate).classifier_eq
    project_heq := ((inquiry old source).compilationFaceAt candidate).project_heq }
  u7RootDisposition_commutes := by
    intro _ _ _ impossible
    exact nomatch impossible

def treeFace : SourceNativeRootSemanticFaceAt (inputRoot old source incidence) (inputVisit old source incidence) where
  projection := .component true
  active := PUnit.unit
  classifier_eq := rfl

theorem tree_source : (treeFace old source incidence).rootRead =
    treeAt old source (old.root.emitted old.visit.current) := rfl

theorem input_value : (inputResultFace old source incidence).rootRead.2.2.1 =
    Finsupp.single (CanonicalUnitArithmeticRoot.nativeActionTarget (treeFace old source incidence).rootRead) 1 :=
  actual_value old source

theorem input_cost : (inputResultFace old source incidence).rootRead.2.1.2.length =
    budget (treeFace old source incidence).rootRead := actual_cost old source

def originalCompilationFace (original : old.Query) : SourceNativeRootSemanticFaceAt
    (inputRoot old source incidence) (inputVisit old source incidence) where
  projection := .inherited (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.originalCompilationFace
    old (reader old source) original).projection
  active := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.originalCompilationFace
    old (reader old source) original).active
  classifier_eq := (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.originalCompilationFace
    old (reader old source) original).classifier_eq

theorem original_compilation (original : old.Query) :
    type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.original_compilation_preserved
      old (reader old source) original) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry.original_compilation_preserved
    old (reader old source) original

end SourceOperationNative.Tree.Installation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
