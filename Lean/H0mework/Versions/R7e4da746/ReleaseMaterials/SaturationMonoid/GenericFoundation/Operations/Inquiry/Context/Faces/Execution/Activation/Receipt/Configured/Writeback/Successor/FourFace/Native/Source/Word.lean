import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Admission
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source
import H0mework.Versions.Rdf421ff6.Realization.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Consumer
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.OwnerFree.Installation.Inquiry

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations
open SourceOperationScalarInventoryLift SourceOperationScalarPresentation CofinalHistorySettlement DebtActivationWorld
namespace AR
export AdmissionReceipt
  (Admission orderedTerminal orderedOldPartialTrace orderedAdmittedTrace ordered_literal_read terminal_lift_read)
end AR
namespace WR
export WordReceipt (orderedExpression)
end WR
namespace AS
export ActualNativeRelationTransport.AS (stockCfg stockScalar stockDecodedEnvironment)
end AS
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
end A
namespace S
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (answeredState actualOccurrence query query_unique authority entryAt)
end S
namespace J
export RootGeneratedDebtActivationJointSource (register initialEvent mathAction)
export RootGeneratedDebtActivationJointSource.Successor.Inquiry
  (sourceAction sourceAction_eq birthProgram mathState targetRoot)
end J
namespace NR
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt input expression expression_eval budget updated_value residual_value)
end NR
namespace Receipt
export SourceGeneratedInquiryReceiptAction (packetAt)
end Receipt
namespace QI
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Inquiry (state query)
end QI

variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}
variable (frame : A.M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable (base : A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s))
variable (before : Inventory (V := V) (X := X) (s := s)) (oldEnvironment : Env V X)
variable (admissions : List (AR.Admission before (AS.stockScalar frame base)))

abbrev originalState := S.answeredState frame (AS.stockCfg base)
abbrev sourceOccurrence := (originalState frame base).root.emitted (originalState frame base).visit.current
abbrev SourceOccurrence := (originalState frame base).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (originalState frame base).visit.current
abbrev words := admissions.map fun admission => admission.1.word
def sourceWord := liftMap (R := ℤ) (words frame base before admissions).sum
def raw := liftExpr (WR.orderedExpression (words frame base before admissions))
def terminal := liftExpr (AR.orderedTerminal oldEnvironment (words frame base before admissions))
abbrev afterEnvironment := AS.stockDecodedEnvironment frame base
abbrev oldRestriction := pairEnvironment oldEnvironment 0

def material (supplied : SourceOccurrence frame base) :
    NR.MaterialAt (Value := PairValue V) (Var := X) (sort := s) supplied where
  environment := oldRestriction oldEnvironment
  increment := afterEnvironment frame base - oldRestriction oldEnvironment
  raw := raw frame base before admissions
  state := ⟨terminal frame base before oldEnvironment admissions,
    AR.orderedOldPartialTrace oldEnvironment before (AS.stockScalar frame base) admissions⟩
  owner := S.entryAt frame supplied

abbrev actualMaterial := material frame base before oldEnvironment admissions (sourceOccurrence frame base)
def request := J.register fun supplied : SourceOccurrence frame base =>
  NR.input (material frame base before oldEnvironment admissions supplied)

def reader : {current : (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
    frame.registered frame.packetAt).Current} →
    (originalState frame base).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current →
    RootGeneratedDebtActivationJointSource.OwnerFree.Raw (Value := PairValue V) (Var := X) (sort := s) :=
  fun {_current} _ => ⟨afterEnvironment frame base,
    (request frame base before oldEnvironment admissions).input.expression⟩
def betaState := QI.state (originalState frame base) (reader frame base before oldEnvironment admissions)
def betaQuery := QI.query (originalState frame base) (reader frame base before oldEnvironment admissions)
  (S.query frame (AS.stockCfg base))

private theorem beta_query_unique (candidate : (betaState frame base before oldEnvironment admissions).Query) :
    candidate = betaQuery frame base before oldEnvironment admissions := by
  rcases candidate with ⟨incidence, occurrence, raw, occurrence_eq, raw_eq⟩
  cases S.query_unique frame (AS.stockCfg base) incidence
  cases occurrence_eq
  cases raw_eq
  rfl

theorem request_environment : (request frame base before oldEnvironment admissions).input.environment =
    afterEnvironment frame base := add_sub_cancel _ _

theorem request_expression : (request frame base before oldEnvironment admissions).input.expression =
    Expr.add (raw frame base before admissions)
      (.linear (-AddMonoidHom.id (PairValue V s)) (terminal frame base before oldEnvironment admissions)) := rfl

def currentTrace : Trace (afterEnvironment frame base) (raw frame base before admissions)
    (.const (evaluation (R := ℤ) (afterEnvironment frame base) (sourceWord frame base before admissions))) :=
  AR.orderedAdmittedTrace _ _ _ admissions

theorem actual_updated_value : (request frame base before oldEnvironment admissions).input.expression.eval
    (request frame base before oldEnvironment admissions).input.environment =
    evaluation (R := ℤ) (afterEnvironment frame base) (sourceWord frame base before admissions) -
      (evaluation (R := ℤ) oldEnvironment (words frame base before admissions).sum, 0) := by
  change (NR.expression (actualMaterial frame base before oldEnvironment admissions)).eval _ = _
  rw [NR.expression_eval, request_environment]
  exact congrArg₂ (· - ·)
    (AR.ordered_literal_read (words frame base before admissions) (afterEnvironment frame base))
    (AR.terminal_lift_read oldEnvironment (afterEnvironment frame base) (words frame base before admissions))

theorem source_effect : type_of% (NR.updated_value (R := ℤ)
    (actualMaterial frame base before oldEnvironment admissions)) := NR.updated_value (R := ℤ) _
theorem source_inverse : type_of% (NR.residual_value (R := ℤ)
    (actualMaterial frame base before oldEnvironment admissions)) := NR.residual_value (R := ℤ) _

private theorem not_settled (settled : SourceOperationExecutionDebt.Settlement
    (J.initialEvent (request frame base before oldEnvironment admissions)).state) : False := by
  have zero := (RootGeneratedDebtActivationJointSource.Idle.law
    (request frame base before oldEnvironment admissions).input.environment
    (request frame base before oldEnvironment admissions).input.expression).settlement_budget_zero settled
  have sourceBudget := NR.budget (actualMaterial frame base before oldEnvironment admissions)
  change remaining (NR.expression (actualMaterial frame base before oldEnvironment admissions)) = 0 at zero
  omega

def firstStep := match _selected : J.mathAction (J.initialEvent (request frame base before oldEnvironment admissions)) with
  | .inl settled => False.elim (not_settled frame base before oldEnvironment admissions settled)
  | .inr paid => paid

theorem first_action : J.sourceAction (betaState frame base before oldEnvironment admissions)
    (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base)) =
    .inr (firstStep frame base before oldEnvironment admissions) := by
  apply (J.sourceAction_eq (betaState frame base before oldEnvironment admissions)
    (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))).trans
  unfold firstStep
  cases actual : J.mathAction (J.initialEvent (request frame base before oldEnvironment admissions)) with
  | inl settled => exact False.elim (not_settled frame base before oldEnvironment admissions settled)
  | inr paid => rfl

/-- This source calculation query has the original inquiry only as its ownership incidence. -/
def bareBirthProgram := J.birthProgram (betaState frame base before oldEnvironment admissions)
  (betaQuery frame base before oldEnvironment admissions)
  (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))
  ((betaState frame base before oldEnvironment admissions).authorityAt (betaQuery frame base before oldEnvironment admissions))
  (firstStep frame base before oldEnvironment admissions)
  (first_action frame base before oldEnvironment admissions)

/-- The parent origin stays explicit; no target occurrence is relabelled as that origin. -/
structure OriginMaterialAt (origin : SourceOccurrence frame base) where
  occurrences : List (AR.Admission before (AS.stockScalar frame base))
  word : Formal ℤ (PairValue V) X s
  oldConstants : V s →₀ ℤ
  newConstants : PairValue V s →₀ ℤ
  native : NR.MaterialAt (Value := PairValue V) (Var := X) (sort := s) origin
  newTrace : Trace (afterEnvironment frame base) native.raw
    (.const (evaluation (R := ℤ) (afterEnvironment frame base) word))

def originMaterialAt (origin : SourceOccurrence frame base) : OriginMaterialAt frame base before origin where
  occurrences := admissions
  word := sourceWord frame base before admissions
  oldConstants := valueMap (R := ℤ) oldEnvironment (words frame base before admissions).sum
  newConstants := valueMap (R := ℤ) (afterEnvironment frame base) (sourceWord frame base before admissions)
  native := material frame base before oldEnvironment admissions origin
  newTrace := currentTrace frame base before admissions

abbrev bareTargetRoot := J.targetRoot (betaState frame base before oldEnvironment admissions)
  (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))
abbrev TargetOccurrence {current : (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
    (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))).Current} :=
  (bareTargetRoot frame base before oldEnvironment admissions).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current

structure TargetMaterialAt
    {current : (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
      (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))).Current}
    (_occurrence : TargetOccurrence frame base before oldEnvironment admissions (current := current)) where
  origin : SourceOccurrence frame base
  origin_eq : origin = sourceOccurrence frame base
  source : OriginMaterialAt frame base before origin
  state : SourceOperationExecutionDebt.State (request frame base before oldEnvironment admissions).input.environment
    (request frame base before oldEnvironment admissions).input.expression
  state_eq : state = current.2.state

def targetMaterialAt
    {current : (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV
      (request frame base before oldEnvironment admissions) (Receipt.packetAt frame (AS.stockCfg base))).Current}
    (occurrence : TargetOccurrence frame base before oldEnvironment admissions (current := current)) :
    TargetMaterialAt frame base before oldEnvironment admissions occurrence := by
  rcases occurrence with ⟨support, event⟩
  cases event
  exact ⟨sourceOccurrence frame base, rfl,
    originMaterialAt frame base before oldEnvironment admissions (sourceOccurrence frame base), current.2.state, rfl⟩

def originLaw : SourceNativeProjectionLaw
    (bareTargetRoot frame base before oldEnvironment admissions).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit
  ActiveAt := fun _ {_current} _ => PUnit
  InactiveAt := fun _ {_current} _ => PEmpty
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} occurrence _ => TargetMaterialAt frame base before oldEnvironment admissions occurrence
  project := fun _ {_current} occurrence _ => targetMaterialAt frame base before oldEnvironment admissions occurrence

def originInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (bareTargetRoot frame base before oldEnvironment admissions).source.base
  (originLaw frame base before oldEnvironment admissions)

def completeTargetAt (event : ExactTemporalCausalRootEventAt
    (betaState frame base before oldEnvironment admissions).root.toAuthoritativeRoot.toLedgerRoot
    (betaState frame base before oldEnvironment admissions).visit) :=
  SourceOperationInquiry.Context.Faces.Execution.Activation.targetCoface
    ((bareBirthProgram frame base before oldEnvironment admissions).targetAt event)
    (originLaw frame base before oldEnvironment admissions)

def birthProgram : type_of% (bareBirthProgram frame base before oldEnvironment admissions) where
  targetAt := completeTargetAt frame base before oldEnvironment admissions

def sourceEvent := (betaState frame base before oldEnvironment admissions).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (betaState frame base before oldEnvironment admissions).visit
def generatedAction := (birthProgram frame base before oldEnvironment admissions).generate
  (sourceEvent frame base before oldEnvironment admissions)

def compilation (candidate : (betaState frame base before oldEnvironment admissions).Query) : SourceNativeInquiryCompilationProgramAt
    (betaState frame base before oldEnvironment admissions).root (betaState frame base before oldEnvironment admissions).visit
    (betaState frame base before oldEnvironment admissions).U7 (betaState frame base before oldEnvironment admissions).calculus
    (betaState frame base before oldEnvironment admissions).root.source.base.lawSurface candidate
    ((betaState frame base before oldEnvironment admissions).emitInquiry candidate)
    ((betaState frame base before oldEnvironment admissions).entryAt candidate)
    ((betaState frame base before oldEnvironment admissions).authorityAt candidate) where
  compile := fun event => by
    cases beta_query_unique frame base before oldEnvironment admissions candidate
    exact .debtAdmission ((birthProgram frame base before oldEnvironment admissions).generate event)

def state : RootInquiryStateAt
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered)
    (RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt) where
  root := (betaState frame base before oldEnvironment admissions).root
  visit := (betaState frame base before oldEnvironment admissions).visit
  U7 := (betaState frame base before oldEnvironment admissions).U7
  calculus := (betaState frame base before oldEnvironment admissions).calculus
  Query := (betaState frame base before oldEnvironment admissions).Query
  entryAt := (betaState frame base before oldEnvironment admissions).entryAt
  authorityAt := (betaState frame base before oldEnvironment admissions).authorityAt
  compilationProgramAt := compilation frame base before oldEnvironment admissions
  compilationFaceAt := fun candidate => by
    cases beta_query_unique frame base before oldEnvironment admissions candidate
    exact { projection := ((betaState frame base before oldEnvironment admissions).compilationFaceAt
              (betaQuery frame base before oldEnvironment admissions)).projection
            active := ((betaState frame base before oldEnvironment admissions).compilationFaceAt
              (betaQuery frame base before oldEnvironment admissions)).active
            classifier_eq := ((betaState frame base before oldEnvironment admissions).compilationFaceAt
              (betaQuery frame base before oldEnvironment admissions)).classifier_eq
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro candidate _ _ impossible
    cases beta_query_unique frame base before oldEnvironment admissions candidate
    exact nomatch impossible

theorem same_root : (state frame base before oldEnvironment admissions).root =
    (betaState frame base before oldEnvironment admissions).root := rfl
theorem same_ledger : (state frame base before oldEnvironment admissions).root.toAuthoritativeRoot.toLedgerRoot =
    (originalState frame base).root.toAuthoritativeRoot.toLedgerRoot := rfl
theorem same_visit : (state frame base before oldEnvironment admissions).visit = (originalState frame base).visit := rfl
theorem compiles : (state frame base before oldEnvironment admissions).compileInquiry (betaQuery frame base before oldEnvironment admissions) =
    .debtAdmission (generatedAction frame base before oldEnvironment admissions) := rfl

def sourcePresentation : RootInquiryStatePresentation where
  N := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.World frame.registered
  V := RootGeneratedDebtActivationJointSource.Successor.CompilerFromPacketSourceLaw.JointV frame.registered frame.packetAt
  state := .create (state frame base before oldEnvironment admissions)

theorem canonical_next : (generatedAction frame base before oldEnvironment admissions).target.targetAnswerAndNext.nextCurrent =
    ⟨(generatedAction frame base before oldEnvironment admissions).target.TargetV,
     (generatedAction frame base before oldEnvironment admissions).target.targetRoot.toAuthoritativeRoot,
     (generatedAction frame base before oldEnvironment admissions).target.targetVisit⟩ :=
  (generatedAction frame base before oldEnvironment admissions).target.targetAnswerAndNext_next_eq

def nextOriginFace : SourceNativeRootSemanticFaceAt
    (generatedAction frame base before oldEnvironment admissions).target.targetRoot
    (generatedAction frame base before oldEnvironment admissions).target.targetVisit where
  projection := (originInstallation frame base before oldEnvironment admissions).embed PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem next_source_word : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.word =
    sourceWord frame base before admissions := rfl
theorem next_old_constants : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.oldConstants =
    valueMap (R := ℤ) oldEnvironment (words frame base before admissions).sum := rfl
theorem next_new_constants : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.newConstants =
    valueMap (R := ℤ) (afterEnvironment frame base) (sourceWord frame base before admissions) := rfl
theorem next_source_occurrences : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.occurrences =
    admissions := rfl

def nextDifferential : PairValue V s :=
  (nextOriginFace frame base before oldEnvironment admissions).rootRead.state.1.eval
    (request frame base before oldEnvironment admissions).input.environment

theorem next_differential_value : nextDifferential frame base before oldEnvironment admissions =
    (request frame base before oldEnvironment admissions).input.expression.eval
      (request frame base before oldEnvironment admissions).input.environment :=
  (nextOriginFace frame base before oldEnvironment admissions).rootRead.state.2.sound.symm

def nextFullValue : PairValue V s :=
  (ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s)
    (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.oldConstants, 0) +
  nextDifferential frame base before oldEnvironment admissions

/-- The actual next paid state contributes the differential; the stored free certificate restores the full update. -/
theorem next_full_value : nextFullValue frame base before oldEnvironment admissions =
    evaluation (R := ℤ) (afterEnvironment frame base) (sourceWord frame base before admissions) := by
  unfold nextFullValue
  rw [next_differential_value, next_old_constants, actual_updated_value]
  have old := LinearMap.congr_fun (valueMap_evaluation (R := ℤ) oldEnvironment)
    (words frame base before admissions).sum
  change ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s)
    (valueMap (R := ℤ) oldEnvironment (words frame base before admissions).sum) = _ at old
  rw [old]
  abel

theorem next_full_certificate : nextFullValue frame base before oldEnvironment admissions =
    ScalarRelationPresentation.freeEvaluation (R := ℤ) (PairValue V s)
      (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.newConstants := by
  rw [next_full_value, next_new_constants]
  exact (LinearMap.congr_fun (valueMap_evaluation (R := ℤ) (afterEnvironment frame base))
    (sourceWord frame base before admissions)).symm

theorem answered_next : (RootInquiryProcessNode.answered (sourcePresentation frame base before oldEnvironment admissions)
    (betaQuery frame base before oldEnvironment admissions)).erase =
    (⟨(generatedAction frame base before oldEnvironment admissions).target.TargetN,
      (generatedAction frame base before oldEnvironment admissions).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent.{u}) := rfl

theorem whole_first : type_of% (generatedAction frame base before oldEnvironment admissions).target.firstDestination_heq :=
  (generatedAction frame base before oldEnvironment admissions).target.firstDestination_heq

end SourceInventoryExecutionFeed.SourceWordNative
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
