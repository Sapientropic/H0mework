import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Context.Faces.Execution.Activation.Receipt.Configured.Writeback.Successor.FourFace.Native.Source.Word.Reentry.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
namespace Q
export SourceOperationInquiry.Context.Faces.Execution.Activation.Shared
  (Query query query_unique resultFace consumer compilationInstallation base root visit datum)
end Q
namespace J
export RootGeneratedDebtActivationJointSource.Successor.Inquiry
  (mathAuthority sourceAction sourceAction_eq targetAt)
end J
namespace CF
export SourceGeneratedInquiryReceiptAction.Configured (lowInitial lowProgramme)
end CF
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (epoch targetCoface optionalTargetCoface)
end A

variable {Sorts : Type u} {V X : Sorts → Type u} [∀ target, AddCommGroup (V target)] {s : Sorts}
variable (frame : Reentry.A.M.Frame (Value := PairValue V) (Var := X) (sort := s))
variable (base : Reentry.A.Programme (PhysicalValue := PairValue V) (PhysicalVar := X) (sort := s))
variable (before : Inventory (V := V) (X := X) (s := s)) (oldEnvironment : Env V X)
variable (admissions : List (AdmissionReceipt.Admission before (Reentry.AS.stockScalar frame base)))

def live := { Reentry.initial frame base before oldEnvironment admissions with
  depth := (Reentry.selected frame base before oldEnvironment admissions).depth }

theorem live_is_selected : live frame base before oldEnvironment admissions =
    Reentry.selected frame base before oldEnvironment admissions :=
  (Reentry.selected_frame frame base before oldEnvironment admissions).symm

abbrev cfg := Reentry.programme frame base before oldEnvironment admissions
abbrev originalRoot := (SourceWordNative.generatedAction frame base before oldEnvironment admissions).target.targetRoot
abbrev materialRoot := Q.root (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)

/-- The old complete inventory and the new material inventory share the actual compiler source. -/
def root := (originalRoot frame base before oldEnvironment admissions).withProjectionCoface
  (materialRoot frame base before oldEnvironment admissions).source.base.projectionLaw

def oldInstallation := SourceNativeProjectionLaw.InstallationAt.inheritedCoface
  (originalRoot frame base before oldEnvironment admissions).source.base
  (materialRoot frame base before oldEnvironment admissions).source.base.projectionLaw

def materialInstallation := SourceNativeProjectionLaw.InstallationAt.componentCoface
  (originalRoot frame base before oldEnvironment admissions).source.base
  (materialRoot frame base before oldEnvironment admissions).source.base.projectionLaw

abbrev visit := Q.visit (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)
abbrev Query := Q.Query (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)
abbrev query := Q.query (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)
abbrev entry := (live frame base before oldEnvironment admissions).currentState.entryAt PUnit.unit

def authority :=
  (J.mathAuthority (SourceWordNative.betaState frame base before oldEnvironment admissions)
    (Reentry.betaRequest frame base before oldEnvironment admissions)
    (Reentry.R.packetAt frame (Reentry.AS.stockCfg base))
    (Reentry.selected frame base before oldEnvironment admissions).depth).withProjectionCoface
      (SourceWordNative.originLaw frame base before oldEnvironment admissions)
    |>.withProjectionCoface (materialRoot frame base before oldEnvironment admissions).source.base.projectionLaw

def resultFace : SourceNativeRootSemanticFaceAt (root frame base before oldEnvironment admissions)
    (visit frame base before oldEnvironment admissions) where
  projection := (materialInstallation frame base before oldEnvironment admissions).embed
    (Q.resultFace (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)).projection
  active := PUnit.unit
  classifier_eq := rfl

def consumer : SourceNativeInquiryAnswerConsumerAt
    (root := root frame base before oldEnvironment admissions) (visit := visit frame base before oldEnvironment admissions)
    (query frame base before oldEnvironment admissions)
    (ULift.up.{u + 1, u} ((root frame base before oldEnvironment admissions).emitted
      (visit frame base before oldEnvironment admissions).current))
    (entry frame base before oldEnvironment admissions) (resultFace frame base before oldEnvironment admissions) where
  projection := (materialInstallation frame base before oldEnvironment admissions).embed
    (Q.consumer (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)).projection
  active := PUnit.unit
  classifier_eq := rfl
  project_heq := HEq.rfl

def answeredCompilation : SourceNativeInquiryCompilationProgramAt
    (root frame base before oldEnvironment admissions) (visit frame base before oldEnvironment admissions)
    (Q.base (live frame base before oldEnvironment admissions)).U7
    (Q.base (live frame base before oldEnvironment admissions)).calculus
    (root frame base before oldEnvironment admissions).source.base.lawSurface
    (query frame base before oldEnvironment admissions)
    (ULift.up.{u + 1, u} ((root frame base before oldEnvironment admissions).emitted
      (visit frame base before oldEnvironment admissions).current))
    (entry frame base before oldEnvironment admissions) (authority frame base before oldEnvironment admissions) where
  compile := fun _ => .answered (resultFace frame base before oldEnvironment admissions)
    (consumer frame base before oldEnvironment admissions)

def answeredState : RootInquiryStateAt
    (Reentry.C.World (Reentry.betaRequest frame base before oldEnvironment admissions))
    (Reentry.C.JointV (Reentry.betaRequest frame base before oldEnvironment admissions)
      (Reentry.R.packetAt frame (Reentry.AS.stockCfg base))) where
  root := root frame base before oldEnvironment admissions
  visit := visit frame base before oldEnvironment admissions
  U7 := (Q.base (live frame base before oldEnvironment admissions)).U7
  calculus := (Q.base (live frame base before oldEnvironment admissions)).calculus
  Query := Query frame base before oldEnvironment admissions
  entryAt := fun _ => entry frame base before oldEnvironment admissions
  authorityAt := fun _ => authority frame base before oldEnvironment admissions
  compilationProgramAt := fun candidate =>
    Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate ▸
      answeredCompilation frame base before oldEnvironment admissions
  compilationFaceAt := fun candidate => by
    cases Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate
    exact { projection := (materialInstallation frame base before oldEnvironment admissions).embed
              ((Q.compilationInstallation (live frame base before oldEnvironment admissions)
                (cfg frame base before oldEnvironment admissions)).embed PUnit.unit)
            active := PUnit.unit
            classifier_eq := rfl
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro candidate _ _ impossible
    cases Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate
    exact nomatch impossible

def sourceFace : SourceNativeRootSemanticFaceAt (root frame base before oldEnvironment admissions)
    (visit frame base before oldEnvironment admissions) where
  projection := (materialInstallation frame base before oldEnvironment admissions).embed
    (Reentry.face frame base before oldEnvironment admissions (live frame base before oldEnvironment admissions)).projection
  active := PUnit.unit
  classifier_eq := rfl

def originFace : SourceNativeRootSemanticFaceAt (root frame base before oldEnvironment admissions)
    (visit frame base before oldEnvironment admissions) where
  projection := (oldInstallation frame base before oldEnvironment admissions).embed
    ((SourceWordNative.originInstallation frame base before oldEnvironment admissions).embed PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

theorem source_material_retained : HEq (sourceFace frame base before oldEnvironment admissions).rootRead
    (Reentry.face frame base before oldEnvironment admissions (live frame base before oldEnvironment admissions)).rootRead := HEq.rfl

theorem origin_retained : (originFace frame base before oldEnvironment admissions).rootRead =
    (Reentry.completedOriginFace frame base before oldEnvironment admissions).rootRead := rfl

abbrev actualMaterial := Reentry.R.actualMaterial (live frame base before oldEnvironment admissions)
  (cfg frame base before oldEnvironment admissions)
abbrev request := Reentry.R.registered (live frame base before oldEnvironment admissions)
  (cfg frame base before oldEnvironment admissions)
abbrev packetAt := Reentry.R.packetAt (live frame base before oldEnvironment admissions)
  (cfg frame base before oldEnvironment admissions)
abbrev firstStep := SourceGeneratedInquiryReceiptAction.firstStep
  (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions)

theorem request_from_installed_material : (actualMaterial frame base before oldEnvironment admissions).raw =
    (sourceFace frame base before oldEnvironment admissions).rootRead.currentMaterial.2.2.2.2.2.1.expression := rfl

theorem first_action : J.sourceAction (answeredState frame base before oldEnvironment admissions)
    (request frame base before oldEnvironment admissions) (packetAt frame base before oldEnvironment admissions) =
    .inr (firstStep frame base before oldEnvironment admissions) :=
  (J.sourceAction_eq _ _ _).trans
    ((J.sourceAction_eq
      (SourceGeneratedInquiryReceiptAction.old (live frame base before oldEnvironment admissions)
        (cfg frame base before oldEnvironment admissions))
      (request frame base before oldEnvironment admissions) (packetAt frame base before oldEnvironment admissions)).symm.trans
      (SourceGeneratedInquiryReceiptAction.first_action (live frame base before oldEnvironment admissions)
        (cfg frame base before oldEnvironment admissions)))

def born : Reentry.A.M.Frame (Value := PairValue (PairValue V)) (Var := X) (sort := s) where
  N := Reentry.C.World (Reentry.betaRequest frame base before oldEnvironment admissions)
  V := Reentry.C.JointV (Reentry.betaRequest frame base before oldEnvironment admissions)
    (Reentry.R.packetAt frame (Reentry.AS.stockCfg base))
  old := answeredState frame base before oldEnvironment admissions
  registered := request frame base before oldEnvironment admissions
  packetAt := packetAt frame base before oldEnvironment admissions
  environment := (CF.lowInitial (live frame base before oldEnvironment admissions)
    (cfg frame base before oldEnvironment admissions)).environment
  depth := 0
  inventory := (CF.lowInitial (live frame base before oldEnvironment admissions)
    (cfg frame base before oldEnvironment admissions)).inventory
  pairInventory := (CF.lowInitial (live frame base before oldEnvironment admissions)
    (cfg frame base before oldEnvironment admissions)).pairInventory
abbrev bornProgramme := CF.lowProgramme (live frame base before oldEnvironment admissions)
  (cfg frame base before oldEnvironment admissions)
abbrev Event := ExactTemporalCausalRootEventAt (root frame base before oldEnvironment admissions).toAuthoritativeRoot.toLedgerRoot
  (visit frame base before oldEnvironment admissions)

def originalTargetAt (event : Event frame base before oldEnvironment admissions) :
    SourceNativeDebtAdmissionActualActionTargetAt
      (root frame base before oldEnvironment admissions) (visit frame base before oldEnvironment admissions) event
      (entry frame base before oldEnvironment admissions) (authority frame base before oldEnvironment admissions) :=
  J.targetAt (answeredState frame base before oldEnvironment admissions)
    (query frame base before oldEnvironment admissions) (request frame base before oldEnvironment admissions)
    (packetAt frame base before oldEnvironment admissions) (authority frame base before oldEnvironment admissions)
    (firstStep frame base before oldEnvironment admissions) (first_action frame base before oldEnvironment admissions) event

def targetAt (event : Event frame base before oldEnvironment admissions) :
    SourceNativeDebtAdmissionActualActionTargetAt
      (root frame base before oldEnvironment admissions) (visit frame base before oldEnvironment admissions) event
      (entry frame base before oldEnvironment admissions) (authority frame base before oldEnvironment admissions) :=
  let original := originalTargetAt frame base before oldEnvironment admissions event
  let sourceFrame := born frame base before oldEnvironment admissions
  let programme := bornProgramme frame base before oldEnvironment admissions
  let material := A.targetCoface original (SourceOperationInquiry.Context.Installation.component (A.epoch sourceFrame))
  let configured := A.optionalTargetCoface material (Q.datum sourceFrame programme).component
  let withQuery := A.targetCoface configured (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.queryLaw (A.epoch sourceFrame) programme)
  let withResult := A.targetCoface withQuery (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.resultLaw (A.epoch sourceFrame) programme)
  let withConsumer := A.targetCoface withResult (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.consumerLaw (A.epoch sourceFrame) programme)
  A.targetCoface withConsumer (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.compilationLaw (A.epoch sourceFrame) programme)

def birthProgram : SourceNativeDebtAdmissionActualActionProgramAt
    (root frame base before oldEnvironment admissions) (visit frame base before oldEnvironment admissions)
    (entry frame base before oldEnvironment admissions) (authority frame base before oldEnvironment admissions) where
  targetAt := targetAt frame base before oldEnvironment admissions

def sourceEvent := (root frame base before oldEnvironment admissions).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt
  (visit frame base before oldEnvironment admissions)
def generatedAction := (birthProgram frame base before oldEnvironment admissions).generate
  (sourceEvent frame base before oldEnvironment admissions)

def compilation (candidate : Query frame base before oldEnvironment admissions) : SourceNativeInquiryCompilationProgramAt
    (root frame base before oldEnvironment admissions) (visit frame base before oldEnvironment admissions)
    (answeredState frame base before oldEnvironment admissions).U7
    (answeredState frame base before oldEnvironment admissions).calculus
    (root frame base before oldEnvironment admissions).source.base.lawSurface candidate
    ((answeredState frame base before oldEnvironment admissions).emitInquiry candidate)
    ((answeredState frame base before oldEnvironment admissions).entryAt candidate)
    ((answeredState frame base before oldEnvironment admissions).authorityAt candidate) where
  compile := fun event => by
    cases Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate
    exact .debtAdmission ((birthProgram frame base before oldEnvironment admissions).generate event)

def state : type_of% (answeredState frame base before oldEnvironment admissions) where
  root := root frame base before oldEnvironment admissions
  visit := visit frame base before oldEnvironment admissions
  U7 := (answeredState frame base before oldEnvironment admissions).U7
  calculus := (answeredState frame base before oldEnvironment admissions).calculus
  Query := Query frame base before oldEnvironment admissions
  entryAt := (answeredState frame base before oldEnvironment admissions).entryAt
  authorityAt := (answeredState frame base before oldEnvironment admissions).authorityAt
  compilationProgramAt := compilation frame base before oldEnvironment admissions
  compilationFaceAt := fun candidate => by
    cases Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate
    exact { projection := ((answeredState frame base before oldEnvironment admissions).compilationFaceAt
              (query frame base before oldEnvironment admissions)).projection
            active := ((answeredState frame base before oldEnvironment admissions).compilationFaceAt
              (query frame base before oldEnvironment admissions)).active
            classifier_eq := ((answeredState frame base before oldEnvironment admissions).compilationFaceAt
              (query frame base before oldEnvironment admissions)).classifier_eq
            project_heq := HEq.rfl }
  u7RootDisposition_commutes := by
    intro candidate _ _ impossible
    cases Q.query_unique (live frame base before oldEnvironment admissions) (cfg frame base before oldEnvironment admissions) candidate
    exact nomatch impossible

def sourcePresentation : RootInquiryStatePresentation where
  N := Reentry.C.World (Reentry.betaRequest frame base before oldEnvironment admissions)
  V := Reentry.C.JointV (Reentry.betaRequest frame base before oldEnvironment admissions)
    (Reentry.R.packetAt frame (Reentry.AS.stockCfg base))
  state := .create (state frame base before oldEnvironment admissions)
def targetPresentation := SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.presentation
  (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions)

theorem compiles : (state frame base before oldEnvironment admissions).compileInquiry
    (query frame base before oldEnvironment admissions) =
    .debtAdmission (generatedAction frame base before oldEnvironment admissions) := rfl

theorem target_root : (generatedAction frame base before oldEnvironment admissions).target.targetRoot =
    Q.root (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions) := rfl

theorem target_next : (generatedAction frame base before oldEnvironment admissions).target.targetAnswerAndNext.nextCurrent =
    ⟨_, (Q.root (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions)).toAuthoritativeRoot,
      Q.visit (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions)⟩ := by
  change (Q.root (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions)).generatedNextCurrentAt
    (.finite (Q.root (born frame base before oldEnvironment admissions) (bornProgramme frame base before oldEnvironment admissions)).toAuthoritativeRoot.toRoot.initialVisit) = _
  apply SourceNativeLivingRootClosure.generatedNextCurrentAt_eq_nativeWriteBranch
  rfl

theorem successor_valid : (targetPresentation frame base before oldEnvironment admissions).erase =
    (RootInquiryProcessNode.answered (sourcePresentation frame base before oldEnvironment admissions)
      (query frame base before oldEnvironment admissions)).erase ∧
    (RootInquiryProcessNode.active (sourcePresentation frame base before oldEnvironment admissions)).PreservesGeneratedLivingLawAt
      (query frame base before oldEnvironment admissions) (.active (targetPresentation frame base before oldEnvironment admissions)) := by
  apply RootInquiryProcessNode.active_debtAdmission_successor_valid
    (sourcePresentation frame base before oldEnvironment admissions) (targetPresentation frame base before oldEnvironment admissions)
    (query frame base before oldEnvironment admissions) (generatedAction frame base before oldEnvironment admissions)
    (compiles frame base before oldEnvironment admissions)
  · exact (congrArg (fun current =>
      (⟨_, current⟩ : AnyAuthoritativeRootCurrent.{u})) (target_next frame base before oldEnvironment admissions)).symm
  · exact HEq.rfl

def nextSourceFace : SourceNativeRootSemanticFaceAt
    (generatedAction frame base before oldEnvironment admissions).target.targetRoot
    (generatedAction frame base before oldEnvironment admissions).target.targetVisit where
  projection := (generatedAction frame base before oldEnvironment admissions).target.oldProjection
    (sourceFace frame base before oldEnvironment admissions).projection
  active := PUnit.unit
  classifier_eq := rfl

def nextOriginFace : SourceNativeRootSemanticFaceAt
    (generatedAction frame base before oldEnvironment admissions).target.targetRoot
    (generatedAction frame base before oldEnvironment admissions).target.targetVisit where
  projection := (generatedAction frame base before oldEnvironment admissions).target.oldProjection
    (originFace frame base before oldEnvironment admissions).projection
  active := PUnit.unit
  classifier_eq := rfl

theorem next_old_constants : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.oldConstants =
    valueMap (R := ℤ) oldEnvironment (SourceWordNative.words frame base before admissions).sum := rfl

theorem next_new_constants : (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.newConstants =
    valueMap (R := ℤ) (SourceWordNative.afterEnvironment frame base)
      (SourceWordNative.sourceWord frame base before admissions) := rfl

def nextDifferential : PairValue V s :=
  (nextOriginFace frame base before oldEnvironment admissions).rootRead.state.1.eval
    (Reentry.betaRequest frame base before oldEnvironment admissions).input.environment

def nextFullValue : PairValue V s :=
  (ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s)
    (nextOriginFace frame base before oldEnvironment admissions).rootRead.source.oldConstants, 0) +
  nextDifferential frame base before oldEnvironment admissions

theorem next_full_value : nextFullValue frame base before oldEnvironment admissions =
    SourceWordNative.nextFullValue frame base before oldEnvironment admissions := by
  unfold nextFullValue nextDifferential
  rw [(nextOriginFace frame base before oldEnvironment admissions).rootRead.state.2.sound.symm,
    next_old_constants, SourceWordNative.actual_updated_value]
  have old := LinearMap.congr_fun (valueMap_evaluation (R := ℤ) oldEnvironment)
    (SourceWordNative.words frame base before admissions).sum
  change ScalarRelationPresentation.freeEvaluation (R := ℤ) (V s)
    (valueMap (R := ℤ) oldEnvironment (SourceWordNative.words frame base before admissions).sum) = _ at old
  rw [old, SourceWordNative.next_full_value]
  abel

theorem whole_first : type_of% (generatedAction frame base before oldEnvironment admissions).target.firstDestination_heq :=
  (generatedAction frame base before oldEnvironment admissions).target.firstDestination_heq

end SourceInventoryExecutionFeed.SourceWordNative.Reentry.Splice
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
