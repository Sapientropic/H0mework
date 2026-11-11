import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextRSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativePortNoetherConsumer
import H0mework.Versions.Rdf421ff6.Foundation.Responsibility.JointSource.OwnerFree.Installation.Math.Frame.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleyNextAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
namespace NS
export OriginalKPaNativeCayleyNextSource
  (sourceRoot sourceVisit nextAdmissions nextPaValue nextPaTrace nextPaTrace_heq nextRReader nextRResult nextRTrace
   nextRInput nextR_input_binding nextR_equation nextR_paid)
end NS
namespace Paid
export OriginalKPaNativePortNoetherConsumer (debtFrame first_ledger first_visit first_occurrence)
end Paid
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var rCode)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw raw)
end O
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (trace value relation_boundary updated_inverse_fibre)
end OC
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation
  (normal targetRuntime target_factorizes realization)
end Calc
namespace Pay
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment)
end Pay
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (root visit endpointCount endpointState residualRegistered residualFirstStep residual_first_action
   residualTarget frame residual_first_receipt residual_frame_next original_material)
end MS
namespace Math
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math (whole_next)
end Math

namespace Adapter
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (sourceRoot : SourceNativeLivingRootClosure N V)
variable (sourceVisit : SourceNativeTemporalVisitAt sourceRoot.toAuthoritativeRoot.toLedgerRoot)
variable (sourceU7 : U7ProducerCalculus N) (sourceCalculus : U7ObstructionEvolutionCalculus N sourceU7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : sourceRoot.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt sourceVisit.current →
  O.Raw (Value := Value) (Var := Var) (sort := sort))
variable (face : SourceNativeRootSemanticFaceAt sourceRoot sourceVisit) (count : Nat)

/-- This is the existing old-projection injection, through the existing math inquiry cofaces. -/
private def retainedFace : SourceNativeRootSemanticFaceAt
    (MS.root sourceRoot sourceVisit sourceU7 sourceCalculus reader count)
    (MS.visit sourceRoot sourceVisit reader count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      sourceRoot.toAuthoritativeRoot sourceVisit.current reader).embed (.inl face.projection))))
  active := face.active
  classifier_eq := face.classifier_eq

private theorem retained_payload : HEq
    (retainedFace sourceRoot sourceVisit sourceU7 sourceCalculus reader face count).rootRead face.rootRead :=
  HEq.rfl

private def targetSourceFace : SourceNativeRootSemanticFaceAt
    (MS.residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).targetRoot
    (MS.residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).targetVisit where
  projection := (MS.residualTarget sourceRoot sourceVisit sourceU7 sourceCalculus reader).oldProjection
    (retainedFace sourceRoot sourceVisit sourceU7 sourceCalculus reader face
      (MS.endpointCount sourceRoot sourceVisit reader)).projection
  active := face.active
  classifier_eq := face.classifier_eq

private theorem target_payload : HEq
    (targetSourceFace sourceRoot sourceVisit sourceU7 sourceCalculus reader face).rootRead face.rootRead :=
  HEq.rfl
end Adapter

namespace L
export OriginalKCofinalFullBranchFibre.KernelWrite.L (Value groups)
end L
local instance receiptGroups (grade : Nat) : ∀ target, AddCommGroup
    (SourceOperationScalarInventoryLift.PairValue
      (L.Value (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade) target) :=
  L.groups (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) (grade + 1)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
def sourceRoot := NS.sourceRoot observation nontrivial half depth ordinal
def sourceVisit := NS.sourceVisit observation nontrivial half depth ordinal
local notation "src" => sourceRoot observation nontrivial half depth ordinal
local notation "here" => sourceVisit observation nontrivial half depth ordinal
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
local notation "auth" => sourceAuthority observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal

section SourceOrigin
local instance levelGroups (grade : Nat) : ∀ target, AddCommGroup
    (L.Value (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade target) :=
  L.groups (SourceOperationScalarInventoryLift.PairValue OriginalKCombReceiptFeedback.Value) grade

def originFace : SourceNativeRootSemanticFaceAt
    (NS.sourceRoot observation nontrivial half depth ordinal)
    (NS.sourceVisit observation nontrivial half depth ordinal) where
  projection := .component PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

theorem origin_occurrences : (originFace observation nontrivial half depth ordinal).rootRead.source.occurrences =
    NS.nextAdmissions observation nontrivial half depth ordinal := rfl

end SourceOrigin

/-- Only the already installed network calculus is borrowed from the proved same first visit. -/
def sourceU7 := (Paid.debtFrame observation nontrivial half depth ordinal).currentState.U7
def sourceCalculus := (Paid.debtFrame observation nontrivial half depth ordinal).currentState.calculus
local notation "u7" => sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => sourceCalculus observation nontrivial half depth ordinal

def sourceReader (supplied : (auth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  NS.nextRReader observation nontrivial half depth ordinal supplied
local notation "reader" => sourceReader observation nontrivial half depth ordinal

theorem source_ledger : type_of% (Paid.first_ledger observation nontrivial half depth ordinal) :=
  Paid.first_ledger observation nontrivial half depth ordinal

theorem source_visit : type_of% (Paid.first_visit observation nontrivial half depth ordinal) :=
  Paid.first_visit observation nontrivial half depth ordinal

theorem source_occurrence : type_of% (Paid.first_occurrence observation nontrivial half depth ordinal) :=
  Paid.first_occurrence observation nontrivial half depth ordinal

def rCalculation := Calc.normal auth origin reader

def rTrace := OC.trace auth origin reader

def rValue := OC.value auth origin reader

theorem r_trace_source : HEq (rTrace observation nontrivial half depth ordinal)
    (NS.nextRResult observation nontrivial half depth ordinal).2.1.2 := HEq.rfl

theorem r_value_source : rValue observation nontrivial half depth ordinal =
    (NS.nextRResult observation nontrivial half depth ordinal).2.2.1 := rfl

theorem r_equation : rValue observation nontrivial half depth ordinal =
    burnolDirectRightResolventCLM c (NS.nextPaValue observation nontrivial half depth ordinal) :=
  (r_value_source observation nontrivial half depth ordinal).trans
    (NS.nextR_equation observation nontrivial half depth ordinal)

theorem r_relation : type_of% (OC.relation_boundary (R := ℤ) auth origin reader) :=
  OC.relation_boundary (R := ℤ) auth origin reader

theorem r_inverse : type_of% (OC.updated_inverse_fibre (R := ℤ) auth origin reader 0) :=
  OC.updated_inverse_fibre (R := ℤ) auth origin reader 0

theorem r_whole_next (count : Nat) : type_of% (Math.whole_next auth origin reader count) :=
  Math.whole_next auth origin reader count

/-- Both paid steps are generated by the literal original R programme at this next occurrence. -/
def rPayments (index : Fin 2) := Pay.activePayment auth origin reader
  ⟨index.val, by change index.val < 2; exact index.isLt⟩

def inquiryState := MS.endpointState src here u7 calculus reader

def retainedNextFace := Adapter.retainedFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)

theorem retained_payload : type_of% (Adapter.retained_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)) :=
  Adapter.retained_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)

def request := MS.residualRegistered src here u7 calculus reader

def firstStep := MS.residualFirstStep src here u7 calculus reader

theorem first_action : type_of% (MS.residual_first_action src here u7 calculus reader) :=
  MS.residual_first_action src here u7 calculus reader

def actualTarget := MS.residualTarget src here u7 calculus reader

def actualFrame := MS.frame src here u7 calculus reader

theorem whole_first : type_of% (MS.residual_first_receipt src here u7 calculus reader) :=
  MS.residual_first_receipt src here u7 calculus reader

theorem canonical_next : type_of% (MS.residual_frame_next src here u7 calculus reader) :=
  MS.residual_frame_next src here u7 calculus reader


/-- The same original source payload is also read at the actual first-write next visit. -/
def targetSourceFace := Adapter.targetSourceFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal)

theorem target_source_payload : type_of% (Adapter.target_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal)) :=
  Adapter.target_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal)

end OriginalKPaNativeCayleyNextAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPaNativeCayleyNextAction"
