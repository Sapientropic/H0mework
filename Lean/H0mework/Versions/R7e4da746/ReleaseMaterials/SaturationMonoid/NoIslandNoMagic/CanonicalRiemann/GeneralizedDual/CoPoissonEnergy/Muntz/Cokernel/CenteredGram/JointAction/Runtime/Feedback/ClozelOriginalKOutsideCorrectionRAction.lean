import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKOutsideCorrectionRAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open private retainedFace retained_payload targetSourceFace target_payload from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction
namespace Source
export OriginalKOutsideCorrectionRSource
  (sourceRoot sourceVisit rReader rResult rTrace rInput finalCorrectionValue r_equation r_paid)
end Source
namespace Prior
export OriginalKPaNativeCayleyNextPrefixAction (finalTarget finalFrame finalOriginFace)
end Prior
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw raw)
end O
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (targetState trace value relation_boundary updated_inverse_fibre)
end OC
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (normal)
end Calc
namespace Pay
export RootGeneratedDebtActivationJointSource.OwnerFree.Payment (activePayment)
end Pay
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (endpointCount endpointState residualRegistered residualFirstStep residual_first_action
   residualTarget frame residual_first_receipt residual_frame_next)
end MS
namespace Math
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math (whole_next)
end Math

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half

def sourceRoot := Source.sourceRoot observation nontrivial half depth ordinal
def sourceVisit := Source.sourceVisit observation nontrivial half depth ordinal
local notation "src" => sourceRoot observation nontrivial half depth ordinal
local notation "here" => sourceVisit observation nontrivial half depth ordinal
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
local notation "auth" => sourceAuthority observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal

/-- The next R uses exactly the root and visit emitted by the preceding action. -/
theorem source_ledger : (src).toAuthoritativeRoot.toLedgerRoot =
    (Prior.finalTarget observation nontrivial half depth ordinal).targetRoot.toAuthoritativeRoot.toLedgerRoot := rfl

theorem source_visit : here = (Prior.finalTarget observation nontrivial half depth ordinal).targetVisit := rfl

theorem source_occurrence : (src).emitted (here).current =
    (Prior.finalTarget observation nontrivial half depth ordinal).targetRoot.emitted
      (Prior.finalTarget observation nontrivial half depth ordinal).targetVisit.current := rfl

def sourceU7 := (Prior.finalFrame observation nontrivial half depth ordinal).currentState.U7
def sourceCalculus := (Prior.finalFrame observation nontrivial half depth ordinal).currentState.calculus
local notation "u7" => sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => sourceCalculus observation nontrivial half depth ordinal

def sourceReader (supplied : (auth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  Source.rReader observation nontrivial half depth ordinal supplied
local notation "reader" => sourceReader observation nontrivial half depth ordinal

def rResult := Source.rResult observation nontrivial half depth ordinal

def rCalculation := Calc.normal auth origin reader

def rState := OC.targetState auth origin reader

def rTrace := OC.trace auth origin reader

def rValue := OC.value auth origin reader

theorem r_result_source : HEq (rResult observation nontrivial half depth ordinal)
    (Source.rResult observation nontrivial half depth ordinal) := HEq.rfl

theorem r_state_source : HEq (rState observation nontrivial half depth ordinal)
    (Source.rResult observation nontrivial half depth ordinal).2.1 := HEq.rfl

theorem r_trace_source : HEq (rTrace observation nontrivial half depth ordinal)
    (Source.rResult observation nontrivial half depth ordinal).2.1.2 := HEq.rfl

theorem r_value_source : rValue observation nontrivial half depth ordinal =
    (Source.rResult observation nontrivial half depth ordinal).2.2.1 := rfl

theorem r_equation : rValue observation nontrivial half depth ordinal =
    burnolDirectRightResolventCLM c (Source.finalCorrectionValue observation nontrivial half depth ordinal) :=
  (r_value_source observation nontrivial half depth ordinal).trans
    (Source.r_equation observation nontrivial half depth ordinal)

theorem r_relation : type_of% (OC.relation_boundary (R := ℤ) auth origin reader) :=
  OC.relation_boundary (R := ℤ) auth origin reader

theorem r_inverse : type_of% (OC.updated_inverse_fibre (R := ℤ) auth origin reader 0) :=
  OC.updated_inverse_fibre (R := ℤ) auth origin reader 0

theorem r_whole_next (count : Nat) : type_of% (Math.whole_next auth origin reader count) :=
  Math.whole_next auth origin reader count

def rPayments (index : Fin 2) := Pay.activePayment auth origin reader
  ⟨index.val, by change index.val < 2; exact index.isLt⟩

def originFace := Prior.finalOriginFace observation nontrivial half depth ordinal

def inquiryState := MS.endpointState src here u7 calculus reader

def retainedNextFace := retainedFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)

theorem retained_source_payload : type_of% (retained_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)) :=
  retained_payload src here u7 calculus reader
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

def actualOriginFace := targetSourceFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal)

theorem target_source_payload : type_of% (target_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal)) :=
  target_payload src here u7 calculus reader (originFace observation nontrivial half depth ordinal)

end OriginalKOutsideCorrectionRAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKOutsideCorrectionRAction"
