import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierNativeAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open private retainedFace retained_payload targetSourceFace target_payload from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction
namespace Source
export OriginalConstantFourierNativeSource
  (sourceRoot sourceVisit reader result trace equation paid)
end Source
namespace Prior
export OriginalWholeDebtRPairedWaveNativeStockConsumer (actualBirthTarget)
end Prior
namespace N
export OriginalKPairedWaveNativeStockSource (bornFrame stockProgramme)
end N
namespace Origin
export OriginalConstantFourierNativeOrigin (originFace)
end Origin
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

namespace SameSource
variable {N : WorldRelationNetwork} {V : Vocabulary}
variable (old : SourceNativeAuthoritativeRootClosure N V) (stage : V.Current)
variable (read : {now : V.Current} →
  old.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now →
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()))

private noncomputable def state := OC.targetState old stage (fun _ => read (old.emitted stage))
private noncomputable def trace := OC.trace old stage (fun _ => read (old.emitted stage))
private noncomputable def value := OC.value old stage (fun _ => read (old.emitted stage))

private theorem state_source : HEq (state old stage read)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
      old read (old.emitted stage)).2.1 := HEq.rfl

private theorem trace_source : HEq (trace old stage read)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
      old read (old.emitted stage)).2.1.2 := HEq.rfl

private theorem value_source : value old stage read =
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt
      old read (old.emitted stage)).2.2.1 := rfl
end SameSource

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
variable (t : ℝ)

noncomputable def sourceRoot := Source.sourceRoot observation nontrivial half depth ordinal
noncomputable def sourceVisit := Source.sourceVisit observation nontrivial half depth ordinal
local notation "src" => sourceRoot observation nontrivial half depth ordinal
local notation "here" => sourceVisit observation nontrivial half depth ordinal
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
local notation "auth" => sourceAuthority observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal

/-- The source action starts at the exact CP412 born root and visit. -/
theorem source_ledger : (src).toAuthoritativeRoot.toLedgerRoot =
    (Prior.actualBirthTarget observation nontrivial half depth ordinal).targetRoot.toAuthoritativeRoot.toLedgerRoot := rfl

theorem source_visit : here = (Prior.actualBirthTarget observation nontrivial half depth ordinal).targetVisit := rfl

theorem source_occurrence : (src).emitted (here).current =
    (Prior.actualBirthTarget observation nontrivial half depth ordinal).targetRoot.emitted
      (Prior.actualBirthTarget observation nontrivial half depth ordinal).targetVisit.current := rfl

noncomputable def sourceU7 := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.answeredState
  (N.bornFrame observation nontrivial half depth ordinal) (N.stockProgramme observation nontrivial half depth ordinal)).U7
noncomputable def sourceCalculus := (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.answeredState
  (N.bornFrame observation nontrivial half depth ordinal) (N.stockProgramme observation nontrivial half depth ordinal)).calculus
local notation "u7" => sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => sourceCalculus observation nontrivial half depth ordinal

noncomputable def sourceReader (_supplied : (auth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  Source.reader observation nontrivial half depth ordinal t ((auth).emitted origin)
local notation "reader" => sourceReader observation nontrivial half depth ordinal t

noncomputable def actionResult := Source.result observation nontrivial half depth ordinal t

noncomputable def actionCalculation := Calc.normal auth origin reader

noncomputable def actionState := SameSource.state auth origin (Source.reader observation nontrivial half depth ordinal t)

noncomputable def actionTrace := SameSource.trace auth origin (Source.reader observation nontrivial half depth ordinal t)

noncomputable def actionValue := SameSource.value auth origin (Source.reader observation nontrivial half depth ordinal t)

theorem action_result_source : HEq (actionResult observation nontrivial half depth ordinal t)
    (Source.result observation nontrivial half depth ordinal t) := HEq.rfl

theorem action_state_source : type_of% (SameSource.state_source auth origin
    (Source.reader observation nontrivial half depth ordinal t)) :=
  SameSource.state_source auth origin (Source.reader observation nontrivial half depth ordinal t)

theorem action_trace_source : type_of% (SameSource.trace_source auth origin
    (Source.reader observation nontrivial half depth ordinal t)) :=
  SameSource.trace_source auth origin (Source.reader observation nontrivial half depth ordinal t)

theorem action_value_source : type_of% (SameSource.value_source auth origin
    (Source.reader observation nontrivial half depth ordinal t)) :=
  SameSource.value_source auth origin (Source.reader observation nontrivial half depth ordinal t)

theorem action_equation : type_of% (Source.equation observation nontrivial half depth ordinal t) :=
  Source.equation observation nontrivial half depth ordinal t

theorem action_relation : type_of% (OC.relation_boundary (R := ℤ) auth origin reader) :=
  OC.relation_boundary (R := ℤ) auth origin reader

theorem action_inverse : type_of% (OC.updated_inverse_fibre (R := ℤ) auth origin reader 0) :=
  OC.updated_inverse_fibre (R := ℤ) auth origin reader 0

theorem action_whole_next (count : Nat) : type_of% (Math.whole_next auth origin reader count) :=
  Math.whole_next auth origin reader count

noncomputable def actionPayments (index : Fin 5) := Pay.activePayment auth origin reader
  ⟨index.val, by change index.val < 5; exact index.isLt⟩

noncomputable def originFace := Origin.originFace observation nontrivial half depth ordinal

noncomputable def inquiryState := MS.endpointState src here u7 calculus reader

noncomputable def retainedNextFace := retainedFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)

theorem retained_source_payload : type_of% (retained_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)) :=
  retained_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal) (MS.endpointCount src here reader)

noncomputable def request := MS.residualRegistered src here u7 calculus reader

noncomputable def firstStep := MS.residualFirstStep src here u7 calculus reader

theorem first_action : type_of% (MS.residual_first_action src here u7 calculus reader) :=
  MS.residual_first_action src here u7 calculus reader

noncomputable def actualTarget := MS.residualTarget src here u7 calculus reader

noncomputable def actualFrame := MS.frame src here u7 calculus reader

theorem whole_first : type_of% (MS.residual_first_receipt src here u7 calculus reader) :=
  MS.residual_first_receipt src here u7 calculus reader

theorem canonical_next : type_of% (MS.residual_frame_next src here u7 calculus reader) :=
  MS.residual_frame_next src here u7 calculus reader

noncomputable def actualOriginFace := targetSourceFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal)

theorem target_source_payload : type_of% (target_payload src here u7 calculus reader
    (originFace observation nontrivial half depth ordinal)) :=
  target_payload src here u7 calculus reader (originFace observation nontrivial half depth ordinal)

end OriginalConstantFourierNativeAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierNativeAction"
