import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextPrefixSource

import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.RawState

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleyNextPrefixAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open RootGeneratedDebtActivationJointSource
open private targetSourceFace target_payload from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction
namespace A
export OriginalKPaNativeCayleyNextAction (actualFrame targetSourceFace)
end A
namespace PX
export OriginalKPaNativeCayleyNextPrefixSource
  (sourceRoot sourceVisit prefixReader prefixResult lastRReader lastRResult targetRFace)
end PX
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw raw nextState common_raw_state)
end O
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (targetState trace value value_source relation_boundary updated_inverse_fibre)
end OC
namespace Calc
export RootGeneratedDebtActivationJointSource.OwnerFree.Calculation (normal target_state target_factorizes)
end Calc
namespace Complete
export RootGeneratedDebtActivationJointSource.OwnerFree.Completion
  (state initial_state next_state)
end Complete
namespace I
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt resultLaw)
end I
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (endpointState residualRegistered residualFirstStep residual_first_action residualTarget frame
   residual_first_receipt residual_frame_next)
end MS
namespace Math
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math (whole_next)
end Math
namespace NR
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest
  (MaterialAt input budget relation_boundary residual_value updated_value)
end NR
namespace SI
export RootGeneratedDebtActivationJointSource.Successor.Inquiry (targetAt)
end SI
namespace SS
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Source (programme)
end SS
namespace Cont
export RootGeneratedDebtActivationJointSource.Successor.Inquiry.Continuation (Frame)
end Cont
namespace Prog
export OriginalKReturnJordanSourceCalculation (Value Var)
end Prog

namespace SameOccurrence
universe u
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (first second : O.Raw (Value := Value) (Var := Var) (sort := sort))

abbrev extended := (root.withProjectionCoface (I.resultLaw root.toAuthoritativeRoot (fun {_} _ => first))).withProjectionCoface
  (I.resultLaw root.toAuthoritativeRoot (fun {_} _ => second))

def firstFace : SourceNativeRootSemanticFaceAt (extended root first second) visit where
  projection := .inherited (.component PUnit.unit)
  active := PUnit.unit
  classifier_eq := rfl

def secondFace : SourceNativeRootSemanticFaceAt (extended root first second) visit where
  projection := .component PUnit.unit
  active := PUnit.unit
  classifier_eq := rfl

def firstResult : I.ResultAt root.toAuthoritativeRoot (fun {_} _ => first) (root.emitted visit.current) :=
  (firstFace root visit first second).rootRead

def secondResult : I.ResultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current) :=
  (secondFace root visit first second).rootRead

theorem first_source : firstResult root visit first second =
    I.resultAt root.toAuthoritativeRoot (fun {_} _ => first) (root.emitted visit.current) := rfl

theorem second_source : secondResult root visit first second =
    I.resultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current) := rfl

theorem first_trace_source : HEq (firstResult root visit first second).2.1.2
    (I.resultAt root.toAuthoritativeRoot (fun {_} _ => first) (root.emitted visit.current)).2.1.2 := HEq.rfl

/-- Coface installation retains the ledger occurrence; the existing raw-state theorem retains the whole calculation state. -/
theorem target_state : OC.targetState (extended root first second).toAuthoritativeRoot visit.current
    (fun _ => first) = OC.targetState root.toAuthoritativeRoot visit.current (fun _ => first) :=
  (Calc.target_state _ _ _).trans
    ((O.common_raw_state (extended root first second).toAuthoritativeRoot visit.current
      root.toAuthoritativeRoot visit.current first (remaining first.expression)).trans
        (Calc.target_state _ _ _).symm)

theorem target_result_state : HEq
    (OC.targetState (extended root first second).toAuthoritativeRoot visit.current (fun _ => first))
    (I.resultAt root.toAuthoritativeRoot (fun {_} _ => first) (root.emitted visit.current)).2.1 :=
  heq_of_eq (target_state root visit first second)

theorem target_result_value : OC.value (extended root first second).toAuthoritativeRoot visit.current
    (fun _ => first) =
      (I.resultAt root.toAuthoritativeRoot (fun {_} _ => first) (root.emitted visit.current)).2.2.1 :=
  (OC.value_source (extended root first second).toAuthoritativeRoot visit.current (fun _ => first)).trans
    (OC.value_source root.toAuthoritativeRoot visit.current (fun _ => first)).symm

variable (u7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N u7)

def nextSecondFace := targetSourceFace (extended root first second) visit u7 calculus (fun _ => first)
  (secondFace root visit first second)

def nextSecondResult : I.ResultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current) :=
  (nextSecondFace root visit first second u7 calculus).rootRead

theorem next_second_source : nextSecondResult root visit first second u7 calculus =
    I.resultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current) := rfl

theorem next_second_state : HEq (nextSecondResult root visit first second u7 calculus).2.1
    (I.resultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current)).2.1 :=
  heq_of_eq (congrArg (fun result => result.2.1) (next_second_source root visit first second u7 calculus))

theorem next_second_trace : HEq (nextSecondResult root visit first second u7 calculus).2.1.2
    (I.resultAt root.toAuthoritativeRoot (fun {_} _ => second) (root.emitted visit.current)).2.1.2 := HEq.rfl
end SameOccurrence

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

private abbrev originalAuthority := (PX.sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
local notation "baseAuthority" => originalAuthority observation nontrivial half depth ordinal

private def prefixRaw := PX.prefixReader observation nontrivial half depth ordinal
  ((PX.sourceRoot observation nontrivial half depth ordinal).emitted
    (PX.sourceVisit observation nontrivial half depth ordinal).current)
private def lastRaw := PX.lastRReader observation nontrivial half depth ordinal
  ((PX.sourceRoot observation nontrivial half depth ordinal).emitted
    (PX.sourceVisit observation nontrivial half depth ordinal).current)

/-- Both existing source laws retain their original occurrence-indexed ResultAt packages. -/
def sourceRoot := SameOccurrence.extended (PX.sourceRoot observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

def sourceVisit : SourceNativeTemporalVisitAt
    (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot :=
  PX.sourceVisit observation nontrivial half depth ordinal

theorem source_ledger : (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot =
    (PX.sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot.toLedgerRoot := rfl

theorem source_visit : sourceVisit observation nontrivial half depth ordinal =
    PX.sourceVisit observation nontrivial half depth ordinal := rfl

local notation "src" => sourceRoot observation nontrivial half depth ordinal
local notation "here" => sourceVisit observation nontrivial half depth ordinal
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
local notation "auth" => sourceAuthority observation nontrivial half depth ordinal
local notation "origin" => sourceCurrent observation nontrivial half depth ordinal

def prefixResultFace := SameOccurrence.firstFace
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

def lastResultFace := SameOccurrence.secondFace
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

def prefixResult := SameOccurrence.firstResult
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

def lastOriginalResult := SameOccurrence.secondResult
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

def prefixTrace := (prefixResult observation nontrivial half depth ordinal).2.1.2

theorem prefix_result_source : type_of% (
  heq_of_eq (SameOccurrence.first_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal))) :=
  heq_of_eq (SameOccurrence.first_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal))

theorem last_original_source : type_of% (
  heq_of_eq (SameOccurrence.second_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal))) :=
  heq_of_eq (SameOccurrence.second_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal))

theorem prefix_trace_source : type_of% (
  SameOccurrence.first_trace_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)) :=
  SameOccurrence.first_trace_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

private def originFace : SourceNativeRootSemanticFaceAt src here where
  projection := .inherited (.inherited (A.targetSourceFace observation nontrivial half depth ordinal).projection)
  active := (A.targetSourceFace observation nontrivial half depth ordinal).active
  classifier_eq := (A.targetSourceFace observation nontrivial half depth ordinal).classifier_eq

private def r1Face : SourceNativeRootSemanticFaceAt src here where
  projection := .inherited (.inherited (PX.targetRFace observation nontrivial half depth ordinal).projection)
  active := (PX.targetRFace observation nontrivial half depth ordinal).active
  classifier_eq := (PX.targetRFace observation nontrivial half depth ordinal).classifier_eq

def sourceU7 := (A.actualFrame observation nontrivial half depth ordinal).currentState.U7
def sourceCalculus := (A.actualFrame observation nontrivial half depth ordinal).currentState.calculus
local notation "u7" => sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => sourceCalculus observation nontrivial half depth ordinal

def prefixReader (supplied : (auth).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  PX.prefixReader observation nontrivial half depth ordinal supplied
local notation "reader" => prefixReader observation nontrivial half depth ordinal

def prefixCalculation := Calc.normal auth origin reader

theorem prefix_state_source : type_of% (
  SameOccurrence.target_result_state
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)) :=
  SameOccurrence.target_result_state
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

theorem prefix_value_source : type_of% (
  SameOccurrence.target_result_value
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)) :=
  SameOccurrence.target_result_value
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal)

theorem prefix_whole_steps (count : Nat) : type_of% (Math.whole_next auth origin reader count) :=
  Math.whole_next auth origin reader count

def prefixRequest := MS.residualRegistered src here u7 calculus reader
def prefixFirstStep := MS.residualFirstStep src here u7 calculus reader
def prefixTarget := MS.residualTarget src here u7 calculus reader
def prefixFrame := MS.frame src here u7 calculus reader

theorem prefix_first_action : type_of% (MS.residual_first_action src here u7 calculus reader) :=
  MS.residual_first_action src here u7 calculus reader
theorem prefix_whole_first : type_of% (MS.residual_first_receipt src here u7 calculus reader) :=
  MS.residual_first_receipt src here u7 calculus reader
theorem prefix_canonical_next : type_of% (MS.residual_frame_next src here u7 calculus reader) :=
  MS.residual_frame_next src here u7 calculus reader

def nextLastResultFace := SameOccurrence.nextSecondFace
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus

def lastResult := SameOccurrence.nextSecondResult
  (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
  (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus

def lastTrace := (lastResult observation nontrivial half depth ordinal).2.1.2

theorem last_result_source : type_of% (
  heq_of_eq (SameOccurrence.next_second_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus)) :=
  heq_of_eq (SameOccurrence.next_second_source
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus)

theorem last_trace_source : type_of% (
  SameOccurrence.next_second_trace
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus) :=
  SameOccurrence.next_second_trace
    (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
    (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus

def prefixOriginFace := targetSourceFace src here u7 calculus reader
  (originFace observation nontrivial half depth ordinal)
def prefixR1Face := targetSourceFace src here u7 calculus reader
  (r1Face observation nontrivial half depth ordinal)

theorem prefix_origin_source : HEq (prefixOriginFace observation nontrivial half depth ordinal).rootRead
    (A.targetSourceFace observation nontrivial half depth ordinal).rootRead := HEq.rfl
theorem prefix_r1_source : HEq (prefixR1Face observation nontrivial half depth ordinal).rootRead
    (PX.targetRFace observation nontrivial half depth ordinal).rootRead := HEq.rfl

private abbrev afterPrefix := (prefixFrame observation nontrivial half depth ordinal).currentState
local notation "post" => afterPrefix observation nontrivial half depth ordinal

/-- The next request consumes the retained original last-R history, rather than running a new R. -/
def lastMaterial (source : (post).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (post).visit.current) : NR.MaterialAt (Value := Prog.Value) (Var := Prog.Var) (sort := ()) source := by
  rcases source with ⟨support, event⟩
  cases event
  exact { environment := (lastRaw observation nontrivial half depth ordinal).environment
          increment := 0
          raw := (lastRaw observation nontrivial half depth ordinal).expression
          state := (lastResult observation nontrivial half depth ordinal).2.1
          owner := (post).entryAt PUnit.unit }

private theorem lastMaterial_state (source : (post).root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
    (post).visit.current) :
    HEq (lastMaterial observation nontrivial half depth ordinal source).state
      (lastResult observation nontrivial half depth ordinal).2.1 := by
  rcases source with ⟨support, event⟩
  cases event
  rfl

def lastActualMaterial := lastMaterial observation nontrivial half depth ordinal
  ((post).root.emitted (post).visit.current)

def lastRequest := register (fun source => NR.input (lastMaterial observation nontrivial half depth ordinal source))

def lastProgramme := SS.programme (prefixFrame observation nontrivial half depth ordinal).old
  (prefixFrame observation nontrivial half depth ordinal).registered
  (prefixFrame observation nontrivial half depth ordinal).packetAt
  (prefixFrame observation nontrivial half depth ordinal).depth

theorem last_material_state_source : type_of% (
  (lastMaterial_state observation nontrivial half depth ordinal
    ((post).root.emitted (post).visit.current)).trans
      (SameOccurrence.next_second_state
        (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
        (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus)) :=
  (lastMaterial_state observation nontrivial half depth ordinal
    ((post).root.emitted (post).visit.current)).trans
      (SameOccurrence.next_second_state
        (PX.sourceRoot observation nontrivial half depth ordinal) (PX.sourceVisit observation nontrivial half depth ordinal)
        (prefixRaw observation nontrivial half depth ordinal) (lastRaw observation nontrivial half depth ordinal) u7 calculus)

theorem last_relation : type_of% (NR.relation_boundary (R := ℤ)
    (lastActualMaterial observation nontrivial half depth ordinal)) :=
  NR.relation_boundary (R := ℤ) (lastActualMaterial observation nontrivial half depth ordinal)
theorem last_inverse : type_of% (NR.residual_value (R := ℤ)
    (lastActualMaterial observation nontrivial half depth ordinal)) :=
  NR.residual_value (R := ℤ) (lastActualMaterial observation nontrivial half depth ordinal)

private theorem last_not_settled (settled : SourceOperationExecutionDebt.Settlement
    (initialEvent (lastRequest observation nontrivial half depth ordinal)).state) : False := by
  have zero := (Idle.law (lastRequest observation nontrivial half depth ordinal).input.environment
    (lastRequest observation nontrivial half depth ordinal).input.expression).settlement_budget_zero settled
  have positive := NR.budget (lastActualMaterial observation nontrivial half depth ordinal)
  change remaining (lastRequest observation nontrivial half depth ordinal).input.expression = 0 at zero
  change remaining (lastRequest observation nontrivial half depth ordinal).input.expression = _ at positive
  omega

def lastFirstStep := match mathAction (initialEvent (lastRequest observation nontrivial half depth ordinal)) with
  | .inl settled => False.elim (last_not_settled observation nontrivial half depth ordinal settled)
  | .inr paid => paid

theorem last_first_action : mathAction (initialEvent (lastRequest observation nontrivial half depth ordinal)) =
    .inr (lastFirstStep observation nontrivial half depth ordinal) := by
  cases selected : mathAction (initialEvent (lastRequest observation nontrivial half depth ordinal)) with
  | inl settled => exact False.elim (last_not_settled observation nontrivial half depth ordinal settled)
  | inr paid => simp only [lastFirstStep, selected]

def finalTarget := SI.targetAt post PUnit.unit (lastRequest observation nontrivial half depth ordinal)
  (lastProgramme observation nontrivial half depth ordinal) ((post).authorityAt PUnit.unit)
  (lastFirstStep observation nontrivial half depth ordinal) (last_first_action observation nontrivial half depth ordinal)
  ((post).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (post).visit)

def finalFrame : Cont.Frame (Value := Prog.Value) (Var := Prog.Var) (sort := ()) where
  N := (prefixFrame observation nontrivial half depth ordinal).currentPresentation.N
  V := (prefixFrame observation nontrivial half depth ordinal).currentPresentation.V
  old := post
  registered := lastRequest observation nontrivial half depth ordinal
  packetAt := lastProgramme observation nontrivial half depth ordinal
  environment := fun {_current} _source => (lastResult observation nontrivial half depth ordinal).1.environment
  depth := 0

theorem last_whole_first : type_of% (finalTarget observation nontrivial half depth ordinal).firstDestination_heq :=
  (finalTarget observation nontrivial half depth ordinal).firstDestination_heq

theorem last_canonical_next : (finalTarget observation nontrivial half depth ordinal).targetAnswerAndNext.nextCurrent =
    (finalFrame observation nontrivial half depth ordinal).currentPresentation.erase.current :=
  (finalTarget observation nontrivial half depth ordinal).targetAnswerAndNext_next_eq

def finalOriginFace : SourceNativeRootSemanticFaceAt
    (finalTarget observation nontrivial half depth ordinal).targetRoot
    (finalTarget observation nontrivial half depth ordinal).targetVisit where
  projection := (finalTarget observation nontrivial half depth ordinal).oldProjection
    (prefixOriginFace observation nontrivial half depth ordinal).projection
  active := (prefixOriginFace observation nontrivial half depth ordinal).active
  classifier_eq := (prefixOriginFace observation nontrivial half depth ordinal).classifier_eq

def finalR1Face : SourceNativeRootSemanticFaceAt
    (finalTarget observation nontrivial half depth ordinal).targetRoot
    (finalTarget observation nontrivial half depth ordinal).targetVisit where
  projection := (finalTarget observation nontrivial half depth ordinal).oldProjection
    (prefixR1Face observation nontrivial half depth ordinal).projection
  active := (prefixR1Face observation nontrivial half depth ordinal).active
  classifier_eq := (prefixR1Face observation nontrivial half depth ordinal).classifier_eq

theorem final_origin_source : HEq (finalOriginFace observation nontrivial half depth ordinal).rootRead
    (A.targetSourceFace observation nontrivial half depth ordinal).rootRead := HEq.rfl
theorem final_r1_source : HEq (finalR1Face observation nontrivial half depth ordinal).rootRead
    (PX.targetRFace observation nontrivial half depth ordinal).rootRead := HEq.rfl

end OriginalKPaNativeCayleyNextPrefixAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPaNativeCayleyNextPrefixAction"
