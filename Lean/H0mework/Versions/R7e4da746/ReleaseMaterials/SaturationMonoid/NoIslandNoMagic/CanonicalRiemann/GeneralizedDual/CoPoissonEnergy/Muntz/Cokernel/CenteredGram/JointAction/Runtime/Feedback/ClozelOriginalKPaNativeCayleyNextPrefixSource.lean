import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKReturnJordanSourceCalculation
import H0mework.Realization.Operations.Execution.LinearInput

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option pp.deepTerms.threshold 24
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleyNextPrefixSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution BurnolPhysicalState
open private nextR_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextRSource
namespace A
export OriginalKPaNativeCayleyNextAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualTarget r_value_source)
end A
namespace NS
export OriginalKPaNativeCayleyNextSource (nextPaValue nextRResult nextR_equation)
end NS
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw raw Current)
end O
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (targetState target_expression value)
end OC
namespace MS
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source
  (answerFace endpointCount endpoint_source_state residualTarget)
end MS
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation
  (ResultAt resultAt source_value source_history)
end Installed
namespace Prog
export OriginalKReturnJordanSourceCalculation (Value Var E prefixCode prefix_code_eval)
export OriginalKPaNativePortSourceCalculation (rCode)
end Prog

namespace Adapter
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (u7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N u7)
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ sort, AddCommGroup (Value sort)] {sort : Sorts}
variable (reader : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current →
  O.Raw (Value := Value) (Var := Var) (sort := sort))

/-- The existing answer projection, inherited by the actual residual first-write target. -/
def targetFace : SourceNativeRootSemanticFaceAt
    (MS.residualTarget root visit u7 calculus reader).targetRoot
    (MS.residualTarget root visit u7 calculus reader).targetVisit where
  projection := (MS.residualTarget root visit u7 calculus reader).oldProjection
    (MS.answerFace root visit u7 calculus reader (MS.endpointCount root visit reader)).projection
  active := PUnit.unit
  classifier_eq := rfl

def state : O.Current root.toAuthoritativeRoot visit.current reader :=
  (targetFace root visit u7 calculus reader).rootRead

def terminalValue : Value sort :=
  (state root visit u7 calculus reader).1.eval (O.raw root.toAuthoritativeRoot visit.current reader).environment
end Adapter

private def prefixSeed {environment : Env Prog.Value Prog.Var}
    (coordinate : BurnolCompletedMellinCoordinate) : (order : Nat) → {value : BurnolL2} →
    Trace environment (Prog.prefixCode coordinate order) (.const value) →
      Σ seed : BurnolL2, Trace environment (.var (0 : Fin 2) : Prog.E) (.const seed)
  | 0, value, trace => ⟨value, trace⟩
  | order+1, _, trace =>
      let child := SourceOperationExecution.originalInput trace
      prefixSeed coordinate order child.2.1

private theorem prefix_budget (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) :
    remaining (Prog.prefixCode coordinate order) = order+1 := by
  induction order with
  | zero => rfl
  | succ order previous =>
    change remaining (Prog.prefixCode coordinate order) + 1 = order+1+1
    rw [previous]

private theorem resumed_power (coordinate : BurnolCompletedMellinCoordinate) (order : Nat)
    (positive : 0 < order) (value : BurnolL2) :
    ((burnolDirectRightResolventCLM coordinate)^(order-1))
      (burnolDirectRightResolventCLM coordinate value) =
        ((burnolDirectRightResolventCLM coordinate)^order) value := by
  change (((burnolDirectRightResolventCLM coordinate)^(order-1)) *
    burnolDirectRightResolventCLM coordinate) value = _
  rw [←pow_succ, show order-1+1=order by omega]

private theorem forward_power (coordinate : BurnolCompletedMellinCoordinate) (order : Nat)
    (value : BurnolL2) :
    burnolDirectRightResolventCLM coordinate (((burnolDirectRightResolventCLM coordinate)^order) value) =
      ((burnolDirectRightResolventCLM coordinate)^(order+1)) value := by
  rw [pow_succ', mul_apply_eq_comp]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal

def targetRFace := Adapter.targetFace src here u7 calculus reader
def targetRState := Adapter.state src here u7 calculus reader
def targetRValue := Adapter.terminalValue src here u7 calculus reader

theorem targetR_state_source : HEq (targetRState observation nontrivial half depth ordinal)
    (NS.nextRResult observation nontrivial half depth ordinal).2.1 := HEq.rfl

theorem targetR_trace_source : HEq (targetRState observation nontrivial half depth ordinal).2
    (NS.nextRResult observation nontrivial half depth ordinal).2.1.2 := HEq.rfl

private theorem targetR_original_terminal : (targetRState observation nontrivial half depth ordinal).1 =
    .const ((NS.nextRResult observation nontrivial half depth ordinal).2.2.1) :=
  (congrArg (fun state : O.Current (src).toAuthoritativeRoot (here).current reader => state.1)
    (eq_of_heq (targetR_state_source observation nontrivial half depth ordinal))).trans
      (nextR_expression observation nontrivial half depth ordinal)

theorem targetR_value_source : targetRValue observation nontrivial half depth ordinal =
    (NS.nextRResult observation nontrivial half depth ordinal).2.2.1 :=
  congrArg (fun expression => expression.eval (O.raw (src).toAuthoritativeRoot (here).current reader).environment)
    (targetR_original_terminal observation nontrivial half depth ordinal)

theorem targetR_terminal : (targetRState observation nontrivial half depth ordinal).1 =
    .const (targetRValue observation nontrivial half depth ordinal) :=
  (targetR_original_terminal observation nontrivial half depth ordinal).trans
    (congrArg Expr.const (targetR_value_source observation nontrivial half depth ordinal).symm)

def targetRTrace : Trace (O.raw (src).toAuthoritativeRoot (here).current reader).environment
    (O.raw (src).toAuthoritativeRoot (here).current reader).expression
    (.const (targetRValue observation nontrivial half depth ordinal)) :=
  Eq.mp (congrArg (fun expression => Trace
    (O.raw (src).toAuthoritativeRoot (here).current reader).environment
    (O.raw (src).toAuthoritativeRoot (here).current reader).expression expression)
      (targetR_terminal observation nontrivial half depth ordinal))
    (targetRState observation nontrivial half depth ordinal).2

/-- These are the literal root and visit generated by the already paid R₁ inquiry. -/
abbrev sourceRoot := (A.actualTarget observation nontrivial half depth ordinal).targetRoot
abbrev sourceVisit := (A.actualTarget observation nontrivial half depth ordinal).targetVisit
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev sourceOccurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (sourceCurrent observation nontrivial half depth ordinal)
local notation "authority" => sourceAuthority observation nontrivial half depth ordinal
local notation "current" => sourceCurrent observation nontrivial half depth ordinal
local notation "occurrence" => sourceOccurrence observation nontrivial half depth ordinal

def prefixEnvironment : Env Prog.Value Prog.Var :=
  fun _ _ => targetRValue observation nontrivial half depth ordinal

def prefixReader {atCurrent : (A.actualTarget observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt atCurrent) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨prefixEnvironment observation nontrivial half depth ordinal, Prog.prefixCode c (m-1)⟩

def prefixResult : Installed.ResultAt authority
    (prefixReader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (prefixReader observation nontrivial half depth ordinal) occurrence

private theorem prefix_expression : (prefixResult observation nontrivial half depth ordinal).2.1.1 =
    .const ((prefixResult observation nontrivial half depth ordinal).2.2.1) :=
  OC.target_expression authority current (fun _ => prefixReader observation nontrivial half depth ordinal occurrence)

def prefixTrace : Trace (prefixEnvironment observation nontrivial half depth ordinal) (Prog.prefixCode c (m-1))
    (.const ((prefixResult observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (prefixEnvironment observation nontrivial half depth ordinal)
    (Prog.prefixCode c (m-1)) expression) (prefix_expression observation nontrivial half depth ordinal))
      (prefixResult observation nontrivial half depth ordinal).2.1.2

def prefixInput := prefixSeed c (m-1) (prefixTrace observation nontrivial half depth ordinal)

theorem prefix_input_binding : (prefixInput observation nontrivial half depth ordinal).1 =
    targetRValue observation nontrivial half depth ordinal :=
  (prefixInput observation nontrivial half depth ordinal).2.sound.symm

theorem prefix_value : (prefixResult observation nontrivial half depth ordinal).2.2.1 =
    ((burnolDirectRightResolventCLM c)^m) (NS.nextPaValue observation nontrivial half depth ordinal) := by
  have source := Installed.source_value authority (prefixReader observation nontrivial half depth ordinal) occurrence
  have evaluated := Prog.prefix_code_eval (prefixEnvironment observation nontrivial half depth ordinal) c (m-1)
  have seed := (targetR_value_source observation nontrivial half depth ordinal).trans
    (NS.nextR_equation observation nontrivial half depth ordinal)
  exact source.trans (evaluated.trans
    ((congrArg (fun value => ((burnolDirectRightResolventCLM c)^(m-1)) value) seed).trans
      (resumed_power c m (generatedRiemannXiZeroOrder_pos observation nontrivial)
        (NS.nextPaValue observation nontrivial half depth ordinal))))

theorem prefix_paid : (prefixResult observation nontrivial half depth ordinal).2.1.2.length = (m-1)+1 :=
  (Installed.source_history authority (prefixReader observation nontrivial half depth ordinal) occurrence).trans
    (prefix_budget c (m-1))

theorem order_one_control (order : m = 1) :
    (prefixReader observation nontrivial half depth ordinal occurrence).expression = (.var (0 : Fin 2) : Prog.E) ∧
    (prefixResult observation nontrivial half depth ordinal).2.1.2.length = 1 ∧
    (prefixResult observation nontrivial half depth ordinal).2.2.1 = targetRValue observation nontrivial half depth ordinal := by
  have code : Prog.prefixCode c (m-1) = (.var (0 : Fin 2) : Prog.E) :=
    congrArg (fun n => Prog.prefixCode c (n-1)) order
  exact ⟨code,
    (prefix_paid observation nontrivial half depth ordinal).trans (congrArg (fun n => (n-1)+1) order),
    (Installed.source_value authority (prefixReader observation nontrivial half depth ordinal) occurrence).trans
      (congrArg (fun expression => expression.eval (prefixEnvironment observation nontrivial half depth ordinal)) code)⟩

def lastREnvironment : Env Prog.Value Prog.Var :=
  fun _ _ => (prefixResult observation nontrivial half depth ordinal).2.2.1

def lastRReader {atCurrent : (A.actualTarget observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt atCurrent) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨lastREnvironment observation nontrivial half depth ordinal, Prog.rCode c⟩

def lastRResult : Installed.ResultAt authority
    (lastRReader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (lastRReader observation nontrivial half depth ordinal) occurrence

private theorem lastR_expression : (lastRResult observation nontrivial half depth ordinal).2.1.1 =
    .const ((lastRResult observation nontrivial half depth ordinal).2.2.1) :=
  OC.target_expression authority current (fun _ => lastRReader observation nontrivial half depth ordinal occurrence)

def lastRTrace : Trace (lastREnvironment observation nontrivial half depth ordinal) (Prog.rCode c)
    (.const ((lastRResult observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (lastREnvironment observation nontrivial half depth ordinal)
    (Prog.rCode c) expression) (lastR_expression observation nontrivial half depth ordinal))
      (lastRResult observation nontrivial half depth ordinal).2.1.2

def lastRInput : Σ point : BurnolL2,
    Trace (lastREnvironment observation nontrivial half depth ordinal) (.var (0 : Fin 2) : Prog.E) (.const point) ×
    PLift (burnolDirectRightResolventCLM c point = (lastRResult observation nontrivial half depth ordinal).2.2.1) :=
  SourceOperationExecution.originalInput (lastRTrace observation nontrivial half depth ordinal)

theorem lastR_input_binding : (lastRInput observation nontrivial half depth ordinal).1 =
    (prefixResult observation nontrivial half depth ordinal).2.2.1 :=
  (lastRInput observation nontrivial half depth ordinal).2.1.sound.symm

theorem lastR_equation : (lastRResult observation nontrivial half depth ordinal).2.2.1 =
    burnolDirectRightResolventCLM c ((prefixResult observation nontrivial half depth ordinal).2.2.1) :=
  (lastRInput observation nontrivial half depth ordinal).2.2.down.symm.trans
    (congrArg (burnolDirectRightResolventCLM c) (lastR_input_binding observation nontrivial half depth ordinal))

theorem lastR_value : (lastRResult observation nontrivial half depth ordinal).2.2.1 =
    ((burnolDirectRightResolventCLM c)^(m+1)) (NS.nextPaValue observation nontrivial half depth ordinal) :=
  (lastR_equation observation nontrivial half depth ordinal).trans
    ((congrArg (burnolDirectRightResolventCLM c) (prefix_value observation nontrivial half depth ordinal)).trans
      (forward_power c m (NS.nextPaValue observation nontrivial half depth ordinal)))

theorem lastR_paid : (lastRResult observation nontrivial half depth ordinal).2.1.2.length =
    remaining (Prog.rCode c) :=
  Installed.source_history authority (lastRReader observation nontrivial half depth ordinal) occurrence

end OriginalKPaNativeCayleyNextPrefixSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKPaNativeCayleyNextPrefixSource"
