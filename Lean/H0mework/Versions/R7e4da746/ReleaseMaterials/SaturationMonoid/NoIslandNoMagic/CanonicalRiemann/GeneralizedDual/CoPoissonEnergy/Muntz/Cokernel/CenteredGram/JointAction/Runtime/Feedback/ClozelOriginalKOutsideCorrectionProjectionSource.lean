import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionPositiveConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKOutsideCorrectionProjectionSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
namespace Prior
export OriginalKOutsideCorrectionRAction (actualTarget)
export OriginalWholeDebtROutsideCorrectionPositiveConsumer
  (nextState nextValue next_state_source next_trace_source)
end Prior
namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E)
end Prog
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end O
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (ResultAt resultAt source_history)
end Installed
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev sourceRoot := (Prior.actualTarget observation nontrivial half depth ordinal).targetRoot
abbrev sourceVisit := (Prior.actualTarget observation nontrivial half depth ordinal).targetVisit
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev sourceOccurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (sourceCurrent observation nontrivial half depth ordinal)
local notation "authority" => sourceAuthority observation nontrivial half depth ordinal
local notation "current" => sourceCurrent observation nontrivial half depth ordinal
local notation "occurrence" => sourceOccurrence observation nontrivial half depth ordinal

def sourceState := Prior.nextState observation nontrivial half depth ordinal

theorem source_state_source : type_of% (Prior.next_state_source observation nontrivial half depth ordinal) :=
  Prior.next_state_source observation nontrivial half depth ordinal

theorem source_trace_source : type_of% (Prior.next_trace_source observation nontrivial half depth ordinal) :=
  Prior.next_trace_source observation nontrivial half depth ordinal

def environment : Env Prog.Value Prog.Var :=
  fun _ _ => Prior.nextValue observation nontrivial half depth ordinal

def code : Prog.E :=
  .linear (s := ()) (outside).toLinearMap.toAddMonoidHom (.var (0 : Fin 2) : Prog.E)

/-- The actual next root supplies the retained R terminal value; this programme executes only its outside projection. -/
def reader {now : (Prior.actualTarget observation nontrivial half depth ordinal).TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt now) :
    O.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨environment observation nontrivial half depth ordinal, code⟩

def result : Installed.ResultAt authority (reader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (reader observation nontrivial half depth ordinal) occurrence

private theorem expression : (result observation nontrivial half depth ordinal).2.1.1 =
    .const ((result observation nontrivial half depth ordinal).2.2.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression authority current
    (fun _ => reader observation nontrivial half depth ordinal occurrence)

def trace : Trace (environment observation nontrivial half depth ordinal) code
    (.const ((result observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal)
    code expression) (expression observation nontrivial half depth ordinal))
    (result observation nontrivial half depth ordinal).2.1.2

theorem trace_heq : type_of% (mp_heq
    (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal) code expression)
      (expression observation nontrivial half depth ordinal))
    (result observation nontrivial half depth ordinal).2.1.2) :=
  mp_heq (congrArg (fun expression => Trace (environment observation nontrivial half depth ordinal)
    code expression) (expression observation nontrivial half depth ordinal))
    (result observation nontrivial half depth ordinal).2.1.2

def input : Σ point : BurnolL2,
    Trace (environment observation nontrivial half depth ordinal) (.var (0 : Fin 2) : Prog.E) (.const point) ×
    PLift (outside point = (result observation nontrivial half depth ordinal).2.2.1) :=
  originalInput (trace observation nontrivial half depth ordinal)

theorem input_binding : (input observation nontrivial half depth ordinal).1 =
    Prior.nextValue observation nontrivial half depth ordinal :=
  (input observation nontrivial half depth ordinal).2.1.sound.symm

theorem equation : (result observation nontrivial half depth ordinal).2.2.1 =
    outside (Prior.nextValue observation nontrivial half depth ordinal) :=
  (input observation nontrivial half depth ordinal).2.2.down.symm.trans
    (congrArg outside (input_binding observation nontrivial half depth ordinal))

theorem paid : (result observation nontrivial half depth ordinal).2.1.2.length = 2 :=
  Installed.source_history authority (reader observation nontrivial half depth ordinal) occurrence

end OriginalKOutsideCorrectionProjectionSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalKOutsideCorrectionProjectionSource"
