import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
import H0mework.Versions.AD.Foundation.Responsibility.JointSource.OwnerFree.Installation.Source
import H0mework.Realization.Operations.Execution.LinearInput

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKPaNativeCayleyNextSource
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

namespace Prog
export OriginalKPaNativePortSourceCalculation (Value Var E rCode)
end Prog
namespace Owner
export RootGeneratedDebtActivationJointSource.OwnerFree (Raw)
end Owner
namespace Installed
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation
  (ResultAt resultAt source_value source_history)
end Installed
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
/-- Literal projections of the already generated canonical-next root and visit. -/
abbrev sourceRoot := (CW.generatedAction observation nontrivial half depth ordinal).target.targetRoot
abbrev sourceVisit := (CW.generatedAction observation nontrivial half depth ordinal).target.targetVisit
private abbrev sourceAuthority := (sourceRoot observation nontrivial half depth ordinal).toAuthoritativeRoot
private abbrev sourceCurrent := (sourceVisit observation nontrivial half depth ordinal).current
private abbrev sourceOccurrence := (sourceRoot observation nontrivial half depth ordinal).emitted
  (sourceCurrent observation nontrivial half depth ordinal)
local notation "authority" => sourceAuthority observation nontrivial half depth ordinal
local notation "nextCurrent" => sourceCurrent observation nontrivial half depth ordinal
local notation "occurrence" => sourceOccurrence observation nontrivial half depth ordinal

def nextREnvironment : Env Prog.Value Prog.Var :=
  fun _ _ => nextPaValue observation nontrivial half depth ordinal

def nextRReader {current : (CW.generatedAction observation nontrivial half depth ordinal).target.TargetV.Current}
    (_source : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :
    Owner.Raw (Value := Prog.Value) (Var := Prog.Var) (sort := ()) :=
  ⟨nextREnvironment observation nontrivial half depth ordinal, Prog.rCode c⟩

def nextRResult : Installed.ResultAt authority
    (nextRReader observation nontrivial half depth ordinal) occurrence :=
  Installed.resultAt authority (nextRReader observation nontrivial half depth ordinal) occurrence

private theorem nextR_expression : (nextRResult observation nontrivial half depth ordinal).2.1.1 =
    .const ((nextRResult observation nontrivial half depth ordinal).2.2.1) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.target_expression authority nextCurrent
    (fun _ => nextRReader observation nontrivial half depth ordinal occurrence)

def nextRTrace : Trace (nextREnvironment observation nontrivial half depth ordinal) (Prog.rCode c)
    (.const ((nextRResult observation nontrivial half depth ordinal).2.2.1)) :=
  Eq.mp (congrArg (fun expression => Trace (nextREnvironment observation nontrivial half depth ordinal)
    (Prog.rCode c) expression) (nextR_expression observation nontrivial half depth ordinal))
      (nextRResult observation nontrivial half depth ordinal).2.1.2

def nextRInput : Σ point : BurnolL2,
    Trace (nextREnvironment observation nontrivial half depth ordinal)
      (.var (0 : Fin 2) : Prog.E) (.const point) ×
    PLift (burnolDirectRightResolventCLM c point =
      (nextRResult observation nontrivial half depth ordinal).2.2.1) :=
  SourceOperationExecution.originalInput (nextRTrace observation nontrivial half depth ordinal)

theorem nextR_input_binding : (nextRInput observation nontrivial half depth ordinal).1 =
    nextPaValue observation nontrivial half depth ordinal :=
  (nextRInput observation nontrivial half depth ordinal).2.1.sound.symm

theorem nextR_equation : (nextRResult observation nontrivial half depth ordinal).2.2.1 =
    burnolDirectRightResolventCLM c (nextPaValue observation nontrivial half depth ordinal) := by
  rw [← (nextRInput observation nontrivial half depth ordinal).2.2.down, nextR_input_binding]

theorem nextR_paid : (nextRResult observation nontrivial half depth ordinal).2.1.2.length =
    remaining (Prog.rCode c) :=
  Installed.source_history authority (nextRReader observation nontrivial half depth ordinal) occurrence

/-- Zero is a downstream control; the same next-source read still executes its original R code. -/
theorem nextR_zero (zero : CW.actualValue observation nontrivial half depth 1 = 0) :
    (nextRResult observation nontrivial half depth ordinal).2.2.1 = 0 ∧
      0 < (nextRResult observation nontrivial half depth ordinal).2.1.2.length := by
  constructor
  · rw [nextR_equation, nextPa_zero observation nontrivial half depth ordinal zero, map_zero]
  · rw [nextR_paid]
    change 0 < _ + 1
    omega

end OriginalKPaNativeCayleyNextSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
