import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierNative.Action
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextPrefixSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Source.WholeFlow

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierNativeConsumer
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open FixedWindowFourierReaction FixedWindowFourierReaction.FullSchur
open OriginalRieszSource
namespace A
export OriginalConstantFourierNativeAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actionState actionTrace actionValue action_value_source actualTarget)
end A
namespace S
export OriginalConstantFourierNativeSource (result original_quarter_value)
end S
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace OC
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (value paid_history)
end OC
namespace W
export OriginalConstantFourierWholeFlow
  (etaPath uPath vPath muPath nuPath forcingPath sourceMu sourceNu fullForcing sourceU
   actual_mean_velocities actual_full_path_equation actual_full_forcing_velocity
   actual_existing_inverse_path actual_existing_inverse_velocity)
end W
open private state_source trace_source trace_length expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPairedWaveNativeStockSource

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "M" => BurnolQuarterMeanZeroCarrier

/-- This face reads the actual first-write target's answer, including the paid history. -/
noncomputable def nextFace (t:ℝ) :=
  Adapter.targetFace src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)
noncomputable def nextState (t:ℝ) :=
  Adapter.state src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)
noncomputable def nextValue (t:ℝ) :=
  Adapter.terminalValue src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)

theorem next_state_source (t:ℝ) : HEq (nextState observation nontrivial half depth ordinal t)
    (A.actionState observation nontrivial half depth ordinal t) :=
  state_source src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)

theorem next_trace_source (t:ℝ) : HEq (nextState observation nontrivial half depth ordinal t).2
    (A.actionTrace observation nontrivial half depth ordinal t) :=
  trace_source src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)

theorem next_paid (t:ℝ) : (nextState observation nontrivial half depth ordinal t).2.length=5 := by
  rw [nextState,trace_length src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)]
  exact OC.paid_history (src).toAuthoritativeRoot (here).current
    (A.sourceReader observation nontrivial half depth ordinal t)

theorem next_value_source (t:ℝ) : nextValue observation nontrivial half depth ordinal t=
    (S.result observation nontrivial half depth ordinal t).2.2.1 := by
  have value : nextValue observation nontrivial half depth ordinal t=
      OC.value (src).toAuthoritativeRoot (here).current
        (A.sourceReader observation nontrivial half depth ordinal t) := by
    unfold nextValue Adapter.terminalValue
    rw [expression src here u7 calculus (A.sourceReader observation nontrivial half depth ordinal t)]
    rfl
  exact value.trans (A.action_value_source observation nontrivial half depth ordinal t)

noncomputable def nextQuarter (t:ℝ) : Hq :=
  burnolQuarterRestriction (nextValue observation nontrivial half depth ordinal t)

theorem next_quarter_source (t:ℝ) : nextQuarter observation nontrivial half depth ordinal t=
    ConstantFourierEulerVelocity.originalSource t := by
  rw [nextQuarter,next_value_source]
  exact S.original_quarter_value observation nontrivial half depth ordinal t

noncomputable def eta (t:ℝ) : M := Constructor.zeroMean (nextQuarter observation nontrivial half depth ordinal t)
noncomputable def u (t:ℝ) : M := burnolMeanZeroBlockInverse (eta observation nontrivial half depth ordinal t)
noncomputable def v (t:ℝ) : M := burnolMeanZeroTruncatedFourier (u observation nontrivial half depth ordinal t)
noncomputable def mu (t:ℝ) : ℂ := burnolQuarterMeanCoefficient (burnolTruncatedFourier (u observation nontrivial half depth ordinal t:Hq))
noncomputable def nu (t:ℝ) : ℂ := burnolQuarterMeanCoefficient (burnolTruncatedFourier (v observation nontrivial half depth ordinal t:Hq))
noncomputable def forcing (t:ℝ) : Hq := (eta observation nontrivial half depth ordinal t:Hq)-
  nu observation nontrivial half depth ordinal t • intervalConstant q-
    mu observation nontrivial half depth ordinal t • burnolTruncatedFourier (intervalConstant q)

theorem eta_source (t:ℝ) : eta observation nontrivial half depth ordinal t=W.etaPath t := by
  unfold eta W.etaPath
  rw [next_quarter_source]
theorem u_source (t:ℝ) : u observation nontrivial half depth ordinal t=W.uPath t := by
  unfold u W.uPath
  rw [eta_source]
theorem v_source (t:ℝ) : v observation nontrivial half depth ordinal t=W.vPath t := by
  unfold v W.vPath
  rw [u_source]
theorem mu_source (t:ℝ) : mu observation nontrivial half depth ordinal t=W.muPath t := by
  unfold mu W.muPath
  rw [u_source]
theorem nu_source (t:ℝ) : nu observation nontrivial half depth ordinal t=W.nuPath t := by
  unfold nu W.nuPath
  rw [v_source]
theorem forcing_source (t:ℝ) : forcing observation nontrivial half depth ordinal t=W.forcingPath t := by
  unfold forcing W.forcingPath
  rw [eta_source,nu_source,mu_source]

/-- Both means are read from this target's full source; neither is a supplied scalar. -/
theorem actual_mean_velocities :
    HasDerivAt (mu observation nontrivial half depth ordinal) W.sourceMu 0 ∧
      HasDerivAt (nu observation nontrivial half depth ordinal) W.sourceNu 0 :=
  ⟨W.actual_mean_velocities.1.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (mu_source observation nontrivial half depth ordinal)),
   W.actual_mean_velocities.2.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (nu_source observation nontrivial half depth ordinal))⟩

theorem actual_full_equation (t:ℝ) : (u observation nontrivial half depth ordinal t:Hq)-
    burnolTruncatedFourier (burnolTruncatedFourier (u observation nontrivial half depth ordinal t:Hq))=
      forcing observation nontrivial half depth ordinal t := by
  rw [u_source,forcing_source]
  exact W.actual_full_path_equation t

theorem actual_full_forcing_velocity :
    HasDerivAt (forcing observation nontrivial half depth ordinal) W.fullForcing 0 :=
  W.actual_full_forcing_velocity.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (forcing_source observation nontrivial half depth ordinal))

/-- The existing full inverse now consumes the literal first-write target's complete forcing. -/
theorem actual_existing_inverse (t:ℝ) :
    sourceInverse q (quarterChart (forcing observation nontrivial half depth ordinal t))=
      quarterChart (u observation nontrivial half depth ordinal t:Hq) := by
  rw [forcing_source,u_source]
  exact W.actual_existing_inverse_path t

theorem actual_existing_inverse_velocity : HasDerivAt
    (fun t:ℝ=>sourceInverse q (quarterChart (forcing observation nontrivial half depth ordinal t))) W.sourceU 0 :=
  W.actual_existing_inverse_velocity.congr_of_eventuallyEq (Filter.Eventually.of_forall
    (fun t=>congrArg (fun value:Hq=>sourceInverse q (quarterChart value))
      (forcing_source observation nontrivial half depth ordinal t)))

end OriginalConstantFourierNativeConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierNativeConsumer"
