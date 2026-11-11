import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionRRegisteredReceiptConsumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionNonzeroSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtROutsideCorrectionEnergySource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtROutsideCorrectionPositiveConsumer
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open private r_expression from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
open private actual_outside_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRCorrectionActionSource
namespace S
export OriginalKOutsideCorrectionRSource (rResult rEnvironment)
end S
namespace A
export OriginalKOutsideCorrectionRAction
  (sourceRoot sourceVisit sourceU7 sourceCalculus sourceReader actualTarget whole_first canonical_next)
end A
namespace Adapter
export OriginalKPaNativeCayleyNextPrefixSource.Adapter (targetFace state terminalValue)
end Adapter
namespace O
export RootGeneratedDebtActivationJointSource.OwnerFree (Current raw)
end O
namespace C
export OriginalWholeDebtROutsideCorrectionRConsumer
  (actualInput actualResult actual_input_source actual_source_equation)
end C
namespace N
export OriginalWholeDebtROutsideCorrectionNonzeroSource
  (original_correction_ne_zero original_sourceFirst_ne_zero original_sourceJump_ne_zero)
end N
namespace E
export OriginalWholeDebtROutsideCorrectionEnergySource
  (actual_input_outside actual_outside_balance actual_outside_bound actual_outside_zero_iff)
export OriginalKCrossParameterRAdjointSource.CayleyEnergySource (sourceDamping sourceDamping_pos)
end E
namespace Prior
export OriginalWholeDebtROutsideCorrectionRRegisteredReceiptConsumer (actual_original_correction_R_whole_next)
end Prior
local notation "outside" => OriginalKCombPhysicalAction.physicalRemainder
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "src" => A.sourceRoot observation nontrivial half depth ordinal
local notation "here" => A.sourceVisit observation nontrivial half depth ordinal
local notation "u7" => A.sourceU7 observation nontrivial half depth ordinal
local notation "calculus" => A.sourceCalculus observation nontrivial half depth ordinal
local notation "reader" => A.sourceReader observation nontrivial half depth ordinal
local notation "x" => C.actualInput observation nontrivial half depth ordinal
local notation "y" => C.actualResult observation nontrivial half depth ordinal

/-- The paid generic adapter reads this R's terminal State at its actual residual first-write target. -/
def nextFace := Adapter.targetFace src here u7 calculus reader
def nextState := Adapter.state src here u7 calculus reader
def nextValue := Adapter.terminalValue src here u7 calculus reader

theorem next_state_source : HEq (nextState observation nontrivial half depth ordinal) (S.rResult observation nontrivial half depth ordinal).2.1 := HEq.rfl

theorem next_trace_source : HEq (nextState observation nontrivial half depth ordinal).2 (S.rResult observation nontrivial half depth ordinal).2.1.2 := HEq.rfl

private theorem next_terminal : (nextState observation nontrivial half depth ordinal).1 = .const y :=
  (congrArg (fun state : O.Current (src).toAuthoritativeRoot (here).current reader => state.1)
    (eq_of_heq (next_state_source observation nontrivial half depth ordinal))).trans
      (r_expression observation nontrivial half depth ordinal)

theorem next_value_source : nextValue observation nontrivial half depth ordinal = y :=
  congrArg (fun expression => expression.eval (O.raw (src).toAuthoritativeRoot (here).current reader).environment)
    (next_terminal observation nontrivial half depth ordinal)

theorem actual_input_ne_zero : x ≠ 0 := by
  rw [C.actual_input_source]
  exact N.original_correction_ne_zero observation nontrivial half

theorem actual_result_ne_zero : y ≠ 0 := by
  intro zero
  apply actual_input_ne_zero observation nontrivial half depth ordinal
  apply (E.actual_outside_zero_iff observation nontrivial half depth ordinal).mp
  rw [zero]
  exact map_zero _

def outsideLowerPrice : ℝ :=
  E.sourceDamping c * ‖nextValue observation nontrivial half depth ordinal‖ ^ 2 / (2 * ‖x‖)

theorem outside_lower_price_pos : 0 < outsideLowerPrice observation nontrivial half depth ordinal := by
  unfold outsideLowerPrice
  rw [next_value_source]
  exact div_pos (mul_pos (E.sourceDamping_pos c)
    (sq_pos_of_pos (norm_pos_iff.mpr (actual_result_ne_zero observation nontrivial half depth ordinal))))
    (mul_pos (by norm_num) (norm_pos_iff.mpr (actual_input_ne_zero observation nontrivial half depth ordinal)))

theorem outside_lower_price_le :
    outsideLowerPrice observation nontrivial half depth ordinal ≤ ‖outside (nextValue observation nontrivial half depth ordinal)‖ := by
  unfold outsideLowerPrice
  rw [next_value_source]
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
    (norm_pos_iff.mpr (actual_input_ne_zero observation nontrivial half depth ordinal)))).mpr
  nlinarith [E.actual_outside_bound observation nontrivial half depth ordinal]

theorem actual_next_outside_pos : 0 < ‖outside (nextValue observation nontrivial half depth ordinal)‖ :=
  (outside_lower_price_pos observation nontrivial half depth ordinal).trans_le (outside_lower_price_le observation nontrivial half depth ordinal)

theorem actual_next_B_source :
    outside (nextValue observation nontrivial half depth ordinal) = OriginalWholeDebtRCorrectionActionSource.nativeOutside c := by
  rw [next_value_source, C.actual_source_equation, C.actual_input_source]
  exact actual_outside_source c

include depth ordinal in
theorem actual_complete_B_ne_zero : OriginalWholeDebtRCorrectionActionSource.nativeOutside c ≠ 0 := by
  rw [←actual_next_B_source observation nontrivial half depth ordinal]
  exact norm_pos_iff.mp (actual_next_outside_pos observation nontrivial half depth ordinal)

private def Receipt : Sort _ :=
  Σ' original : type_of% (Prior.actual_original_correction_R_whole_next observation nontrivial half depth ordinal),
    PProd (original = Prior.actual_original_correction_R_whole_next observation nontrivial half depth ordinal) (
  Σ' stateData : type_of% (nextState observation nontrivial half depth ordinal),
    PProd (stateData = nextState observation nontrivial half depth ordinal) (
      (type_of% (next_state_source observation nontrivial half depth ordinal)) ∧
      (type_of% (next_trace_source observation nontrivial half depth ordinal)) ∧
      (type_of% (next_value_source observation nontrivial half depth ordinal)) ∧
      (type_of% (N.original_sourceJump_ne_zero observation nontrivial half)) ∧
      (type_of% (N.original_sourceFirst_ne_zero observation nontrivial half)) ∧
      (type_of% (actual_input_ne_zero observation nontrivial half depth ordinal)) ∧
      (type_of% (actual_result_ne_zero observation nontrivial half depth ordinal)) ∧
      (type_of% (E.actual_outside_balance observation nontrivial half depth ordinal)) ∧
      (type_of% (E.actual_outside_zero_iff observation nontrivial half depth ordinal)) ∧
      (type_of% (outside_lower_price_pos observation nontrivial half depth ordinal)) ∧
      (type_of% (outside_lower_price_le observation nontrivial half depth ordinal)) ∧
      (type_of% (actual_next_B_source observation nontrivial half depth ordinal)) ∧
      (type_of% (actual_complete_B_ne_zero observation nontrivial half depth ordinal)) ∧
      (type_of% (A.whole_first observation nontrivial half depth ordinal)) ∧
      (type_of% (A.canonical_next observation nontrivial half depth ordinal))))

noncomputable opaque actual_original_complete_B_price_whole_next : Receipt observation nontrivial half depth ordinal := by
  exact ⟨Prior.actual_original_correction_R_whole_next observation nontrivial half depth ordinal, rfl,
    nextState observation nontrivial half depth ordinal, rfl, next_state_source observation nontrivial half depth ordinal,
    next_trace_source observation nontrivial half depth ordinal, next_value_source observation nontrivial half depth ordinal,
    N.original_sourceJump_ne_zero observation nontrivial half,
    N.original_sourceFirst_ne_zero observation nontrivial half,
    actual_input_ne_zero observation nontrivial half depth ordinal, actual_result_ne_zero observation nontrivial half depth ordinal,
    E.actual_outside_balance observation nontrivial half depth ordinal, E.actual_outside_zero_iff observation nontrivial half depth ordinal,
    outside_lower_price_pos observation nontrivial half depth ordinal, outside_lower_price_le observation nontrivial half depth ordinal,
    actual_next_B_source observation nontrivial half depth ordinal, actual_complete_B_ne_zero observation nontrivial half depth ordinal,
    A.whole_first observation nontrivial half depth ordinal, A.canonical_next observation nontrivial half depth ordinal⟩

end OriginalWholeDebtROutsideCorrectionPositiveConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalWholeDebtROutsideCorrectionPositiveConsumer"

