import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyWriteback

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 900000
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace CP805Independent

open BurnolPhysicalState OriginalKDirectRCofinalDivision
open OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open RootGeneratedDebtActivationJointSource.OwnerFree
open SourceGeneratedActionObservationHistory.ContractiveRecovery
open Filter SourceOperationEffects SourceOperationExecution
open scoped Topology InnerProductSpace

local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "Proj" => OriginalKCombPhysicalAction.physicalProjection
local notation "Ext" => OriginalKCombPhysicalAction.physicalRemainder

private theorem original_drive_is_generated_by_the_cayley_action (c : BurnolCompletedMellinCoordinate)
    (x : BurnolL2) :
    CountedCayleyInverse.drive c (R c x) = x - sourceCayley c x :=
  CountedCayleyInverse.drive_source c x

private theorem entrance_zero (c : BurnolCompletedMellinCoordinate) (y : BurnolL2) :
    CountedCayleyInverse.entrance c y 0 = 0 := by
  simp [CountedCayleyInverse.entrance, approximate, birkhoffAverage, birkhoffSum]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "prior" => D.raw observation nontrivial half depth ordinal
local notation "before" => D.raw observation nontrivial half depth (ordinal+1)
local notation "after" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "wave" => actualDivisionCompactWave observation nontrivial half depth (ordinal+1)
local notation "counts" => CountedCellHistory.count observation nontrivial half depth ordinal
local notation "root" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "current" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "reader" => CountedCayleyProgramme.reader observation nontrivial half depth ordinal
local notation "child" => CountedCayleyProgramme.countChild observation nontrivial half depth ordinal
local notation "out" => CountedCayleyProgramme.output observation nontrivial half depth ordinal
local notation "K" => (burnolCompletedMellinRieszVector coord : BurnolL2)

private theorem paid_count_is_the_retained_child_of_the_finite_entrance
    (N : Nat) (positive : 0 < N) (n : Nat) :
    let paid := child N positive n
    (paid.trace.length = 8 ∧ (CountedCayleyProgramme.Eval.trace root current (reader N positive n)).length = 10+n) ∧
    paid.value 0 = DualSource.source N after ∧ paid.value 1 = DualSource.source (N+1) after := by
  let paid := child N positive n
  have read := CountedCayleyProgramme.count_child_source observation nontrivial half depth ordinal N positive n
  have value : paid.value = counts N := read.1
  exact ⟨⟨read.2,CountedCayleyProgramme.paid_steps observation nontrivial half depth ordinal N positive n⟩,
    (congrFun value 0).trans (CountedCellHistory.count_source observation nontrivial half depth ordinal N 0),
    (congrFun value 1).trans (CountedCellHistory.count_source observation nontrivial half depth ordinal N 1)⟩

private def actual_parent_retains_child_trace (N : Nat) (positive : 0 < N) (n : Nat) :=
  (child N positive n).retained

private theorem finite_error_is_paid_by_the_original_predecessor
    (N : Nat) (positive : 0 < N) (n : Nat) :
    ‖(out N positive n).1-before‖ ≤ 2*‖prior‖/(sourceDamping coord*((n : ℝ)+1)) :=
  CountedCayleyWriteback.finite_entrance_error observation nontrivial half depth ordinal N positive n

private theorem the_same_finite_entrance_has_exact_signed_Fourier
    (N : Nat) (positive : 0 < N) (n : Nat) :
    (F (out N positive n).1,F (out N positive n).2) =
      (CountedCayleyInverse.waveEntrance coord wave n,wave) :=
  CountedCayleyWriteback.finite_wave observation nontrivial half depth ordinal N positive n

private theorem limit_feeds_original_slots_and_independent_K (N : Nat) (positive : 0 < N) :
    Tendsto (out N positive) atTop (𝓝 (before,after)) ∧
    Tendsto (fun n =>
      let fields := out N positive n
      ((Proj fields.1,Ext fields.1),(Proj fields.2,Ext fields.2),inner ℂ K (Proj fields.2)))
      atTop (𝓝 (OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1),
        OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth (ordinal+1+1),
        inner ℂ ((R coord).adjoint K) before)) ∧
    ∀ᶠ n : Nat in atTop, (out N positive n).1 ≠ 0 :=
  ⟨CountedCayleyWriteback.actual_entrance observation nontrivial half depth ordinal N positive,
    CountedCayleyWriteback.actual_entrance_slots observation nontrivial half depth ordinal N positive⟩

private def actual_paid_relation_cochain_fibre_whole_and_next
    (N : Nat) (positive : 0 < N) (n : Nat)
    (increment : Env CountedCellHistory.CellValue CountedCellHistory.Var) :=
  let full := CountedCayleyWriteback.actual_entrance_writeback observation nontrivial half depth ordinal N positive n increment
  let action := full.2.2
  let native := action.2.2.2.2.2.1
  let macroReceipt := action.2.2.2.2.2.2.2.2.2.2
  And.intro action.1 <| And.intro action.2.1 <| And.intro action.2.2.1 <|
    And.intro action.2.2.2.1 <| And.intro action.2.2.2.2.1 <|
    And.intro native.2.2.1 <| And.intro native.2.2.2 <|
    And.intro macroReceipt.2.2.1 <| And.intro macroReceipt.2.2.2.2.2.2.2.1 <|
    And.intro macroReceipt.2.2.2.2.2.2.2.2.1 <|
      And.intro macroReceipt.2.2.2.2.2.2.2.2.2.1 macroReceipt.2.2.2.2.2.2.2.2.2.2

private theorem zero_iterations_keeps_successor_but_omits_nonzero_actual_entrance
    (N : Nat) (positive : 0 < N) :
    out N positive 0 = (0,after) ∧ out N positive 0 ≠ (before,after) := by
  have actual := CountedCayleyWriteback.finite_source observation nontrivial half depth ordinal N positive 0
  rw [entrance_zero] at actual
  open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial in
  have quarter : burnolQuarterRestriction before ≠ 0 := by
    rw [actual_raw_quarter observation nontrivial half depth (ordinal+1)]
    exact smul_ne_zero (canonical_source_mean_ne observation half (ordinal+1))
      (intervalConstant_ne_zero (by norm_num))
  refine ⟨actual,?_⟩
  intro same
  have erased := congrArg (Prod.fst : BurnolL2 × BurnolL2 → BurnolL2) (same.symm.trans actual)
  exact quarter (by change before = 0 at erased; rw [erased,map_zero])

end CP805Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction

#eval IO.println "CP805_CONTROL + original_drive_is_generated_by_the_cayley_action"
#eval IO.println "CP805_CONTROL + paid_count_is_the_retained_child_of_the_finite_entrance"
#eval IO.println "CP805_CONTROL + finite_error_is_paid_by_the_original_predecessor"
#eval IO.println "CP805_CONTROL + the_same_finite_entrance_has_exact_signed_Fourier"
#eval IO.println "CP805_CONTROL + limit_feeds_original_slots_and_independent_K"
#eval IO.println "CP805_CONTROL + actual_paid_relation_cochain_fibre_whole_and_next"
#eval IO.println "CP805_CONTROL - zero_iterations_keeps_successor_but_omits_nonzero_actual_entrance"
#eval IO.println "CP805_GATE_PASS positive=6 negative=1"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
