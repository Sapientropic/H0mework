import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyResidualRecoveryConsumer

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 800000
set_option linter.defProp false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CP808Independent

open BurnolPhysicalState Filter RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open RootGeneratedDebtActivationJointSource.OwnerFree
open CountedCayleyResidualInverse (approximate approximate_succ data defect effect effect_inverse recover)
open CountedCayleyResidualInverse.Geom (clock driveScale finite finite_zero retention retention_pos)
open CountedCayleyResidualRecovery
open scoped InnerProductSpace Topology

open private slotRead from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocityReceipt

local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2

private theorem empty_approximation (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    approximate c 0 x = 0 := by
  rw [approximate, finite_zero, ContinuousLinearMap.zero_apply]

private theorem one_approximation_ne_zero (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (live : x ≠ 0) : approximate c 1 x ≠ 0 := by
  have damping := sourceDamping_pos c
  have scale : driveScale (sourceDamping c) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (Complex.ofReal_ne_zero.mpr damping.ne')
      (Complex.ofReal_ne_zero.mpr (retention_pos damping).ne'))
  rw [show (1 : Nat) = 0+1 from rfl, approximate_succ, empty_approximation, map_zero, zero_add]
  exact smul_ne_zero scale live

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "d" => sourceDamping c
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "point" "[" j "]" => D.raw observation nontrivial half depth j
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "values" => CountedCayleyIncrement.residualRead observation nontrivial half depth ordinal
local notation "readPair" => data observation nontrivial half depth ordinal
local notation "oldPair" => CountedCayleyProgramme.output observation nontrivial half depth ordinal
local notation "fit" => fields observation nontrivial half depth ordinal
local notation "child" => pairedChild observation nontrivial half depth ordinal
local notation "authority" => CountedFiniteNative.root observation nontrivial half depth ordinal
local notation "origin" => CountedFiniteNative.current observation nontrivial half depth ordinal
local notation "oldReader" => CountedCayleyProgramme.reader observation nontrivial half depth ordinal
local notation "newReader" => CountedCayleyResidualRecovery.reader observation nontrivial half depth ordinal
local notation "delta" => CountedCayleyIncrement.increment observation nontrivial half depth ordinal

private theorem both_paid_residual_slots_and_exact_inverse (N : Nat) (positive : 0 < N) (n : Nat) :
    readPair N positive n = (values N positive n 0, values N positive n 1) ∧
    readPair N positive n = (R c (oldPair N positive n).1 - (oldPair N positive n).1,
      R c (oldPair N positive n).2 - (oldPair N positive n).2) ∧
    (recover c (readPair N positive n).1,recover c (readPair N positive n).2) = oldPair N positive n :=
  ⟨rfl,CountedCayleyResidualInverse.actual_effect observation nontrivial half depth ordinal N positive n,
    CountedCayleyResidualInverse.actual_recovered observation nontrivial half depth ordinal N positive n⟩

private theorem finite_recovery_error_uses_paid_residual_and_transports_defect
    (N : Nat) (positive : 0 < N) (n m : Nat) :
    ‖fit N positive n m - oldPair N positive n‖ ≤ retention d ^ m * ‖readPair N positive n‖ ∧
    defect c (fit N positive n m) = approximate c m (defect c (readPair N positive n)) :=
  ⟨actual_finite_error observation nontrivial half depth ordinal N positive n m,
    actual_finite_defect observation nontrivial half depth ordinal N positive n m⟩

private def retained_paired_child (N : Nat) (positive : 0 < N) (n m : Nat) :=
  (child N positive n m).retained

private theorem actual_paired_child_preserves_old_field_effect_and_steps (N : Nat) (positive : 0 < N)
    (n m : Nat) :
    let source := raw authority origin (oldReader N positive n)
    let paid := child N positive n m
    paid.value = (CountedCayleyProgramme.Eval.value authority origin (oldReader N positive n),
      source.expression.effect source.environment (delta N positive n)) ∧
    paid.trace.length = 10+n ∧
    (CountedCayleyResidualRecovery.Eval.trace authority origin (newReader N positive n m)).length = 10+n+1+m := by
  have source := paired_child_source observation nontrivial half depth ordinal N positive n m
  exact ⟨source.1,source.2,paid_rounds observation nontrivial half depth ordinal N positive n m⟩

private theorem exact_finite_positive_clock_fourier (N : Nat) (positive : 0 < N) (n m : Nat) :
    (F (fit N positive n m).1,F (fit N positive n m).2) =
      (finite (waveResolvent c) d m (F (readPair N positive n).1),
       finite (waveResolvent c) d m (F (readPair N positive n).2)) ∧
    ∀ x, waveResolvent c x = FiniteMobiusResolventFlux.Rplus (c.value/2) x :=
  ⟨actual_wave_fields observation nontrivial half depth ordinal N positive n m, wave_resolvent_source c⟩

private theorem actual_diagonal_graph_and_independent_K (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => fit N positive n n) atTop (𝓝 (point[ordinal+1],point[ordinal+1+1])) ∧
    Tendsto (fun n => defect c (fit N positive n n)) atTop (𝓝 0) ∧
    Tendsto (fun n => slotRead K (fit N positive n n)) atTop
      (𝓝 (nativeInput (ordinal+1),nativeInput (ordinal+1+1),inner ℂ ((R c).adjoint K) point[ordinal+1])) :=
  ⟨actual_diagonal_fields observation nontrivial half depth ordinal N positive,
    actual_defect_zero_limit observation nontrivial half depth ordinal N positive,
    actual_independent_K observation nontrivial half depth ordinal N positive⟩

private def recovery_and_original_ledger_consumers (N : Nat) (positive : 0 < N) (n m : Nat) :=
  let consumed := consume_actual_recovery observation nontrivial half depth ordinal N positive n m
  let paid := consumed.1
  let newWholeNext := paid.2.2.2.2.2
  let update := consumed.2.1
  let original := update.2.2.2.2.2.2
  let oldWholeNext := original.2.2.2.2.2.2.2.1
  let originalMacro := original.2.2.2.2.2.2.2.2.2.2.2
  And.intro paid.2.2.1 <| And.intro paid.2.2.2.1 <| And.intro paid.2.2.2.2.1 <|
    And.intro newWholeNext.2.2.1 <| And.intro newWholeNext.2.2.2 <|
    And.intro update.2.2.2.2.1 <| And.intro oldWholeNext.2.2.1 <| And.intro oldWholeNext.2.2.2 <|
    And.intro originalMacro.2.2.2.2.2.2.2.1 <|
    And.intro originalMacro.2.2.2.2.2.2.2.2.1 originalMacro.2.2.2.2.2.2.2.2.2

private theorem actual_zero_entrance_defect_excludes_exact_graph_preimage (N : Nat) (positive : 0 < N) :
    defect c (readPair N positive 0) ≠ 0 ∧
    ¬ ∃ x, (effect c x,effect c (R c x)) = readPair N positive 0 := by
  have live := CountedCayleyResidualInverse.actual_zero_round_defect
    observation nontrivial half depth ordinal N positive
  refine ⟨live,?_⟩
  rintro ⟨x,payment⟩
  apply live
  apply (CountedCayleyResidualInverse.exact_incidence_fibre c (readPair N positive 0)).mp
  refine ⟨x,payment,?_⟩
  intro y same
  exact (effect_inverse c).1.injective (congrArg Prod.fst (same.trans payment.symm))

private theorem zero_inverse_rounds_erase_both_slots_and_one_retains_the_successor
    (N : Nat) (positive : 0 < N) (n : Nat) :
    fit N positive n 0 = (0,0) ∧ (fit N positive n 1).2 ≠ 0 := by
  constructor
  · exact (fields_source observation nontrivial half depth ordinal N positive n 0).trans
      (Prod.ext (empty_approximation c _) (empty_approximation c _))
  · have actual := congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2)
      (fields_source observation nontrivial half depth ordinal N positive n 1)
    exact fun erased => one_approximation_ne_zero c (readPair N positive n).2
      (CountedCayleyIncrement.actual_residual_successor_ne_zero observation nontrivial half depth ordinal N positive n)
      (actual.symm.trans erased)

end CP808Independent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision

#eval IO.println "CP808_CONTROL + both_paid_residual_slots_and_exact_inverse"
#eval IO.println "CP808_CONTROL + finite_recovery_error_uses_paid_residual_and_transports_defect"
#eval IO.println "CP808_CONTROL + actual_paired_child_preserves_old_field_effect_and_steps"
#eval IO.println "CP808_CONTROL + exact_finite_positive_clock_fourier"
#eval IO.println "CP808_CONTROL + actual_diagonal_graph_and_independent_K"
#eval IO.println "CP808_CONTROL + recovery_and_original_ledger_consumers"
#eval IO.println "CP808_CONTROL - actual_zero_entrance_defect_excludes_exact_graph_preimage"
#eval IO.println "CP808_CONTROL - zero_inverse_rounds_erase_both_slots_and_one_retains_the_successor"
#eval IO.println "CP808_GATE_PASS positive=6 negative=2"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
