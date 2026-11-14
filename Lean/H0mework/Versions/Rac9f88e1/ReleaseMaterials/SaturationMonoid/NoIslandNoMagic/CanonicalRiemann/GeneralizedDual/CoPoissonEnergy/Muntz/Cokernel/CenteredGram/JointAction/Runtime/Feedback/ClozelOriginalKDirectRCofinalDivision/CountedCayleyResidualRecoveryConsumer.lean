import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyResidualRecovery

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 180000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyResidualRecovery

open BurnolPhysicalState Filter RootInquiryCompletion
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open CountedCayleyResidualInverse (approximate approximate_error approximate_succ data defect approximate_defect)
open CountedCayleyResidualInverse.Geom (retention retention_pos retention_lt_one clock driveScale finite finite_zero finite_succ)
open scoped InnerProductSpace Topology

open private literal_R from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity
open private slotRead slotRead_tendsto slots Riesz_read from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocityReceipt

local notation "Resolvent" => burnolDirectRightResolventCLM
local notation "d" => sourceDamping
local notation "F" => fourierL2
local notation "FieldOp" => BurnolL2 →L[ℂ] BurnolL2

def waveResolvent (c : BurnolCompletedMellinCoordinate) : FieldOp :=
  (F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((Resolvent c).comp (F).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem wave_resolvent_source (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    waveResolvent c x = FiniteMobiusResolventFlux.Rplus (c.value/2) x := by
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  change F (burnolDirectRightResolvent (c.value/2) ((F).symm x)) = _
  rw [FiniteMobiusResolventFlux.fourier_R _ right, (F).apply_symm_apply]

theorem approximate_wave (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) (m : Nat) :
    F (approximate c m x) = finite (waveResolvent c) (d c) m (F x) := by
  have intertwines (field : BurnolL2) :
      F (clock (Resolvent c) (d c) field) = clock (waveResolvent c) (d c) (F field) := by
    change F ((retention (d c) : ℂ) • (field+(d c : ℂ) • Resolvent c field)) =
      (retention (d c) : ℂ) • (F field+(d c : ℂ) • F (Resolvent c ((F).symm (F field))))
    rw [(F).symm_apply_apply, map_smul, map_add, map_smul]
  induction m with
  | zero => simp only [approximate, finite_zero, zero_apply, map_zero]
  | succ m previous =>
    have next := congrArg (fun op : FieldOp => op (F x)) (finite_succ (waveResolvent c) (d c) m)
    change finite (waveResolvent c) (d c) (m+1) (F x) =
      clock (waveResolvent c) (d c) (finite (waveResolvent c) (d c) m (F x)) + driveScale (d c) • F x at next
    rw [approximate_succ, map_add, map_smul, intertwines, previous, next]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "K" => (burnolCompletedMellinRieszVector c : BurnolL2)
local notation "oldField" => D.raw observation nontrivial half depth (ordinal+1)
local notation "newField" => D.raw observation nontrivial half depth (ordinal+1+1)
local notation "out" => CountedCayleyProgramme.output observation nontrivial half depth ordinal
local notation "input" => data observation nontrivial half depth ordinal
local notation "completed" => terminal observation nontrivial half depth ordinal
local notation "nativeInput" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth

def fields (N : Nat) (positive : 0 < N) (n m : Nat) : BurnolL2 × BurnolL2 :=
  let value := (completed N positive n m).2
  (value 0,value 1)

local notation "fit" => fields observation nontrivial half depth ordinal

theorem fields_source (N : Nat) (positive : 0 < N) (n m : Nat) :
    fit N positive n m = (approximate c m (input N positive n).1,approximate c m (input N positive n).2) :=
  congrArg (fun (value : SourceOperationScalarInventoryLift.PairValue CountedCellHistory.CellValue ()) =>
      (value.2 0,value.2 1)) (terminal_source observation nontrivial half depth ordinal N positive n m)

theorem actual_finite_error (N : Nat) (positive : 0 < N) (n m : Nat) :
    ‖fit N positive n m-out N positive n‖ ≤ retention (d c)^m*‖input N positive n‖ := by
  let actual := input N positive n
  let returned := CountedCayleyResidualInverse.recover c
  have reads : (returned actual.1, returned actual.2) = out N positive n :=
    CountedCayleyResidualInverse.actual_recovered observation nontrivial half depth ordinal N positive n
  rw [fields_source, ← reads, Prod.norm_def]
  apply max_le
  · exact (approximate_error c actual.1 m).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le actual) (pow_nonneg (retention_pos (sourceDamping_pos c)).le _))
  · exact (approximate_error c actual.2 m).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le actual) (pow_nonneg (retention_pos (sourceDamping_pos c)).le _))

theorem actual_wave_fields (N : Nat) (positive : 0 < N) (n m : Nat) :
    (F (fit N positive n m).1,F (fit N positive n m).2) =
      (finite (waveResolvent c) (d c) m (F (input N positive n).1),
        finite (waveResolvent c) (d c) m (F (input N positive n).2)) := by
  rw [fields_source]
  exact Prod.ext (approximate_wave c _ m) (approximate_wave c _ m)

theorem actual_finite_defect (N : Nat) (positive : 0 < N) (n m : Nat) :
    defect c (fit N positive n m) = approximate c m (defect c (input N positive n)) := by
  rw [fields_source, approximate_defect]

/-- The two cutoffs can grow together, with a complete actual field at every finite index. -/
theorem actual_diagonal_fields (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => fit N positive n n) atTop (𝓝 (oldField,newField)) := by
  have source := CountedCayleyIncrement.actual_residual_tendsto observation nontrivial half depth ordinal N positive
  have decay := tendsto_pow_atTop_nhds_zero_of_lt_one (retention_pos (sourceDamping_pos c)).le
    (retention_lt_one (sourceDamping_pos c))
  have price := decay.mul source.norm
  rw [zero_mul] at price
  have error : Tendsto (fun n => fit N positive n n-out N positive n) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => actual_finite_error observation nontrivial half depth ordinal N positive n n) price
  have limit := error.add (CountedCayleyWriteback.actual_entrance observation nontrivial half depth ordinal N positive)
  rw [zero_add] at limit
  exact limit.congr' (Eventually.of_forall fun n => sub_add_cancel _ _)

theorem actual_defect_zero_limit (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => defect c (fit N positive n n)) atTop (𝓝 0) := by
  let full := actual_diagonal_fields observation nontrivial half depth ordinal N positive
  have action : @Eq BurnolL2 newField (Resolvent c oldField) :=
    literal_R observation nontrivial half depth (ordinal+1)
  have next := ((Resolvent c).continuous.tendsto oldField).comp full.fst_nhds
  have gap := full.snd_nhds.sub next
  have zero : @Eq BurnolL2 (newField-Resolvent c oldField) 0 := sub_eq_zero.mpr action
  change Tendsto (fun n => defect c (fit N positive n n)) atTop (𝓝 (newField-Resolvent c oldField)) at gap
  rwa [zero] at gap

theorem actual_independent_K (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => slotRead K (fit N positive n n)) atTop
      (𝓝 (nativeInput (ordinal+1),nativeInput (ordinal+1+1),inner ℂ ((Resolvent c).adjoint K) oldField)) :=
  slotRead_tendsto (actual_diagonal_fields observation nontrivial half depth ordinal N positive)
    (slots observation nontrivial half depth ordinal) (slots observation nontrivial half depth (ordinal+1))
    (Riesz_read observation nontrivial half depth ordinal)

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "consume_actual_recovery"

theorem consume_actual_recovery (N : Nat) (positive : 0 < N) (n m : Nat) :
    type_of% (actual_paid_recovery observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (CountedCayleyIncrement.actual_update_consumed observation nontrivial half depth ordinal N positive n) ∧
    type_of% (actual_finite_error observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (actual_wave_fields observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (actual_finite_defect observation nontrivial half depth ordinal N positive n m) ∧
    type_of% (actual_defect_zero_limit observation nontrivial half depth ordinal N positive) ∧
    type_of% (actual_independent_K observation nontrivial half depth ordinal N positive) :=
  ⟨actual_paid_recovery observation nontrivial half depth ordinal N positive n m,
    CountedCayleyIncrement.actual_update_consumed observation nontrivial half depth ordinal N positive n,
    actual_finite_error observation nontrivial half depth ordinal N positive n m,
    actual_wave_fields observation nontrivial half depth ordinal N positive n m,
    actual_finite_defect observation nontrivial half depth ordinal N positive n m,
    actual_defect_zero_limit observation nontrivial half depth ordinal N positive,
    actual_independent_K observation nontrivial half depth ordinal N positive⟩

end CountedCayleyResidualRecovery
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
