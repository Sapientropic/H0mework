import H0mework.Versions.Rac9f88e1.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCayleyResidual

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 150000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyIncrement

open BurnolPhysicalState RootInquiryCompletion Filter SourceOperationEffects SourceOperationExecution
open OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial
open RootGeneratedDebtActivationJointSource.OwnerFree
open scoped InnerProductSpace Topology

open private literal_R from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedVelocity

local notation "physical" => OriginalKCombPhysicalAction.physicalProjection
local notation "Resolvent" => burnolDirectRightResolventCLM

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "K" => (burnolCompletedMellinRieszVector coord : BurnolL2)
local notation "point" "[" j "]" => D.raw observation nontrivial half depth j
local notation "values" => residualRead observation nontrivial half depth ordinal
local notation "changeBy" => increment observation nontrivial half depth ordinal

/-- The independent original Riesz pairing reads the change from the physical component of the actual relation. -/
theorem actual_K_increment (N : Nat) (positive : 0 < N) :
    Tendsto (fun n => inner ℂ K (physical (values N positive n 1))) atTop
      (𝓝 (inner ℂ ((Resolvent coord).adjoint K) (point[ordinal+1+1]-point[ordinal+1]))) := by
  let readK : BurnolL2 →L[ℂ] ℂ := (innerSL ℂ K).comp physical
  let difference := point[ordinal+1+1+1]-point[ordinal+1+1]
  have response : Tendsto (fun n => values N positive n 1) atTop (𝓝 difference) :=
    (actual_residual_tendsto observation nontrivial half depth ordinal N positive).snd_nhds
  have source : @Eq BurnolL2 difference (Resolvent coord (point[ordinal+1+1]-point[ordinal+1])) := by
    dsimp only [difference]
    have first : @Eq BurnolL2 (point[ordinal+1+1+1]) (Resolvent coord (point[ordinal+1+1])) :=
      literal_R observation nontrivial half depth (ordinal+1+1)
    have second : @Eq BurnolL2 (point[ordinal+1+1]) (Resolvent coord (point[ordinal+1])) :=
      literal_R observation nontrivial half depth (ordinal+1)
    rw [map_sub]
    exact congrArg₂ (· - ·) first second
  have observed := (readK.continuous.tendsto difference).comp response
  have direct : readK difference = inner ℂ ((Resolvent coord).adjoint K) (point[ordinal+1+1]-point[ordinal+1]) := by
    change inner ℂ K (physical difference) = _
    rw [source]
    exact (Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
      (burnolCompletedMellinRieszVector coord) (Resolvent coord (point[ordinal+1+1]-point[ordinal+1]))).trans
      (ContinuousLinearMap.adjoint_inner_left (Resolvent coord) (point[ordinal+1+1]-point[ordinal+1]) K).symm
  rwa [direct] at observed

private theorem actual_outputs_distinct :
    @Ne BurnolL2 (point[ordinal+1+1+1]) (point[ordinal+1+1]) := by
  let j := ordinal+1+1
  let old := canonicalRaw observation half j 0
  let born := canonicalRaw observation half (j+1) 0
  have phase : born = -2*old/(coord).value := by
    change rawIterate coord seedRaw (sourceIndex observation (j+1)) 0 =
      -2*rawIterate coord seedRaw (sourceIndex observation j) 0/(coord).value
    rw [show sourceIndex observation (j+1) = sourceIndex observation j+1 by unfold sourceIndex; omega]
    exact raw_iterate_mean_update coord seedRaw _
  have live : old ≠ 0 := canonical_source_mean_ne observation half j
  have parameter : (coord).value ≠ 0 := by
    intro zero
    have half := (coord).rightHalf
    rw [zero] at half
    norm_num at half
  intro same
  have projected : born • intervalConstant (1/4) = old • intervalConstant (1/4) := by
    have left := actual_raw_quarter observation nontrivial half depth (j+1)
    have right := actual_raw_quarter observation nontrivial half depth j
    exact left.symm.trans ((congrArg burnolQuarterRestriction same).trans right)
  have flat : born = old := by
    apply sub_eq_zero.mp
    have erased : (born-old) • intervalConstant (1/4) = 0 := by
      rw [sub_smul, projected, sub_self]
    exact (smul_eq_zero.mp erased).resolve_right (intervalConstant_ne_zero (by norm_num))
  have relation := (eq_div_iff parameter).mp (flat.symm.trans phase)
  have impossible : ((coord).value+2)*old = 0 := by linear_combination relation
  have value : (coord).value+2 = 0 := (mul_eq_zero.mp impossible).resolve_right live
  have contradiction := congrArg Complex.re value
  have impossible : (coord).value.re+2 = 0 := by
    norm_num [Complex.add_re] at contradiction ⊢
    exact contradiction
  linarith [(coord).rightHalf]

/-- The same paid residual contains a live successor difference even for a zero-round entrance. -/
theorem actual_residual_successor_ne_zero (N : Nat) (positive : 0 < N) (n : Nat) :
    values N positive n 1 ≠ 0 := by
  have paid := congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2)
    (actual_residual observation nontrivial half depth ordinal N positive n)
  have born := congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2)
    (CountedCayleyWriteback.finite_source observation nontrivial half depth (ordinal+1) N positive n)
  have old := congrArg (Prod.snd : BurnolL2 × BurnolL2 → BurnolL2)
    (CountedCayleyWriteback.finite_source observation nontrivial half depth ordinal N positive n)
  have actual : values N positive n 1 = point[ordinal+1+1+1]-point[ordinal+1+1] :=
    paid.trans (congrArg₂ (· - ·) born old)
  rw [actual]
  exact sub_ne_zero.mpr (actual_outputs_distinct observation nontrivial half depth ordinal)

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_update_consumed"

theorem actual_update_consumed (N : Nat) (positive : 0 < N) (n : Nat) :
    type_of% (actual_residual observation nontrivial half depth ordinal N positive n) ∧
    type_of% (actual_resolvent_effect observation nontrivial half depth ordinal N positive n) ∧
    type_of% (actual_K_increment observation nontrivial half depth ordinal N positive) ∧
    type_of% (actual_residual_successor_ne_zero observation nontrivial half depth ordinal N positive n) ∧
    type_of% (installed_counted_recover observation nontrivial half depth ordinal N positive n) ∧
    type_of% (CountedCayleyRelations.terminal_boundary_effect observation nontrivial half depth ordinal N positive n
      (changeBy N positive n)) ∧
    type_of% (CountedCayleyWriteback.actual_entrance_writeback observation nontrivial half depth ordinal N positive n
      (changeBy N positive n)) :=
  ⟨actual_residual observation nontrivial half depth ordinal N positive n,
    actual_resolvent_effect observation nontrivial half depth ordinal N positive n,
    actual_K_increment observation nontrivial half depth ordinal N positive,
    actual_residual_successor_ne_zero observation nontrivial half depth ordinal N positive n,
    installed_counted_recover observation nontrivial half depth ordinal N positive n,
    CountedCayleyRelations.terminal_boundary_effect observation nontrivial half depth ordinal N positive n
      (changeBy N positive n),
    CountedCayleyWriteback.actual_entrance_writeback observation nontrivial half depth ordinal N positive n
      (changeBy N positive n)⟩

end CountedCayleyIncrement
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
