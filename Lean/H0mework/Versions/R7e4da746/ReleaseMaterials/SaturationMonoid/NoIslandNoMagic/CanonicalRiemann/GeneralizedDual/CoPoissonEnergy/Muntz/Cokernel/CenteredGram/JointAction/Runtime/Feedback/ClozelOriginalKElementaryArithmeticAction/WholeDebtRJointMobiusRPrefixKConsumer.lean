import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.WholeDebtRJointMobiusRPrefixSource

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalWholeDebtRJointMobiusRPrefixKConsumer
open Complex MeasureTheory Set Filter BurnolPhysicalState OriginalRieszSource
open OriginalKCrossParameterRAdjointSource
open scoped Topology InnerProductSpace
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "coordinate" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "input" => OriginalWholeDebtRJointMobiusRActionSource.sourceInput observation nontrivial half
local notation "next" => OriginalWholeDebtRJointMobiusRActionSource.sourceNext observation nontrivial half
local notation "raw" => OriginalWholeDebtRJointMobiusRPrefixSource.nextRaw observation nontrivial half
local notation "K" => (burnolCompletedMellinRieszVector coordinate : BurnolL2)
local notation "F" => fourierL2
local notation "P" => burnolEvenAmbientProjection

/-- The zero-end counterterm and prefix are paired as one actual L² object. -/
theorem actual_K_prefix_integrable : Integrable (fun x : ℝ => inner ℂ (K x) (raw x)) volume := by
  exact (L2.integrable_inner (𝕜 := ℂ) K next).congr
    ((OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_raw observation nontrivial half).mono
      (fun x same => congrArg (inner ℂ (K x)) same))

theorem actual_K_prefix_price : inner ℂ K next = ∫ x : ℝ, inner ℂ (K x) (raw x) := by
  rw [L2.inner_def]
  exact integral_congr_ae ((OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_raw observation nontrivial half).mono
    (fun x same => congrArg (inner ℂ (K x)) same))

/-- The physical projection preserves this original K price by the paid true Riesz face. -/
theorem actual_physical_K_prefix_price :
    inner ℂ K (P next : BurnolL2) = ∫ x : ℝ, inner ℂ (K x) (raw x) := by
  have projection := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (burnolCompletedMellinRieszVector coordinate) next
  exact projection.trans (actual_K_prefix_price observation nontrivial half)

/-- The existing full original B adjoint field independently consumes the complete generated prefix. -/
theorem actual_K_adjoint_consumer :
    (∫ x : ℝ, inner ℂ (K x) (raw x)) = inner ℂ (sourceAdjointK coordinate) (input : BurnolL2) := by
  rw [← actual_K_prefix_price observation nontrivial half]
  exact (original_R_adjoint_reads coordinate input).1

theorem actual_FK_adjoint_consumer :
    Integrable (fun x : ℝ => inner ℂ (F K x) (raw x)) volume ∧
      (∫ x : ℝ, inner ℂ (F K x) (raw x)) = inner ℂ (sourceAdjointFK coordinate) (input : BurnolL2) := by
  have source := OriginalWholeDebtRJointMobiusRPrefixSource.actual_next_raw observation nontrivial half
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) (F K) next).congr
    (source.mono (fun x same => congrArg (inner ℂ (F K x)) same)), ?_⟩
  calc
    _ = inner ℂ (F K) next := by
      rw [L2.inner_def]
      exact integral_congr_ae (source.symm.mono (fun x same => congrArg (inner ℂ (F K x)) same))
    _ = _ := (original_R_adjoint_reads coordinate input).2

/-- Position-gap generation does not admit this next to the physical face or an old cofinal occurrence. -/
theorem actual_next_not_physical : next ∉ evenBurnolClosedFace (1 / 4 : ℝ) := by
  intro membership
  apply OriginalWholeDebtRJointMobiusStrictSource.actual_effect_ne_zero observation nontrivial half
  exact Submodule.starProjection_orthogonal_apply_eq_zero membership

end OriginalWholeDebtRJointMobiusRPrefixKConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
