import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelTopology

-- These dependent theorems are consumed by name.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cokernel_to_model"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cokernel_model_next"

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift
open SourceGeneratedPrimePowerCompletion CofinalAllPrimeTopology

attribute [local instance] relationGroups

open private paidEvaluation from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage
open private ambient_power_bijective from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCokernelTopology

private def cokernelMap {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    (evaluate : A →ₗ[ℤ] B) (evaluateNext : C →ₗ[ℤ] D)
    (source : A →ₗ[ℤ] C) (target : B →ₗ[ℤ] D)
    (actual : ∀ word, target (evaluate word) = evaluateNext (source word)) :
    (B ⧸ LinearMap.range evaluate) →ₗ[ℤ] (D ⧸ LinearMap.range evaluateNext) :=
  (LinearMap.range evaluate).mapQ (LinearMap.range evaluateNext) target (by
    rintro _ ⟨word, rfl⟩
    exact ⟨source word, (actual word).symm⟩)

private theorem stage_cokernel_map {A B C D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [AddCommGroup D]
    (evaluate : A →ₗ[ℤ] B) (evaluateNext : C →ₗ[ℤ] D)
    (injective : Function.Injective evaluate) (injectiveNext : Function.Injective evaluateNext)
    (source : A →ₗ[ℤ] C) (target : B →ₗ[ℤ] D)
    (actual : ∀ word, target (evaluate word) = evaluateNext (source word))
    (p : Nat.Primes) (j : Nat)
    (ambient : Function.Bijective (powerMultiplication (L := B) p j))
    (ambientNext : Function.Bijective (powerMultiplication (L := D) p j))
    (value : StageResidual (L := A) p j) :
    cokernelMap evaluate evaluateNext source target actual
      (stageCokernelEquiv evaluate injective p j ambient value).val =
      (stageCokernelEquiv evaluateNext injectiveNext p j ambientNext (stageMap p j source value)).val := by
  obtain ⟨word, rfl⟩ := (powerRange (L := A) p j).mkQ_surjective value
  obtain ⟨divided, paid⟩ := ambient.2 (evaluate word)
  have moved : powerMultiplication p j (target divided) = evaluateNext (source word) :=
    ((map_smul target ((p.1 : ℤ)^(j+1)) divided).symm.trans (congrArg target paid)).trans (actual word)
  have oldRead := stage_cokernel_of_divided evaluate injective p j ambient word divided paid
  have newRead := stage_cokernel_of_divided evaluateNext injectiveNext p j ambientNext (source word)
    (target divided) moved
  have sourceRead := stage_successor_apply p j source word
  let read := cokernelMap evaluate evaluateNext source target actual
  let next := stageCokernelEquiv evaluateNext injectiveNext p j ambientNext
  exact (congrArg read oldRead).trans
    (newRead.symm.trans (congrArg (fun stage => (next stage).val) sourceRead.symm))

private theorem complex_power_bijective {A : Type} [AddCommGroup A] [Module ℂ A]
    (p : Nat.Primes) (j : Nat) : Function.Bijective (powerMultiplication (L := A) p j) := by
  let denominator := (p.1 : ℤ)^(j+1)
  have primeNonzero : (p.1 : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have nonzero : (denominator : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (pow_ne_zero _ primeNonzero)
  change Function.Bijective (fun value : A => denominator • value)
  refine ⟨?_, ?_⟩
  · intro left right equal
    change denominator • left = denominator • right at equal
    have scaled : (denominator : ℂ) • left = (denominator : ℂ) • right :=
      (Int.cast_smul_eq_zsmul ℂ denominator left).trans
        (equal.trans (Int.cast_smul_eq_zsmul ℂ denominator right).symm)
    have cancel := congrArg (fun value : A => ((denominator : ℂ)⁻¹) • value) scaled
    simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul] using cancel
  · intro value
    refine ⟨((denominator : ℂ)⁻¹) • value, ?_⟩
    change denominator • (((denominator : ℂ)⁻¹) • value) = value
    rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul, mul_inv_cancel₀ nonzero, one_smul]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

private def evaluationToModel (grade : Nat) :=
  ((H.projection (sourceStep observation nontrivial half)
    (sourceBranches observation nontrivial half)).restrictScalars ℤ).comp
    (((branchReadback observation nontrivial half).restrictScalars ℤ).comp (collapseLinear grade))

def actualPaidCokernelToModel (ordinal : Nat) :=
  cokernelMap (paidEvaluation observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth ordinal) LinearMap.id
    (evaluationToModel observation nontrivial half (D.packet observation nontrivial half depth ordinal).1)
    (fun _ => rfl)

def actualPaidModelCokernelStage (ordinal : Nat) (p : Nat.Primes) (j : Nat) :=
  stageCokernelEquiv (factor observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth ordinal) p j (complex_power_bijective p j)

private theorem stage_map_identity_apply {A : Type} [AddCommGroup A]
    (p : Nat.Primes) (j : Nat) (value : StageResidual (L := A) p j) :
    stageMap p j LinearMap.id value = value := LinearMap.congr_fun (stageMap_id p j) value

theorem actual_paid_cokernel_to_model (ordinal : Nat) (p : Nat.Primes) (j : Nat)
    (value : StageResidual (L := SourceCompletion observation nontrivial half depth ordinal) p j) :
    actualPaidCokernelToModel observation nontrivial half depth ordinal
      (actualPaidCokernelStage observation nontrivial half depth ordinal p j value).val =
      (actualPaidModelCokernelStage observation nontrivial half depth ordinal p j value).val := by
  let project := evaluationToModel observation nontrivial half (D.packet observation nontrivial half depth ordinal).1
  let read := actualPaidModelCokernelStage observation nontrivial half depth ordinal p j
  have mapped := stage_cokernel_map (paidEvaluation observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth ordinal) LinearMap.id project
    (fun _ => rfl) p j (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p j)
    (complex_power_bijective p j) value
  exact mapped.trans (congrArg (fun stage => (read stage).val) (stage_map_identity_apply p j value))

private def modelCharge (ordinal : Nat) :=
  (actualPaidCompletion observation nontrivial half depth (ordinal+1)).symm.toLinearMap.comp
    (actualPaidCompletion observation nontrivial half depth ordinal).toLinearMap

private def modelAction :=
  (H.modelAction (sourceStep observation nontrivial half) (sourceBranches observation nontrivial half)).restrictScalars ℤ

private theorem actual_model_square (ordinal : Nat) (word : SourceCompletion observation nontrivial half depth ordinal) :
    modelAction observation nontrivial half (factor observation nontrivial half depth ordinal word) =
      factor observation nontrivial half depth (ordinal+1)
        (modelCharge observation nontrivial half depth ordinal word) := by
  let coordinate := actualPaidCompletion observation nontrivial half depth ordinal
  have arrived := actual_paid_model_next observation nontrivial half depth ordinal (coordinate word)
  exact (congrArg (fun source =>
    modelAction observation nontrivial half (factor observation nontrivial half depth ordinal source))
    (coordinate.symm_apply_apply word).symm).trans arrived

/-- The native model action descends to the two literal adjacent cokernels. -/
def actualPaidModelCokernelNext (ordinal : Nat) :=
  cokernelMap (factor observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth (ordinal+1))
    (modelCharge observation nontrivial half depth ordinal) (modelAction observation nontrivial half)
    (actual_model_square observation nontrivial half depth ordinal)

/-- The source cokernel torsion is consumed by the actual model at the next ordinal. -/
theorem actual_paid_cokernel_model_next (ordinal : Nat) (p : Nat.Primes) (j : Nat) (coefficient : ℤ) :
    let old := (actualPaidCompletion observation nontrivial half depth ordinal).symm coefficient
    let new := (actualPaidCompletion observation nontrivial half depth (ordinal+1)).symm coefficient
    actualPaidModelCokernelNext observation nontrivial half depth ordinal
      (actualPaidCokernelToModel observation nontrivial half depth ordinal
        (actualPaidCokernelStage observation nontrivial half depth ordinal p j (stageProjection p j old)).val) =
      (actualPaidModelCokernelStage observation nontrivial half depth (ordinal+1) p j (stageProjection p j new)).val := by
  let current := actualPaidCompletion observation nontrivial half depth ordinal
  let next := actualPaidCompletion observation nontrivial half depth (ordinal+1)
  let old := current.symm coefficient
  let read := actualPaidModelCokernelStage observation nontrivial half depth (ordinal+1) p j
  have source : modelCharge observation nontrivial half depth ordinal old = next.symm coefficient :=
    congrArg next.symm (current.apply_symm_apply coefficient)
  have sameStage :=
    (stage_successor_apply p j (modelCharge observation nontrivial half depth ordinal) old).trans
      (congrArg (stageProjection p j) source)
  have mapped := stage_cokernel_map (factor observation nontrivial half depth ordinal)
    (factor observation nontrivial half depth (ordinal+1))
    (actual_paid_factor_injective observation nontrivial half depth ordinal)
    (actual_paid_factor_injective observation nontrivial half depth (ordinal+1))
    (modelCharge observation nontrivial half depth ordinal) (modelAction observation nontrivial half)
    (actual_model_square observation nontrivial half depth ordinal) p j
    (complex_power_bijective p j) (complex_power_bijective p j) (stageProjection p j old)
  exact (congrArg (actualPaidModelCokernelNext observation nontrivial half depth ordinal)
    (actual_paid_cokernel_to_model observation nontrivial half depth ordinal p j (stageProjection p j old))).trans
      (mapped.trans (congrArg (fun stage => (read stage).val) sameStage))

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
