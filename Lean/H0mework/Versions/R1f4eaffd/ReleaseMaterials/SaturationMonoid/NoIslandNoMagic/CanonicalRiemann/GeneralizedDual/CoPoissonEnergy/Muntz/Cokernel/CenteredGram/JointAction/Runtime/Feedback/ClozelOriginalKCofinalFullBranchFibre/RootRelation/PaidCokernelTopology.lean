import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.GenericFoundation.Cofinal.Topology.CokernelTorsion
import H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage

-- These dependent theorems are consumed by name.
run_cmd Lean.modifyEnv fun env =>
  let env := Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_cokernel_transition"
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_ambient_stage_zero"

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.RootRelation

open BurnolPhysicalState SourceOperationScalarInventoryLift SourceGeneratedPrimePowerCompletion

attribute [local instance] relationGroups

open private paidEvaluation divide_at_grade from
  H0mework.Versions.R1f4eaffd.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.RootRelation.PaidCoverage

private theorem int_smul_injective_at_grade (denominator : ℤ) (nonzero : denominator ≠ 0)
    (grade : Nat) : Function.Injective (fun value : L.Value (PairValue C.Value) grade () =>
      denominator • value) := by
  induction grade with
  | zero =>
    intro left right equal
    change BurnolL2 × BurnolL2 at left right
    change denominator • left = denominator • right at equal
    have scalarNonzero : (denominator : ℂ) ≠ 0 := Int.cast_ne_zero.mpr nonzero
    have scaled : (denominator : ℂ) • left = (denominator : ℂ) • right :=
      (Int.cast_smul_eq_zsmul ℂ denominator left).trans
        (equal.trans (Int.cast_smul_eq_zsmul ℂ denominator right).symm)
    have cancel := congrArg (fun value : BurnolL2 × BurnolL2 => ((denominator : ℂ)⁻¹) • value) scaled
    change (left : BurnolL2 × BurnolL2) = right
    simpa only [smul_smul, inv_mul_cancel₀ scalarNonzero, one_smul] using cancel
  | succ grade previous =>
    intro left right equal
    change (denominator • left : L.Value (PairValue C.Value) grade () × L.Value (PairValue C.Value) grade ()) =
      denominator • right at equal
    exact Prod.ext (previous (congrArg Prod.fst equal)) (previous (congrArg Prod.snd equal))

private theorem ambient_power_bijective (grade : Nat) (p : Nat.Primes) (j : Nat) :
    Function.Bijective (powerMultiplication (L := PairValue (L.Value (PairValue C.Value) grade) ()) p j) := by
  let denominator := (p.1 : ℤ)^(j+1)
  have primeNonzero : (p.1 : ℤ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have nonzero : denominator ≠ 0 := pow_ne_zero _ primeNonzero
  have divide := divide_at_grade denominator nonzero grade
  have unique := int_smul_injective_at_grade denominator nonzero grade
  change Function.Bijective (fun value : PairValue (L.Value (PairValue C.Value) grade) () => denominator • value)
  refine ⟨?_, ?_⟩
  · intro left right equal
    exact Prod.ext (unique (congrArg Prod.fst equal)) (unique (congrArg Prod.snd equal))
  · intro value
    obtain ⟨left, paidLeft⟩ := divide value.1
    obtain ⟨right, paidRight⟩ := divide value.2
    exact ⟨(left, right), Prod.ext paidLeft paidRight⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

/-- The literal source stage is read in the original evaluator's coverage cokernel. -/
def actualPaidCokernelStage (ordinal : Nat) (p : Nat.Primes) (j : Nat) :=
  stageCokernelEquiv (paidEvaluation observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal) p j
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p j)

theorem actual_paid_cokernel_transition (ordinal : Nat) (p : Nat.Primes) (j : Nat)
    (value : StageResidual (L := SourceCompletion observation nontrivial half depth ordinal) p (j+1)) :
    (actualPaidCokernelStage observation nontrivial half depth ordinal p j (transition p j value)).val =
      (p.1 : ℤ) • (actualPaidCokernelStage observation nontrivial half depth ordinal p (j+1) value).val :=
  stage_cokernel_transition (paidEvaluation observation nontrivial half depth ordinal)
    (actual_paid_evaluation_injective observation nontrivial half depth ordinal) p j
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p j)
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p (j+1)) value

private theorem stage_zero_of_power_surjective {A : Type} [AddCommGroup A]
    (p : Nat.Primes) (j : Nat) (surjective : Function.Surjective (powerMultiplication (L := A) p j))
    (value : A) : stageProjection p j value = 0 :=
  (stageProjection_eq_zero_iff p j value).mpr (surjective value)

theorem actual_paid_ambient_stage_zero (ordinal : Nat) (p : Nat.Primes) (j : Nat)
    (word : SourceCompletion observation nontrivial half depth ordinal) :
    stageProjection p j (paidEvaluation observation nontrivial half depth ordinal word) = 0 :=
  stage_zero_of_power_surjective p j
    (ambient_power_bijective (D.packet observation nontrivial half depth ordinal).1 p j).2
    (paidEvaluation observation nontrivial half depth ordinal word)

end OriginalKCofinalFullBranchFibre.RootRelation
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
