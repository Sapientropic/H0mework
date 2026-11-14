import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Spectrum
import H0mework.Versions.Re60a8605.ReleaseMaterials.SaturationMonoid.FiniteCNF.Joint
import H0mework.Realization.Operations.FiniteKernel
import Mathlib.Algebra.Algebra.Tower

/-!
# Original CNF multiplication action, finite observation, and joint mass

The explicit integer-energy polynomial annihilates multiplication by the
original violation count. Its monic coefficients generate the existing finite
observation recurrence with exactly `m + 1` coordinates. The zero projector's
actual uniform-source mass agrees with the clause-joint program and with the
existing effective coefficient. These are source identities, not running-time
bounds for generating the observation coordinates.
-/

namespace SaturationMonoid.ComplexityProjection.SATSource

open Polynomial
open scoped BigOperators

noncomputable section

abbrev Source (n : Nat) := Assignment n → ℚ

/-- Multiplication by the original CNF violation count on the full assignment source. -/
def hamiltonian {n : Nat} (formula : CNFFormula n) : Module.End ℚ (Source n) :=
  Algebra.lsmul ℚ ℚ (Source n) fun assignment =>
    (violationCount formula assignment : ℚ)

@[simp] theorem hamiltonian_apply {n : Nat} (formula : CNFFormula n)
    (source : Source n) (assignment : Assignment n) :
    hamiltonian formula source assignment =
      (violationCount formula assignment : ℚ) * source assignment := rfl

theorem hamiltonian_pow_apply {n : Nat} (formula : CNFFormula n)
    (k : Nat) (source : Source n) (assignment : Assignment n) :
    (hamiltonian formula ^ k) source assignment =
      (violationCount formula assignment : ℚ) ^ k * source assignment := by
  rw [hamiltonian, ← map_pow]
  rfl

/-- Algebra evaluation is the pointwise polynomial on the actual source energies. -/
theorem aeval_hamiltonian_apply {n : Nat} (formula : CNFFormula n)
    (p : Polynomial ℚ) (source : Source n) (assignment : Assignment n) :
    aeval (hamiltonian formula) p source assignment =
      p.eval (violationCount formula assignment : ℚ) * source assignment := by
  rw [hamiltonian, aeval_algHom_apply]
  change (aeval (fun x => (violationCount formula x : ℚ)) p) assignment *
    source assignment = _
  simp only [aeval_fn_apply, coe_aeval_eq_eval]

/-- The known energy window gives an operator relation on the complete source. -/
theorem annihilator_hamiltonian {n : Nat} (formula : CNFFormula n) :
    aeval (hamiltonian formula) (annihilator formula.length) = 0 := by
  apply LinearMap.ext
  intro source
  funext assignment
  rw [aeval_hamiltonian_apply, annihilator_eval_violationCount]
  simp

def zeroProjector {n : Nat} (formula : CNFFormula n) : Module.End ℚ (Source n) :=
  aeval (hamiltonian formula) (zeroFilter formula.length)

/-- The actual projector retains exactly the assignments satisfying the original CNF. -/
theorem zeroProjector_apply {n : Nat} (formula : CNFFormula n)
    (source : Source n) (assignment : Assignment n) :
    zeroProjector formula source assignment =
      if CNFFormula.eval formula (extendAssignment assignment) = true
      then source assignment else 0 := by
  rw [zeroProjector, aeval_hamiltonian_apply, zeroFilter_eval_violationCount]
  split_ifs <;> simp

theorem zeroProjector_idempotent {n : Nat} (formula : CNFFormula n) :
    zeroProjector formula * zeroProjector formula = zeroProjector formula := by
  apply LinearMap.ext
  intro source
  funext assignment
  change zeroProjector formula (zeroProjector formula source) assignment = _
  simp only [zeroProjector_apply]
  split_ifs <;> rfl

theorem annihilator_monic (m : Nat) : (annihilator m).Monic :=
  monic_prod_of_monic _ _ fun r _ => monic_X_sub_C (r : ℚ)

theorem annihilator_natDegree (m : Nat) : (annihilator m).natDegree = m + 1 := by
  rw [annihilator, natDegree_prod_of_monic _ _ fun (r : Nat) _ => monic_X_sub_C (r : ℚ)]
  simp only [natDegree_X_sub_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- The recurrence coefficients are generated from the explicit monic relation. -/
def recurrenceCoefficients {n : Nat} (formula : CNFFormula n) :
    Fin (formula.length + 1) → ℚ :=
  fun index => -(annihilator formula.length).coeff index.val

theorem hamiltonian_power_generated {n : Nat} (formula : CNFFormula n) :
    hamiltonian formula ^ (formula.length + 1) =
      ∑ index : Fin (formula.length + 1),
        recurrenceCoefficients formula index • (hamiltonian formula ^ index.val) := by
  have generated := congrArg (aeval (hamiltonian formula))
    (annihilator_monic formula.length).as_sum
  rw [annihilator_hamiltonian, annihilator_natDegree] at generated
  simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at generated
  have leading := eq_neg_of_add_eq_zero_left generated.symm
  have reindex := Fin.sum_univ_eq_sum_range
    (fun index => -((annihilator formula.length).coeff index) •
      (hamiltonian formula ^ index)) (formula.length + 1)
  apply (show hamiltonian formula ^ (formula.length + 1) =
      ∑ index ∈ Finset.range (formula.length + 1),
        -((annihilator formula.length).coeff index) • (hamiltonian formula ^ index) from
    by
      rw [← Finset.sum_neg_distrib] at leading
      simpa only [← _root_.neg_smul] using leading).trans
  exact reindex.symm

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedActionObservationHistory

theorem hamiltonian_observation_law {n : Nat} (formula : CNFFormula n)
    {B : Type} [AddCommGroup B] [Module ℚ B] (observation : Source n →ₗ[ℚ] B) :
    observation.comp (hamiltonian formula ^ (formula.length + 1)) =
      ∑ index : Fin (formula.length + 1), recurrenceCoefficients formula index •
        stageEvaluator (hamiltonian formula) observation index.val := by
  rw [hamiltonian_power_generated]
  ext source
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.smul_apply, map_smul]
  apply Finset.sum_congr rfl
  intro index _
  rfl

/-- Every linear observation of the original source has the explicit `m + 1` window. -/
theorem finite_prefix_iff_model {n : Nat} (formula : CNFFormula n)
    {B : Type} [AddCommGroup B] [Module ℚ B] (observation : Source n →ₗ[ℚ] B)
    (left right : Source n) :
    prefixEvaluator (hamiltonian formula) observation formula.length left =
        prefixEvaluator (hamiltonian formula) observation formula.length right ↔
      projection (hamiltonian formula) observation left =
        projection (hamiltonian formula) observation right :=
  FiniteRecurrence.prefix_fibre_iff_model (hamiltonian formula) observation
    formula.length (recurrenceCoefficients formula)
    (hamiltonian_observation_law formula observation) left right

/-- The unchanged counting source assigns weight one to every original assignment. -/
def uniformSeed (n : Nat) : Source n := fun _ => 1

def sourceMass (n : Nat) : Source n →ₗ[ℚ] ℚ :=
  ∑ assignment : Assignment n, LinearMap.proj assignment

theorem sourceMass_apply {n : Nat} (source : Source n) :
    sourceMass n source = ∑ assignment : Assignment n, source assignment := by
  simp only [sourceMass, LinearMap.sum_apply, LinearMap.proj_apply]

def sourceMoment {n : Nat} (formula : CNFFormula n) (k : Nat) : ℚ :=
  sourceMass n ((hamiltonian formula ^ k) (uniformSeed n))

theorem sourceMoment_eq_sum {n : Nat} (formula : CNFFormula n) (k : Nat) :
    sourceMoment formula k =
      ∑ assignment : Assignment n, (violationCount formula assignment : ℚ) ^ k := by
  simp only [sourceMoment, sourceMass_apply, hamiltonian_pow_apply, uniformSeed, mul_one]

theorem sourceMass_polynomial {n : Nat} (formula : CNFFormula n) (p : Polynomial ℚ) :
    sourceMass n (aeval (hamiltonian formula) p (uniformSeed n)) =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * sourceMoment formula k := by
  rw [aeval_eq_sum_range]
  simp only [LinearMap.sum_apply, map_sum, LinearMap.smul_apply, map_smul,
    smul_eq_mul, sourceMoment]

open SourceGeneratedFiniteEffectiveCoefficient

/-- The original zero coefficient is the actual projected source mass. -/
theorem sourceMass_zeroProjector_eq_coefficient {n : Nat} (formula : CNFFormula n) :
    sourceMass n (zeroProjector formula (uniformSeed n)) =
      (effectiveCoefficient (violationCount formula) 0 : ℚ) := by
  rw [sourceMass_apply]
  simp only [zeroProjector_apply, uniformSeed, Finset.sum_boole,
    effectiveCoefficient_eq_card_filter, violationCount_eq_zero_iff_eval]

/-- The executable shared clause-joint program reads the mass of the same projector. -/
theorem sharedReadout_eq_projected_mass {n : Nat} (formula : CNFFormula n) :
    (SATJoint.sharedReadout formula : ℚ) =
      sourceMass n (zeroProjector formula (uniformSeed n)) := by
  rw [SATJoint.sharedReadout_eq_count, sourceMass_zeroProjector_eq_coefficient,
    effectiveCoefficient_eq_card_filter]
  simp only [Int.cast_natCast, violationCount_eq_zero_iff_eval]
  rfl

/-- The source moments combine to the scalar generated by the executable joint program. -/
theorem sharedReadout_eq_moment_combination {n : Nat} (formula : CNFFormula n) :
    (SATJoint.sharedReadout formula : ℚ) =
      ∑ k ∈ Finset.range ((zeroFilter formula.length).natDegree + 1),
        (zeroFilter formula.length).coeff k * sourceMoment formula k := by
  rw [sharedReadout_eq_projected_mass, zeroProjector, sourceMass_polynomial]

end
end SaturationMonoid.ComplexityProjection.SATSource
