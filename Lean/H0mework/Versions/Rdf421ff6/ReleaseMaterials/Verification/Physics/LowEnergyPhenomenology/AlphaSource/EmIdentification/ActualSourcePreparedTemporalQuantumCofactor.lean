import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedTemporalQuantumWard

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumCofactor
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalCharacteristic
open PreparationVacuumOriginalGreenFeedback ActualEMAction ActualEMDressedSchur ActualEMDressedConstraint
open ActualDressedNullNative ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator ActualDressedZeroDamping
open ActualSourcePreparedTemporalEMConstraint ActualSourcePreparedTemporalQuantumWard
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil

def sourceTemporalQuantumConstraintPolynomial (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (row : Fin 9) : ℂ[X] :=
  dampingSlice epsilon (
    dotProduct (fun i => (MvPolynomial.C (originalNullColumn (-(frequencyRay epsilon 0 n)) row i) : Parameters))
      ((commonNumerator event n)*ᵥ((commonClearedPencil event n).adjugate*ᵥ
        (fun j => MvPolynomial.C (sourceTemporalEMForce j)))))

private theorem positive_clock_polynomial_zero (P : ℂ[X])
    (vanishes : ∀ sigma : ℝ, 0 < sigma → P.eval (sigma : ℂ)=0) : P=0 := by
  let f : Fin (P.natDegree+1) → ℂ := fun k => ((k.val+1 : ℕ) : ℂ)
  have injective : Function.Injective f := by
    intro a b equality
    change ((a.val+1 : ℕ) : ℂ)=((b.val+1 : ℕ) : ℂ) at equality
    apply Fin.ext
    have natural : a.val+1=b.val+1 := by exact_mod_cast equality
    omega
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P injective
  · intro k
    have positive : (0 : ℝ) < ((k.val+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k.val
    simpa only [f, Complex.ofReal_natCast] using vanishes ((k.val+1 : ℕ) : ℝ) positive
  · simp

private theorem cofactor_quantum_cokernel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (J Q : Matrix ι ι ℂ) (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) (d sigma : ℂ) (E : ι → ℂ)
    (nonzero : sigma ≠ 0) (classical : ∀ a, L (J*ᵥa)=0) (compatible : L E=0) :
    L (Q*ᵥ((d • J-sigma • Q).adjugate*ᵥE))=0 := by
  let P := d • J-sigma • Q
  have adj := congrArg (fun A : Matrix ι ι ℂ => A*ᵥE) (Matrix.mul_adjugate P)
  rw [←Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at adj
  have rows := congrArg L adj
  change L ((d • J-sigma • Q)*ᵥ(P.adjugate*ᵥE))=L (P.det • E) at rows
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, map_sub, map_smul, map_smul, map_smul,
    classical, compatible, smul_zero, smul_zero, zero_sub] at rows
  exact (smul_eq_zero.mp (neg_eq_zero.mp rows)).resolve_left nonzero

private theorem eval_constant_full_read (v : Fin 3 → ℂ)
    (Q H : Matrix (Fin 289) (Fin 289) Parameters) (l E : Fin 289 → ℂ) :
    MvPolynomial.eval v (dotProduct (fun i => MvPolynomial.C (l i))
      (Q*ᵥ(H*ᵥ(fun j => MvPolynomial.C (E j))))) =
    dotProduct l ((Q.map (MvPolynomial.eval v))*ᵥ((H.map (MvPolynomial.eval v))*ᵥE)) := by
  simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, MvPolynomial.eval_C, Matrix.map_apply]

private theorem constraint_polynomial_eval (event : DressedEvent) (epsilon sigma : ℝ)
    (n : PhysicalMomentum) (row : Fin 9) :
    (sourceTemporalQuantumConstraintPolynomial event epsilon n row).eval (sigma : ℂ) =
      sourceCokernel (frequencyRay epsilon 0 n)
        (((commonNumerator event n).map (MvPolynomial.eval (irValues epsilon sigma 0)))*ᵥ
          (((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate*ᵥ
            sourceTemporalEMForce)) row := by
  have adj := (MvPolynomial.eval (irValues epsilon sigma 0)).map_adjugate (commonClearedPencil event n)
  have mapped : (commonClearedPencil event n).adjugate.map (MvPolynomial.eval (irValues epsilon sigma 0)) =
      ((commonClearedPencil event n).map (MvPolynomial.eval (irValues epsilon sigma 0))).adjugate := adj
  unfold sourceTemporalQuantumConstraintPolynomial
  rw [damping_slice_eval, eval_constant_full_read, mapped, original_null_cokernel]
  rfl

/-- Every coefficient of the actual quantum nine-row cofactor is generated as
zero from the original static Euler rows and the same temporal EM source column.
No regular Green chart, pole mode or zero-clock balance is assumed. -/
theorem source_temporal_quantum_constraint_polynomial (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (row : Fin 9) :
    sourceTemporalQuantumConstraintPolynomial event epsilon n row = 0 := by
  apply positive_clock_polynomial_zero
  intro sigma positive
  rw [constraint_polynomial_eval]
  let evaluation := MvPolynomial.eval (irValues epsilon sigma 0)
  have pencil : (commonClearedPencil event n).map evaluation =
      evaluation (commonDenominator event n) • emOriginalJacobi (frequencyRay epsilon 0 n) -
        (sigma : ℂ) • (commonNumerator event n).map evaluation := by
    unfold commonClearedPencil
    rw [Matrix.map_sub _ (fun a b => evaluation.map_sub a b),
      Matrix.map_smul' _ _ _ (fun a b => evaluation.map_mul a b),
      Matrix.map_smul' _ _ _ (fun a b => evaluation.map_mul a b)]
    dsimp only [evaluation]
    rw [common_jacobi_eval]
    simp only [MvPolynomial.eval_X, irValues, one_ne_zero, ite_false, ite_true]
  have static : frequencyRay epsilon 0 n 0=0 := by
    change -Complex.I*((0*epsilon^2 : ℝ) : ℂ)=0
    simp only [zero_mul, Complex.ofReal_zero, mul_zero]
  have classical : ∀ a : Fin 289 → ℂ,
      sourceCokernel (frequencyRay epsilon 0 n) (emOriginalJacobi (frequencyRay epsilon 0 n)*ᵥa)=0 := by
    intro a
    rw [em_jacobi_source]
    exact (source_compatibility_nine _ _).mp (source_compatibility_euler _ _)
  have sigma_nonzero : (sigma : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt positive)
  have generated := cofactor_quantum_cokernel (emOriginalJacobi (frequencyRay epsilon 0 n))
    ((commonNumerator event n).map evaluation) (sourceCokernel (frequencyRay epsilon 0 n))
    (evaluation (commonDenominator event n)) (sigma : ℂ) sourceTemporalEMForce sigma_nonzero classical
    (source_em_temporal_cokernel _ static)
  rw [←pencil] at generated
  exact congrFun generated row

theorem source_temporal_quantum_constraint_coefficient (event : DressedEvent) (epsilon : ℝ)
    (n : PhysicalMomentum) (row : Fin 9) (k : ℕ) :
    (sourceTemporalQuantumConstraintPolynomial event epsilon n row).coeff k = 0 := by
  rw [source_temporal_quantum_constraint_polynomial, coeff_zero]

end LowEnergy.GaussComposite.ActualSourcePreparedTemporalQuantumCofactor
