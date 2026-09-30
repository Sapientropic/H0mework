import H0mework.Physics.LowEnergy.FullQuantum.TriangularTime

/-! Exact triangular time evolution gives a momentum-uniform linear growth bound. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open YangMills.FullPairing Triangular ProofFreeRicherAnholonomicSource StageNineHolonomicField
noncomputable section
local instance : NormedAlgebra ℚ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : NormedAlgebra ℝ (Hilbert →L[ℂ] Hilbert) := NormedAlgebra.restrictScalars ℝ ℂ _

theorem flow_unitary (A : Operators) (skew : star A=-A) (time : ℝ) :
    flow A time ∈ unitary Operators := by
  apply NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
  change star ((time : ℂ) • A)=-((time : ℂ) • A)
  rw [star_smul,skew]
  simp
  ext v i
  rfl

theorem flow_norm_le_one (A : Operators) (skew : star A=-A) (time : ℝ) : ‖flow A time‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro initial
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (flow_unitary A skew time),one_mul]

theorem freeEvolution_norm_le_one (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (momentum : Fin 3 → ℝ) (symmetric : IsSelfAdjoint (operator (freeHamiltonian C p momentum)))
    (time : ℝ) : ‖freeEvolution C p momentum time‖≤1 := by
  have skew : star (operator (freeDrift C p momentum))=-operator (freeDrift C p momentum) := by
    rw [← free_hamiltonian_drift,operator_smul,star_smul,symmetric.star_eq]
    simp
    ext v i
    simp
  exact flow_norm_le_one _ skew time

theorem complete_evolution_bound (C : StageNineHolonomicConfiguration) (p : BasePoint)
    (momentum : Fin 3 → ℝ) (symmetric : IsSelfAdjoint (operator (freeHamiltonian C p momentum)))
    (time : ℝ) :
    ‖evolution C p momentum time‖≤1+|time| * ‖operator (interaction C p)‖ := by
  rw [source_exact_duhamel]
  have integrand (s : ℝ) :
      ‖freeEvolution C p momentum (time-s)*operator (interaction C p)*freeEvolution C p momentum s‖≤
        ‖operator (interaction C p)‖ := by
    calc
      _ ≤ ‖freeEvolution C p momentum (time-s)‖*‖operator (interaction C p)‖*
          ‖freeEvolution C p momentum s‖ := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ 1*‖operator (interaction C p)‖*1 := by
        gcongr <;> exact freeEvolution_norm_le_one C p momentum symmetric _
      _ = _ := by ring
  have integral := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := time) (fun s _ => integrand s)
  have free := freeEvolution_norm_le_one C p momentum symmetric time
  exact (norm_add_le _ _).trans ((add_le_add free integral).trans_eq (by simp [mul_comm]))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
