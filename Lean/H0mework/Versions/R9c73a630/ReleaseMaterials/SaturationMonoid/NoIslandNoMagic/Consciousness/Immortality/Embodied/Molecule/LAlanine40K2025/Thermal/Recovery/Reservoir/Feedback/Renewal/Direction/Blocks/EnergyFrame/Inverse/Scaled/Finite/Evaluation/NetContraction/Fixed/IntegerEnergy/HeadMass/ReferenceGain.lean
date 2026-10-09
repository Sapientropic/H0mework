import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.HeadMass.EntryError
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.ChargedProgram.EnergyOrder

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Load.Source Collision Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section



/-! From the original rational net operator to the actual source input. -/

def computedOrdinaryBody (a b : Basis) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.kronecker (computedOrdinaryPairBlock a b) environmentState

theorem computed_ordinary_body_positive (a b : Basis) :
    (computedOrdinaryBody a b).PosSemidef :=
  (computed_ordinary_pair_positive a b).kronecker environmentState_positive

theorem computed_ordinary_body_trace (a b : Basis) :
    (computedOrdinaryBody a b).trace.re = (computedOrdinaryPairBlock a b).trace.re := by
  rw [computedOrdinaryBody]
  simp only [Matrix.kronecker,Matrix.trace_kronecker,environmentState_trace,mul_one]

theorem original_ordinary_body_reference_error (a b : Basis) (ordered : a < b) :
    ‖qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)-computedOrdinaryBody a b‖ ≤
      (4/10^20 : ℝ)+(7/10^18)*(computedOrdinaryBody a b).trace.re := by
  have split : qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)-
      computedOrdinaryBody a b =
      Matrix.kronecker (originalPairBlock a b-computedOrdinaryPairBlock a b)
        Prepared.finiteEnvironment +
      Matrix.kronecker (computedOrdinaryPairBlock a b)
        (Prepared.finiteEnvironment-environmentState) := by
    rw [qvalue_kron,ordinary_pair_block_value,environmentQ_value,computedOrdinaryBody]
    ext i j
    simp only [Matrix.kronecker,Matrix.kroneckerMap_apply,Matrix.sub_apply,Matrix.add_apply]
    ring
  have mass := positive_norm_le_trace_re (computedOrdinaryPairBlock a b)
    (computed_ordinary_pair_positive a b)
  have massNonnegative := (norm_nonneg (computedOrdinaryPairBlock a b)).trans mass
  have pair : ‖Matrix.kronecker (originalPairBlock a b-computedOrdinaryPairBlock a b)
      Prepared.finiteEnvironment‖ ≤ (4/10^20 : ℝ) :=
    (kronecker_norm_le _ _).trans
      ((mul_le_mul (source_ordinary_pair_block_error a b ordered)
        Diagonal.finite_environment_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have env : ‖Prepared.finiteEnvironment-environmentState‖ ≤ (7/10^18 : ℝ) := by
    simpa only [norm_sub_rev] using Prepared.original_finite_environment_error
  have environment : ‖Matrix.kronecker (computedOrdinaryPairBlock a b)
      (Prepared.finiteEnvironment-environmentState)‖ ≤
      (computedOrdinaryPairBlock a b).trace.re*(7/10^18 : ℝ) :=
    (kronecker_norm_le _ _).trans (mul_le_mul mass env (norm_nonneg _) massNonnegative)
  rw [split,computed_ordinary_body_trace]
  exact (norm_add_le _ _).trans ((add_le_add pair environment).trans (by ring_nf; rfl))

theorem original_ordinary_gain_reference_error (a b : Basis) (ordered : a < b) :
    |(smallGainQ (s(a,b)) : ℝ)-
      (sourceOrdinaryQNet a b ordered * computedOrdinaryBody a b).trace.re| ≤
      (3/10^12 : ℝ)*(computedOrdinaryBody a b).trace.re+(2/10^14 : ℝ) := by
  rw [← ordinary_fast_gain_original a b ordered,source_ordinary_q_gain_cast,Collision.energy]
  have trace := Donor.trace_norm_bound
    (sourceOrdinaryQNet a b ordered *
      (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)-computedOrdinaryBody a b))
  norm_num at trace
  have productBound :
      ‖sourceOrdinaryQNet a b ordered *
        (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)-computedOrdinaryBody a b)‖ ≤
      (102528 : ℝ)*((4/10^20)+(7/10^18)*(computedOrdinaryBody a b).trace.re) :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul (source_ordinary_qnet_norm a b ordered)
        (original_ordinary_body_reference_error a b ordered) (norm_nonneg _) (by norm_num))
  have bound := ((Complex.abs_re_le_norm
    (sourceOrdinaryQNet a b ordered *
      (qvalue (qkron (ordinaryPairBlockQ a b) environmentQ)-computedOrdinaryBody a b)).trace).trans trace).trans
    (mul_le_mul_of_nonneg_left productBound (by norm_num : (0 : ℝ) ≤ 4))
  simp only [Matrix.mul_sub,Matrix.trace_sub,Complex.sub_re] at bound
  have mass := (Complex.nonneg_iff.mp (computed_ordinary_body_positive a b).trace_nonneg).1
  exact bound.trans (by nlinarith only [mass])

theorem original_ordinary_gain_lower_of_order (a b : Basis) (ordered : a < b)
    (floor : ℝ)
    (spectral : floor • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceOrdinaryQNet a b ordered) :
    (floor-3/10^12)*(computedOrdinaryBody a b).trace.re-(2/10^14 : ℝ) ≤
      (smallGainQ (s(a,b)) : ℝ) := by
  have energy := energy_lower_from_order _ _ (computed_ordinary_body_positive a b) floor spectral
  have error := (abs_le.mp (original_ordinary_gain_reference_error a b ordered)).1
  linarith only [energy,error]


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
