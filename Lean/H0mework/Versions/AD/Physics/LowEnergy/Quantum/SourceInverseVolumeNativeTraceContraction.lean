import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceInverseVolumeDoubleGramCurvatureForm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.SourceNativeTraceContraction
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open GaussNativeForm
open SaturationMonoid.PhysicsCore StageNineHolonomicField StageNineP286BracketCalculus
open StageNineP286LinkedActiveGaugeBFAlgebra StageNineP286GaugeConnectionVariationDensity
open scoped InnerProductSpace

private theorem scalar_skew (a : NativeLie) (x y : Scalar) :
    inner ℝ (scalarP286ActionBilinear a x) y+inner ℝ x (scalarP286ActionBilinear a y)=0 := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing,original_scalar_pairing] at h
  exact h

/-- The full native trace contracts with the same complete scalar frame. -/
theorem original_trace_contraction (n : Scalar →ₗ[ℝ] NativeLie)
    (M : Module.End ℝ NativeLie) (s : Scalar) :
    LinearMap.trace ℝ NativeLie (M.comp (n.comp (SourceQuantumScalarChart.action s)))=
      -(∑ r : ScalarIndex,inner ℝ s (scalarP286ActionBilinear (M (n (scalarBasis r))) (scalarBasis r))) := by
  have h := LinearMap.trace_comp_comm' (R := ℝ) (M := NativeLie) (N := Scalar)
    (SourceQuantumScalarChart.action s) (M.comp n)
  rw [LinearMap.comp_assoc] at h
  rw [h,LinearMap.trace_eq_matrix_trace ℝ scalarBasis.toBasis]
  simp only [Matrix.trace,Matrix.diag,LinearMap.toMatrix_apply,LinearMap.comp_apply]
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  simp only [OrthonormalBasis.coe_toBasis_repr_apply,OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis]
  change inner ℝ (scalarBasis r) (scalarP286ActionBilinear (M (n (scalarBasis r))) s)=_
  have hs := scalar_skew (M (n (scalarBasis r))) s (scalarBasis r)
  rw [real_inner_comm (scalarBasis r) (scalarP286ActionBilinear (M (n (scalarBasis r))) s)] at hs
  exact eq_neg_of_add_eq_zero_left hs

/-- The same trace supplies the complete scalar divergence vector. -/
theorem original_trace_vector (n : Scalar →ₗ[ℝ] NativeLie) :
    (∑ r : ScalarIndex,LinearMap.trace ℝ NativeLie
      (n.comp (SourceQuantumScalarChart.action (scalarBasis r))) • scalarBasis r)=
      -(∑ r : ScalarIndex,scalarP286ActionBilinear (n (scalarBasis r)) (scalarBasis r)) := by
  apply scalarBasis.repr.injective
  apply PiLp.ext
  intro s
  simp only [OrthonormalBasis.repr_apply_apply,inner_sum,inner_neg_right,inner_smul_right]
  have hb := orthonormal_iff_ite.mp scalarBasis.orthonormal
  simp only [hb,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_pos]
  have h := original_trace_contraction n (LinearMap.id : Module.End ℝ NativeLie) (scalarBasis s)
  simpa only [LinearMap.id_comp,LinearMap.id_apply,inner_sum] using h

/-- Scalar skew transports both occurrences of the same inverse-frame read. -/
theorem original_skew_frame_contraction (n : Scalar →ₗ[ℝ] NativeLie) (a : NativeLie) :
    (∑ r : ScalarIndex,scalarP286ActionBilinear
      (n (scalarP286ActionBilinear a (scalarBasis r))) (scalarBasis r))=
      -(∑ r : ScalarIndex,scalarP286ActionBilinear (n (scalarBasis r))
        (scalarP286ActionBilinear a (scalarBasis r))) := by
  let rho : NativeLie →ₗ[ℝ] Scalar →ₗ[ℝ] Scalar := scalarP286ActionBilinear
  change (∑ r : ScalarIndex,rho (n (rho a (scalarBasis r))) (scalarBasis r))=
    -(∑ r : ScalarIndex,rho (n (scalarBasis r)) (rho a (scalarBasis r)))
  have he (r : ScalarIndex) : n (rho a (scalarBasis r))=
      ∑ s : ScalarIndex,inner ℝ (scalarBasis s)
        (rho a (scalarBasis r)) • n (scalarBasis s) := by
    simpa only [map_sum,map_smul] using congrArg n
      (scalarBasis.sum_repr' (rho a (scalarBasis r))).symm
  have hx (r : ScalarIndex) : rho (n (rho a (scalarBasis r))) (scalarBasis r)=
      ∑ s : ScalarIndex,inner ℝ (scalarBasis s) (rho a (scalarBasis r)) •
        rho (n (scalarBasis s)) (scalarBasis r) := by
    rw [he]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
  simp only [hx]
  rw [Finset.sum_comm]
  have hc (s r : ScalarIndex) : inner ℝ (scalarBasis s)
      (rho a (scalarBasis r))=
      -inner ℝ (scalarBasis r) (rho a (scalarBasis s)) := by
    have h := scalar_skew a (scalarBasis r) (scalarBasis s)
    rw [real_inner_comm (scalarBasis s) (scalarP286ActionBilinear a (scalarBasis r))] at h
    exact eq_neg_of_add_eq_zero_left h
  have hs (s : ScalarIndex) :
      (∑ r : ScalarIndex,inner ℝ (scalarBasis s) (rho a (scalarBasis r)) •
        rho (n (scalarBasis s)) (scalarBasis r))=
      -(rho (n (scalarBasis s)) (rho a (scalarBasis s))) := by
    calc
      _ = ∑ r : ScalarIndex,-inner ℝ (scalarBasis r) (rho a (scalarBasis s)) •
          rho (n (scalarBasis s)) (scalarBasis r) := by
        apply Finset.sum_congr rfl
        intro r _
        rw [hc s r]
      _ = -(∑ r : ScalarIndex,inner ℝ (scalarBasis r) (rho a (scalarBasis s)) •
          rho (n (scalarBasis s)) (scalarBasis r)) := by
        simp only [neg_smul,Finset.sum_neg_distrib]
      _ = _ := by
        congr 1
        simpa only [map_sum,map_smul] using congrArg (rho (n (scalarBasis s)))
          (scalarBasis.sum_repr' (rho a (scalarBasis s)))
  simp only [hs,Finset.sum_neg_distrib]

end LowEnergy.SourceNativeTraceContraction
