import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualMixedPreparedKernel
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveArrays

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLocalizedYukawa
open SaturationMonoid.PhysicsCore
open PreparationVacuumPrimitiveMatrix PreparationScalarCoordinates PreparationActualFactor
open CanonicalPreparationCutoff SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumScalarChart
open GaussYukawaCoefficient GaussRadialDomain GaussCoreHilbert FullYSourceCutoffVolterra
open scoped BigOperators Topology RealInnerProductSpace

theorem scalar_norm_le_L1 (s : Scalar) : ‖s‖ ≤ scalarL1 s := by
  have square : ‖s‖^2=∑ i : Fin 70,(scalarRealify s i)^2 := by
    rw [←real_inner_self_eq_norm_sq,scalar_inner_realified]
    simp only [pow_two]
  have sumBound := Finset.sum_sq_le_sq_sum_of_nonneg
    (s:=Finset.univ) (f:=fun i : Fin 70=>|scalarRealify s i|) (fun _ _=>abs_nonneg _)
  have nonnegative : 0 ≤ scalarL1 s := Finset.sum_nonneg (fun _ _=>abs_nonneg _)
  simp only [sq_abs] at sumBound
  change (∑ i : Fin 70,(scalarRealify s i)^2) ≤ (scalarL1 s)^2 at sumBound
  rw [←square] at sumBound
  nlinarith [norm_nonneg s]

def sourceRadiusBound : ℝ := 916
def sourceCutRate : ℝ := 1-sourceRadiusBound⁻¹

theorem sourceRadiusBound_positive : 0<sourceRadiusBound := by norm_num [sourceRadiusBound]
theorem sourceCutRate_nonnegative : 0 ≤ sourceCutRate := by norm_num [sourceCutRate,sourceRadiusBound]
theorem sourceCutRate_lt_one : sourceCutRate<1 := by norm_num [sourceCutRate,sourceRadiusBound]

theorem source_scalar_norm (z : SourceCoordinateSlice) (box : fullCoordinates z∈sourceClosedBox) :
    ‖z.2.1.val‖ ≤ 915 := by
  have source:=sourceScalar_box_L1 (fullCoordinates z,0) box
  rw [sourceScalar_native,ContinuousLinearEquiv.symm_apply_apply] at source
  exact (scalar_norm_le_L1 z.2.1.val).trans source

theorem source_radius_bound (z : SourceCoordinateSlice) (box : fullCoordinates z∈sourceClosedBox) :
    radius z ≤ sourceRadiusBound := by
  have sigma:=source_scalar_norm z box
  have square : (radius z)^2=1+‖z.2.1.val‖^2/4 :=
    Real.sq_sqrt (by positivity)
  norm_num [sourceRadiusBound]
  nlinarith [radius_pos z,norm_nonneg z.2.1.val]

theorem reciprocal_positive (z : SourceCoordinateSlice) : 0<reciprocal z :=
  inv_pos.mpr (radius_pos z)

theorem reciprocal_le_one (z : SourceCoordinateSlice) : reciprocal z ≤ 1 :=
  inv_le_one_of_one_le₀ (one_le_radius z)

theorem source_geometric_rate (z : SourceCoordinateSlice) (box : fullCoordinates z∈sourceClosedBox) :
    0 ≤ 1-reciprocal z ∧ 1-reciprocal z ≤ sourceCutRate := by
  refine ⟨sub_nonneg.mpr (reciprocal_le_one z),?_⟩
  have inverse : sourceRadiusBound⁻¹ ≤ (radius z)⁻¹ :=
    inv_anti₀ (radius_pos z) (source_radius_bound z box)
  exact sub_le_sub_left inverse 1

theorem actual_cutoff_graph_residual (n : ℕ) (x y : H) (source : (x,y)∈GaussRadialDomain.graph) :
    y-cutoff n x=((1-GaussRadialDomain.inverseRadius)^(n+1)) y := by
  have graph : GaussYukawaOperator.bounded x=GaussRadialDomain.inverseRadius y := source
  induction n with
  | zero=>
    change y-GaussYukawaOperator.bounded x=(1-GaussRadialDomain.inverseRadius) y
    rw [graph]
    simp only [sub_apply,one_apply_eq_self]
  | succ n ih=>
    change y-(GaussYukawaOperator.bounded x+(1-GaussRadialDomain.inverseRadius) (cutoff n x))=
      ((1-GaussRadialDomain.inverseRadius)^(n+1+1)) y
    rw [graph,pow_succ']
    change y-(GaussRadialDomain.inverseRadius y+(1-GaussRadialDomain.inverseRadius) (cutoff n x))=
      (1-GaussRadialDomain.inverseRadius) (((1-GaussRadialDomain.inverseRadius)^(n+1)) y)
    rw [←ih]
    simp only [sub_apply,one_apply_eq_self,map_sub]
    abel

end LowEnergy.PreparationVacuumLocalizedYukawa
