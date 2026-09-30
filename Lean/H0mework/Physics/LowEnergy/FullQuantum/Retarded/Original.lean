import H0mework.Physics.LowEnergy.FullQuantum.Retarded.Green
import H0mework.Physics.LowEnergy.FullQuantum.TriangularTrace

/-! The same causal integral returns to the full mother Dirac operator, with
its original temporal-principal inverse on the right and independent dual readers intact. -/
set_option autoImplicit false
open Set MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair YangMills.FullPairing
open Triangular FullSpace StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

private theorem operator_one : operator (1 : Mother)=(1 : Operators) := by ext v; simp [operator]

private theorem operator_from (A : Operators) : operator (fromOperator A)=A := by
  ext v
  simp [operator,fromOperator]

private theorem operator_injective : Function.Injective operator := by
  intro A B same
  apply LinearMap.ext
  intro v
  apply naturalCoordinates.injective
  have read := congrArg (fun T : Operators => T (naturalCoordinates v)) same
  simpa only [operator_coordinates] using read

def sourceInverse (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Mother :=
  fromOperator (resolvent point momentum energy damping)

theorem sourceInverse_two_sided (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    fullKernel actual point momentum (spectralParameter energy damping)*sourceInverse point momentum energy damping=1 ∧
      sourceInverse point momentum energy damping*fullKernel actual point momentum (spectralParameter energy damping)=1 := by
  constructor
  · apply operator_injective
    rw [operator_mul,sourceInverse,operator_from,operator_one]
    exact (resolvent_two_sided point momentum energy damping positive).1
  · apply operator_injective
    rw [operator_mul,sourceInverse,operator_from,operator_one]
    exact (resolvent_two_sided point momentum energy damping positive).2

theorem sourceKernel_isUnit (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    IsUnit (fullKernel actual point momentum (spectralParameter energy damping)) :=
  ⟨⟨fullKernel actual point momentum (spectralParameter energy damping),sourceInverse point momentum energy damping,
    (sourceInverse_two_sided point momentum energy damping positive).1,
    (sourceInverse_two_sided point momentum energy damping positive).2⟩,rfl⟩

theorem sourceFree_regular (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    IsUnit (freeKernel actual point momentum (spectralParameter energy damping)) :=
  (full_regular_iff_free actual point momentum (spectralParameter energy damping)).mp
    (sourceKernel_isUnit point momentum energy damping positive)

theorem value_fullResolvent (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    value point momentum energy damping =
      Complex.I • operator (fullResolvent actual point momentum (spectralParameter energy damping)) := by
  have inverse := fullResolvent_two_sided actual point momentum (spectralParameter energy damping)
    (sourceFree_regular point momentum energy damping positive)
  have left : operator (fullResolvent actual point momentum (spectralParameter energy damping))*
      kernel point momentum energy damping=1 := by
    rw [kernel,← operator_mul,inverse.2,operator_one]
  calc
    _ = (operator (fullResolvent actual point momentum (spectralParameter energy damping))*
        kernel point momentum energy damping)*value point momentum energy damping := by rw [left,one_mul]
    _ = operator (fullResolvent actual point momentum (spectralParameter energy damping))*
        (kernel point momentum energy damping*value point momentum energy damping) := mul_assoc _ _ _
    _ = _ := by rw [value_kernel_left point momentum energy damping positive,mul_smul_comm,mul_one]

def diracIntegrand (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping time : ℝ) : Operators :=
  integrand point momentum energy damping time*
    operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))

theorem diracIntegrand_integrable (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    IntegrableOn (diracIntegrand point momentum energy damping) (Ioi 0) := by
  let multiply := (ContinuousLinearMap.mul ℂ Operators).flip
    (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)))
  exact multiply.integrable_comp (integrand_integrable point momentum energy damping positive)

def diracValue (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) : Operators :=
  ∫ t : ℝ in Ioi 0, diracIntegrand point momentum energy damping t

theorem diracValue_side (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    diracValue point momentum energy damping=value point momentum energy damping*
      operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)) := by
  exact ((ContinuousLinearMap.mul ℂ Operators).flip
    (operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)))).integral_comp_comm
      (integrand_integrable point momentum energy damping positive)

theorem diracValue_original (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    diracValue point momentum energy damping=
      operator (diracResolvent actual point momentum (spectralParameter energy damping)) := by
  rw [diracValue_side point momentum energy damping positive,
    value_fullResolvent point momentum energy damping positive,diracResolvent,
    operator_smul,operator_mul,smul_mul_assoc]

theorem diracValue_two_sided (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    operator (diracKernel actual point momentum (spectralParameter energy damping))*
      diracValue point momentum energy damping=1 ∧
    diracValue point momentum energy damping*
      operator (diracKernel actual point momentum (spectralParameter energy damping))=1 := by
  have generated := diracResolvent_two_sided actual point momentum (spectralParameter energy damping)
    (actual_noncharacteristic point) (sourceFree_regular point momentum energy damping positive)
  rw [diracValue_original point momentum energy damping positive]
  constructor
  · rw [← operator_mul,generated.1,operator_one]
  · rw [← operator_mul,generated.2,operator_one]

theorem diracValue_bound (point : BasePoint) (momentum : Fin 3 → ℝ)
    (energy damping : ℝ) (positive : 0<damping) :
    ‖diracValue point momentum energy damping‖≤
      (damping⁻¹+couplingNorm point*damping⁻¹^2)*
        ‖operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))‖ := by
  rw [diracValue_side point momentum energy damping positive]
  exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
    (value_bound point momentum energy damping positive) (norm_nonneg _))

theorem diracValue_continuous (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    Continuous (fun momentum : Fin 3 → ℝ => diracValue point momentum energy damping) := by
  simp only [diracValue_side point _ energy damping positive]
  exact (value_continuous point energy damping positive).mul continuous_const

theorem dirac_initial_readback (point : BasePoint) (momentum : Fin 3 → ℝ) (energy damping : ℝ) :
    operator (currentCoframeMatterTemporalPrincipal (actual.coframe point))*
      diracIntegrand point momentum energy damping 0=1 := by
  rw [diracIntegrand,integrand_zero,one_mul,← operator_mul]
  have source : currentCoframeMatterTemporalPrincipal (actual.coframe point)*
      currentCoframeMatterTemporalPrincipalInverse (actual.coframe point)=1 := by
    apply LinearMap.ext
    intro v
    exact currentCoframeMatterTemporalPrincipalInverse_right _ (actual_noncharacteristic point) v
  rw [source,operator_one]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.Retarded
