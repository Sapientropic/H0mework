import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeGreen.Space
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.PerturbedGreen.Inverse

/-! Every actual real gauge resolvent obeys the same source coercive bound, independently of amplitude. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace ProofFreeRicherAnholonomicSource PerturbedGreen
noncomputable section

def Equation (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (parameter : ℝ) (field source : FullMatterL2) : Prop :=
  field=freeR point energy damping positive (source+(parameter : ℂ) • W field)

theorem equation_norm (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) (field source : FullMatterL2)
    (solves : Equation point energy damping positive W parameter field source) :
    damping*‖field‖≤‖source‖ := by
  have real : (inner ℂ field (W field)).im=0 :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp symmetric).im_inner_self_apply field
  have paired := freeR_imaginary_pair point energy damping positive (source+(parameter : ℂ) • W field)
  rw [← solves] at paired
  simp only [inner_add_right,inner_smul_right,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,real,zero_mul,mul_zero,add_zero] at paired
  exact norm_of_imaginary_pair damping field source paired

theorem equation_zero (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) (field : FullMatterL2)
    (solves : Equation point energy damping positive W parameter field 0) : field=0 := by
  have estimate := equation_norm point energy damping positive W symmetric parameter field 0 solves
  rw [norm_zero] at estimate
  apply norm_eq_zero.mp
  nlinarith [norm_nonneg field]

theorem equation_unique (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ) (first second source : FullMatterL2)
    (left : Equation point energy damping positive W parameter first source)
    (right : Equation point energy damping positive W parameter second source) : first=second := by
  have difference : Equation point energy damping positive W parameter (first-second) 0 := by
    change first-second=freeR point energy damping positive (0+(parameter : ℂ) • W (first-second))
    calc
      _ = freeR point energy damping positive (source+(parameter : ℂ) • W first)-
          freeR point energy damping positive (source+(parameter : ℂ) • W second) := congrArg₂ (fun u v => u-v) left right
      _ = freeR point energy damping positive
          ((source+(parameter : ℂ) • W first)-(source+(parameter : ℂ) • W second)) := (map_sub _ _ _).symm
      _ = _ := by
        congr 1
        rw [map_sub,smul_sub,zero_add]
        abel
  exact sub_eq_zero.mp (equation_zero point energy damping positive W symmetric parameter (first-second) difference)

structure ResolventAt (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (parameter : ℝ) where
  value : SpatialOperators
  solves : ∀ source : FullMatterL2, Equation point energy damping positive W parameter (value source) source

theorem ResolventAt.norm (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) (symmetric : IsSelfAdjoint W) (parameter : ℝ)
    (generated : ResolventAt point energy damping positive W parameter) : ‖generated.value‖≤damping⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr positive.le)
  intro source
  have bound := equation_norm point energy damping positive W symmetric parameter (generated.value source) source
    (generated.solves source)
  exact (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using bound) |>.trans_eq (by ring)

def initial (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (W : SpatialOperators) : ResolventAt point energy damping positive W 0 where
  value := freeR point energy damping positive
  solves source := by simp [Equation]

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
