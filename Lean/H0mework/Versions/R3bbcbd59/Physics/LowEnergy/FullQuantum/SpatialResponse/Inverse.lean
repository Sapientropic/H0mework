import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialResponse.Fields

/-! The same primitive all-field family has the ordered resolvent identity and a genuine operator-norm derivative. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
open FullSpace GaugeGreen ScalarGreen PerturbedGreen
noncomputable section
attribute [local irreducible] fullG

theorem family_zero (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) :
    family energy damping positive gauge direction scalar scalarDirection 0=
      fullG 0 energy damping positive gauge 1 scalar := by
  simp only [family,Complex.ofReal_zero,zero_smul,add_zero]

theorem family_correction (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (epsilon : ℝ) (source : FullMatterL2) :
    correction (fullG 0 energy damping positive gauge 1 scalar) (variation direction scalarDirection) (epsilon : ℂ)
      (family energy damping positive gauge direction scalar scalarDirection epsilon source)=
      fullG 0 energy damping positive gauge 1 scalar source := by
  let lifted := domainFullG 0 energy damping positive (gauge+epsilon • direction) 1
    (scalar+(epsilon : ℂ) • scalarDirection) source
  have affine := originalKernel_affine energy damping gauge direction scalar scalarDirection epsilon lifted
  have solves := originalKernel_fullG 0 energy damping positive (gauge+epsilon • direction) 1
    (scalar+(epsilon : ℂ) • scalarDirection) source
  change originalKernel 0 energy damping (gauge+epsilon • direction) 1
    (scalar+(epsilon : ℂ) • scalarDirection) lifted=source at solves
  rw [solves] at affine
  have base : originalKernel 0 energy damping gauge 1 scalar lifted=
      source-(epsilon : ℂ) • variation direction scalarDirection lifted.val :=
    eq_sub_iff_add_eq.mpr affine.symm
  have restored := fullG_originalKernel 0 energy damping positive gauge 1 scalar lifted
  rw [base,map_sub,map_smul] at restored
  change lifted.val+(epsilon : ℂ) • fullG 0 energy damping positive gauge 1 scalar
    (variation direction scalarDirection lifted.val)=fullG 0 energy damping positive gauge 1 scalar source
  exact eq_sub_iff_add_eq.mp restored.symm

theorem family_correction_operator (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (epsilon : ℝ) :
    correction (fullG 0 energy damping positive gauge 1 scalar) (variation direction scalarDirection) (epsilon : ℂ)*
      family energy damping positive gauge direction scalar scalarDirection epsilon=
      fullG 0 energy damping positive gauge 1 scalar := by
  apply ContinuousLinearMap.ext
  intro source
  exact family_correction energy damping positive gauge direction scalar scalarDirection epsilon source

theorem resolvent_identity (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (epsilon : ℝ) :
    family energy damping positive gauge direction scalar scalarDirection epsilon-fullG 0 energy damping positive gauge 1 scalar=
      -(epsilon : ℂ) • (fullG 0 energy damping positive gauge 1 scalar*variation direction scalarDirection*
        family energy damping positive gauge direction scalar scalarDirection epsilon) := by
  have fixed := family_correction_operator energy damping positive gauge direction scalar scalarDirection epsilon
  rw [correction,add_mul,one_mul,smul_mul_assoc] at fixed
  calc
    _ = (fullG 0 energy damping positive gauge 1 scalar-
        (epsilon : ℂ) • (fullG 0 energy damping positive gauge 1 scalar*variation direction scalarDirection*
          family energy damping positive gauge direction scalar scalarDirection epsilon))-
        fullG 0 energy damping positive gauge 1 scalar := by rw [← eq_sub_iff_add_eq.mpr fixed]
    _ = _ := by module

theorem family_eq_inverse_near (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) (epsilon : ℝ)
    (small : ‖(epsilon : ℂ) • (fullG 0 energy damping positive gauge 1 scalar*variation direction scalarDirection)‖<1) :
    family energy damping positive gauge direction scalar scalarDirection epsilon=
      response (fullG 0 energy damping positive gauge 1 scalar) (variation direction scalarDirection) (epsilon : ℂ) := by
  let G := fullG 0 energy damping positive gauge 1 scalar
  let V := variation direction scalarDirection
  have unit := correction_isUnit G V (epsilon : ℂ) small
  have inverse := Ring.inverse_mul_cancel _ unit
  calc
    _ = 1*family energy damping positive gauge direction scalar scalarDirection epsilon := (one_mul _).symm
    _ = (Ring.inverse (correction G V (epsilon : ℂ))*correction G V (epsilon : ℂ))*
        family energy damping positive gauge direction scalar scalarDirection epsilon := by rw [inverse]
    _ = Ring.inverse (correction G V (epsilon : ℂ))*
        (correction G V (epsilon : ℂ)*family energy damping positive gauge direction scalar scalarDirection epsilon) := mul_assoc _ _ _
    _ = Ring.inverse (correction G V (epsilon : ℂ))*G := by
      rw [family_correction_operator]
    _ = _ := rfl

theorem family_derivative (energy damping : ℝ) (positive : 0<damping)
    (gauge direction : GaugeProfile) (scalar scalarDirection : ScalarProfile) :
    HasDerivAt (family energy damping positive gauge direction scalar scalarDirection)
      (-(fullG 0 energy damping positive gauge 1 scalar*variation direction scalarDirection*
        fullG 0 energy damping positive gauge 1 scalar)) 0 := by
  have equal : (fun epsilon : ℝ => response (fullG 0 energy damping positive gauge 1 scalar)
      (variation direction scalarDirection) (epsilon : ℂ))=ᶠ[𝓝 0]
      family energy damping positive gauge direction scalar scalarDirection := by
    filter_upwards [small_near_zero (fullG 0 energy damping positive gauge 1 scalar)
      (variation direction scalarDirection)] with epsilon small
    exact (family_eq_inverse_near energy damping positive gauge direction scalar scalarDirection epsilon small).symm
  exact (response_real_derivative (fullG 0 energy damping positive gauge 1 scalar)
    (variation direction scalarDirection)).congr_of_eventuallyEq equal.symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialResponse
