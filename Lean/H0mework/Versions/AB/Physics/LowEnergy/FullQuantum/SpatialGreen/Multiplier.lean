import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.FullSpace.Dual
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.Retarded.Original

/-! The actual positive-damping time integral acts on every full spatial source. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
open FullSpace Retarded YangMills.FullPairing ProofFreeRicherAnholonomicSource
open Stage9C.Material.SpinPair StageNineCurrentCoframeMatterTemporalPrincipal
noncomputable section

def bound (point : BasePoint) (damping : ℝ) : ℝ :=
  (damping⁻¹+couplingNorm point*damping⁻¹^2)*
    ‖operator (currentCoframeMatterTemporalPrincipalInverse (actual.coframe point))‖

theorem bound_nonnegative (point : BasePoint) (damping : ℝ) (positive : 0<damping) :
    0≤bound point damping := by unfold bound couplingNorm; positivity

def matrices (point : BasePoint) (energy damping : ℝ) (frequency : Position) : FiberOperators :=
  diracValue point (physicalMomentum frequency) energy damping

theorem matrices_continuous (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    Continuous (matrices point energy damping) :=
  (diracValue_continuous point energy damping positive).comp physicalMomentum_continuous

theorem matrices_bound (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (frequency : Position) : ‖matrices point energy damping frequency‖≤bound point damping :=
  diracValue_bound point (physicalMomentum frequency) energy damping positive

def momentumGreen (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (matrices point energy damping) (matrices_continuous point energy damping positive)
    (bound point damping) (matrices_bound point energy damping positive) (bound_nonnegative point damping positive)

theorem momentumGreen_ae (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : momentumGreen point energy damping positive source=ᵐ[volume]
      fun frequency => diracValue point (physicalMomentum frequency) energy damping (source frequency) :=
  multiplierValue_ae (matrices point energy damping) (matrices_continuous point energy damping positive)
    (bound point damping) (matrices_bound point energy damping positive) source

def green (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumGreen point energy damping positive).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem green_fourier (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) :
    fourier (green point energy damping positive source)=momentumGreen point energy damping positive (fourier source) :=
  fourier.apply_symm_apply _

theorem green_fourier_ae (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) : fourier (green point energy damping positive source)=ᵐ[volume]
      fun frequency => diracValue point (physicalMomentum frequency) energy damping (fourier source frequency) := by
  rw [green_fourier]
  exact momentumGreen_ae point energy damping positive (fourier source)

theorem green_norm (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    ‖green point energy damping positive‖≤bound point damping := by
  apply ContinuousLinearMap.opNorm_le_bound _ (bound_nonnegative point damping positive)
  intro source
  change ‖fourier.symm (momentumGreen point energy damping positive (fourier source))‖≤_
  rw [fourier.symm.norm_map]
  exact ((momentumGreen point energy damping positive).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (multiplier_norm (matrices point energy damping)
      (matrices_continuous point energy damping positive) (bound point damping)
      (matrices_bound point energy damping positive) (bound_nonnegative point damping positive))
        (norm_nonneg _)).trans_eq (by rw [fourier.norm_map]))

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialGreen
