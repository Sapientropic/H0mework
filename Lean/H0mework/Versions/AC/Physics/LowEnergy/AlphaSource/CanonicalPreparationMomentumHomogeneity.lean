import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationMomentumSymbol
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory Filter Set
open scoped ContDiff Topology SchwartzMap
attribute [local irreducible] b1 symbolSlice jointSymbol

def momentumSlice (x : PhysicalMomentum) (p : PhysicalMomentum) : ℂ := symbolSlice p x

theorem momentumSlice_smooth (x : PhysicalMomentum) : ContDiff ℝ ∞ (momentumSlice x) := by
  have same : momentumSlice x=(fun p : PhysicalMomentum => jointSymbol (x,p)) := by
    funext p
    simp only [momentumSlice,jointSymbol]
  rw [same]
  exact jointSymbol_smooth.comp
    (show ContDiff ℝ ∞ (fun p : PhysicalMomentum => (x,p)) from contDiff_const.prodMk contDiff_id)

theorem source_radial_plateau (p : PhysicalMomentum) (high : 1 ≤ ‖p‖) : radialRoot p=1 := by
  rw [radialRoot,sourceChi,if_neg (by linarith),if_pos (by linarith)]
  norm_num

theorem unitMomentum_positive_smul (p : PhysicalMomentum) (a : ℝ)
    (positive : 0<a) (nonzero : p≠0) : unitMomentum (a • p)=unitMomentum p := by
  rw [unitMomentum,unitMomentum,norm_smul,Real.norm_eq_abs,abs_of_pos positive,smul_smul]
  congr 1
  field_simp [positive.ne',norm_ne_zero_iff.mpr nonzero]

theorem source_high_homothety (x p : PhysicalMomentum) (a : ℝ)
    (positive : 0<a) (high : 1≤‖p‖) (scaledHigh : 1≤‖a • p‖) :
    momentumSlice x (a • p)=a • momentumSlice x p := by
  have nonzero : p≠0 := by intro zero; simp only [zero,norm_zero] at high; linarith
  have scaledNonzero : a • p≠0 := smul_ne_zero positive.ne' nonzero
  unfold momentumSlice
  rw [symbolSlice_radial (a • p) scaledNonzero,symbolSlice_radial p nonzero,
    unitMomentum_positive_smul p a positive nonzero,source_radial_plateau p high,
    source_radial_plateau (a • p) scaledHigh]
  simp only [Pi.smul_apply,smul_eq_mul,norm_smul,Real.norm_eq_abs,abs_of_pos positive,
    mul_one,Complex.ofReal_mul,Complex.real_smul]
  ring

theorem source_high_homothety_germ (x p : PhysicalMomentum) (a : ℝ)
    (positive : 0<a) (high : 1<‖p‖) (scaledHigh : 1<‖a • p‖) :
    (fun q : PhysicalMomentum => momentumSlice x (a • q))=ᶠ[𝓝 p]
      (fun q : PhysicalMomentum => a • momentumSlice x q) := by
  have nearby : ∀ᶠ q : PhysicalMomentum in 𝓝 p,1<‖q‖ :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds high
  have scaledNearby : ∀ᶠ q : PhysicalMomentum in 𝓝 p,1<‖a • q‖ :=
    (isOpen_lt continuous_const (continuous_id.const_smul a).norm).mem_nhds scaledHigh
  filter_upwards [nearby,scaledNearby] with q hq haq
  exact source_high_homothety x q a positive hq.le haq.le

theorem momentum_derivative_homothety (j : ℕ) (x p : PhysicalMomentum) (a : ℝ)
    (positive : 0<a) (high : 1<‖p‖) (scaledHigh : 1<‖a • p‖) :
    a^j • iteratedFDeriv ℝ j (momentumSlice x) (a • p)=
      a • iteratedFDeriv ℝ j (momentumSlice x) p := by
  have smooth : ContDiff ℝ (j : ℕ∞ω) (momentumSlice x) := (momentumSlice_smooth x).of_le
    (by exact_mod_cast (le_top : (j : ℕ∞)≤⊤))
  have derivative := ((source_high_homothety_germ x p a positive high scaledHigh).iteratedFDeriv ℝ j).eq_of_nhds
  rw [iteratedFDeriv_comp_const_smul a smooth] at derivative
  rw [iteratedFDeriv_const_smul_apply' smooth.contDiffAt] at derivative
  exact derivative

end LowEnergy.PreparationMomentumSymbol
