import H0mework.Physics.LowEnergy.LightModes.Source
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.Basic

/-! The roots generated from the four full source factors produce actual
complex time exponents in the original fixed axial momentum chart. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightModes
open Filter Topology
noncomputable section

theorem root_sign (branch : Branch) (w : ℝ) :
    (branch=.axialPhase → 0<(sourceRoot branch).root w) ∧
    (branch≠.axialPhase → (sourceRoot branch).root w<0) := by
  have bounds := (sourceRoot branch).root_in_window w
  cases branch <;> simp only [sourceRoot,Set.mem_Icc] at bounds ⊢
  all_goals constructor
  all_goals intro h
  all_goals first | contradiction | linarith [bounds.1,bounds.2]

def sourceWave (branch : Branch) (q : ℝ) : ℂ :=
  if branch=.axialPhase then (q^(sourcePower branch)*Real.sqrt ((sourceRoot branch).root (q^2)) : ℝ)
  else Complex.I*(q^(sourcePower branch)*Real.sqrt (-(sourceRoot branch).root (q^2)) : ℝ)

theorem source_wave_square (branch : Branch) (q : ℝ) :
    (sourceWave branch q)^2=((q^2)^(sourcePower branch)*(sourceRoot branch).root (q^2) : ℝ) := by
  have power : (q^(sourcePower branch))^2=(q^2)^(sourcePower branch) := by
    rw [← pow_mul,← pow_mul,Nat.mul_comm]
  by_cases axial : branch=.axialPhase
  · have positive := (root_sign branch (q^2)).1 axial
    simp only [sourceWave,if_pos axial,← Complex.ofReal_pow,mul_pow,Real.sq_sqrt positive.le,power]
  · have negative := (root_sign branch (q^2)).2 axial
    simp only [sourceWave,if_neg axial,mul_pow,Complex.I_sq,← Complex.ofReal_pow,
      Real.sq_sqrt (neg_nonneg.mpr negative.le),power]
    push_cast
    ring

theorem source_wave_nonzero (branch : Branch) (q : ℝ) (nonzero : q≠0) : sourceWave branch q≠0 := by
  have rootNonzero : (sourceRoot branch).root (q^2)≠0 := by
    by_cases axial : branch=.axialPhase
    · exact ((root_sign branch (q^2)).1 axial).ne'
    · exact ((root_sign branch (q^2)).2 axial).ne
  intro zero
  have square := source_wave_square branch q
  rw [zero,zero_pow (by decide)] at square
  have product := Complex.ofReal_eq_zero.mp square.symm
  exact mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ nonzero)) rootNonzero product

theorem source_factor_cast (branch : Branch) (v w : ℝ) :
    sourceFactor branch (v : ℂ) (w : ℂ)=(sourceFactor branch v w : ℝ) := by
  cases branch <;> simp [sourceFactor]

theorem source_wave_on_shell (branch : Branch) (q : ℝ) (small : |q|≤momentumRadius) :
    sourceFactor branch ((sourceWave branch q)^2) ((q : ℂ)^2)=0 := by
  rw [source_wave_square,← Complex.ofReal_pow,source_factor_cast]
  rw [source_factor_root branch (q^2) (momentum_root_domain branch q small),Complex.ofReal_zero]

theorem source_wave_squared_ratio (branch : Branch) (q : ℝ) (nonzero : q≠0) :
    (sourceWave branch q)^2/(q : ℂ)^(2*sourcePower branch)=((sourceRoot branch).root (q^2) : ℝ) := by
  rw [source_wave_square]
  push_cast
  rw [← pow_mul]
  field_simp [Complex.ofReal_ne_zero.mpr nonzero]

theorem source_wave_leading (branch : Branch) :
    Tendsto (fun q : ℝ => (sourceWave branch q)^2/(q : ℂ)^(2*sourcePower branch))
      (𝓝[≠] 0) (𝓝 ((sourceRoot branch).center : ℂ)) := by
  have square : Tendsto (fun q : ℝ => q^2) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_pow 2).tendsto (0 : ℝ)
  have root := (sourceRoot branch).root_limit.comp square
  have cast := (Complex.continuous_ofReal.tendsto ((sourceRoot branch).center)).comp root
  have generated := cast.mono_left (show 𝓝[≠] (0 : ℝ)≤𝓝 0 from inf_le_left)
  apply generated.congr'
  filter_upwards [self_mem_nhdsWithin] with q nonzero
  exact (source_wave_squared_ratio branch q (by simpa using nonzero)).symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightModes
