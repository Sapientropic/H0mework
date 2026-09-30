import H0mework.Physics.LowEnergy.LightInteraction.Normalization

/-! A source cubic between the two reciprocal actual light poles has a
true double-pole coefficient. The reciprocal-leg orientation is explicit. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
open LightModes Filter Topology
noncomputable section

theorem double_pole_limit (f g : ℂ → ℂ) (point d : ℂ)
    (derivative : HasDerivAt f d point) (root : f point=0) (simple : d≠0)
    (regular : ContinuousAt g point) :
    Tendsto (fun z => (z-point)^2*(g z/(f z)^2)) (𝓝[≠] point) (𝓝 (g point/d^2)) := by
  have first := simple_pole_residue f g point d derivative root simple regular
  have second := simple_pole_residue f (fun _ => 1) point d derivative root simple continuousAt_const
  have generated := first.mul second
  convert! generated using 1
  · funext z
    simp only [div_eq_mul_inv,pow_two,mul_inv_rev,one_mul]
    ring
  · simp only [div_eq_mul_inv,pow_two,mul_inv_rev,one_mul]
    ring

def sourceFormFactor (z : ℂ) (q : ℝ) : ℂ :=
  sourceNumerator z q/(sourceFactor .axialPhase (z^2) ((q : ℂ)^2))^2

theorem source_numerator_continuous (q : ℝ) : Continuous (fun z : ℂ => sourceNumerator z q) := by
  unfold sourceNumerator sourcePolynomial
  generalize responseTerms=terms
  apply Continuous.mul continuous_const
  exact (continuous_pow 2).add
    ((rebuild_continuous terms).comp ((continuous_pow 2).prodMk continuous_const))

theorem generated_double_pole (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    Tendsto (fun z : ℂ => (z-sourceWave .axialPhase q)^2*sourceFormFactor z q)
      (𝓝[≠] (sourceWave .axialPhase q)) (𝓝 (-(coupling q : ℂ))) ∧
    coupling q≠0 := by
  have generated := source_complex_simple .axialPhase q small nonzero
  constructor
  · have pole := double_pole_limit
      (fun z => sourceFactor .axialPhase (z^2) ((q : ℂ)^2))
      (fun z => sourceNumerator z q) (sourceWave .axialPhase q) (axialTimeDerivative q)
      generated.1 (source_wave_on_shell .axialPhase q small) generated.2
      (source_numerator_continuous q).continuousAt
    rw [original_double_residue q small nonzero] at pole
    exact pole
  · exact (coupling_positive q small).ne'

def reverseDerivative (q : ℝ) : ℂ :=
  (complexSquaredPolynomial .axialPhase (q^2)).derivative.eval ((-sourceWave .axialPhase q)^2)*
    (2*(-sourceWave .axialPhase q))

theorem reciprocal_orientation (q : ℝ) : reverseDerivative q= -axialTimeDerivative q := by
  unfold reverseDerivative axialTimeDerivative
  rw [neg_sq]
  ring

theorem generated_reciprocal_residue (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    sourceNumerator (sourceWave .axialPhase q) q/(axialTimeDerivative q*reverseDerivative q)=
      (coupling q : ℂ) := by
  rw [reciprocal_orientation,mul_neg,div_neg,← pow_two,original_double_residue q small nonzero,neg_neg]

def physicalCoupling (q : ℝ) : ℝ :=
  (Stage9C.Material.SpinPair.lapse*Real.sqrt 2)^2*coupling q

theorem physical_coupling_positive (q : ℝ) (small : |q| ≤ momentumRadius) : 0<physicalCoupling q := by
  unfold physicalCoupling
  exact mul_pos (sq_pos_of_pos (mul_pos Stage9C.Material.SpinPair.lapse_pos (by positivity)))
    (coupling_positive q small)

theorem original_time_coupling_limit :
    Tendsto physicalCoupling (𝓝 0) (𝓝 (486*Real.sqrt 15/390625)) := by
  have generated := coupling_limit.const_mul ((Stage9C.Material.SpinPair.lapse*Real.sqrt 2)^2)
  have scale : (Stage9C.Material.SpinPair.lapse*Real.sqrt 2)^2*responseScale=
      486*Real.sqrt 15/390625 := by
    rw [mul_pow,Stage9C.Material.SpinPair.lapse_sq,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
    unfold responseScale
    ring
  rw [scale] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.LightInteraction
