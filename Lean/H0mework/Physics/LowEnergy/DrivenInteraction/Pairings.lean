import H0mework.Physics.LowEnergy.DrivenInteraction.Normalization

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
open LightModes LightInteraction Stage9C.Material.SpinPair Filter Topology
noncomputable section

def growthSign (positive : Bool) : ℂ := if positive then 1 else -1
def orientedDerivative (positive : Bool) (q : ℝ) : ℂ := growthSign positive*axialTimeDerivative q
def pairNumerator (first second : Bool) (z : ℂ) (q : ℝ) : ℂ :=
  if first=second then growthNumerator z q else sourceNumerator z q
def pairCoupling (first second : Bool) (q : ℝ) : ℝ :=
  if first=second then physicalGrowthCoupling q else physicalCoupling q

theorem pair_u_residue (first second : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    pairNumerator first second (sourceWave .axialPhase q) q/
      (orientedDerivative first q*orientedDerivative second q)=
        ((if first=second then growthCoupling q else coupling q : ℝ) : ℂ) := by
  cases first <;> cases second <;>
    simp only [pairNumerator,orientedDerivative,growthSign,Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,
      one_mul,mul_neg,neg_mul,div_neg,← pow_two,neg_sq,
      original_growth_residue q small nonzero,original_double_residue q small nonzero,neg_neg]

theorem pair_physical_residue (first second : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) (nonzero : q≠0) :
    ((lapse*spinScale : ℝ) : ℂ)^2*
      (pairNumerator first second (sourceWave .axialPhase q) q/
        (orientedDerivative first q*orientedDerivative second q))=(pairCoupling first second q : ℂ) := by
  rw [pair_u_residue first second q small nonzero]
  cases first <;> cases second <;>
    simp [pairCoupling,physicalGrowthCoupling,physicalCoupling,spinScale]

theorem pair_coupling_positive (first second : Bool) (q : ℝ) (small : |q| ≤ momentumRadius) :
    0<pairCoupling first second q := by
  unfold pairCoupling
  split
  · exact physical_growth_coupling_positive q small
  · exact physical_coupling_positive q small

theorem pair_coupling_limit (first second : Bool) :
    Tendsto (pairCoupling first second) (𝓝 0) (𝓝 (486*Real.sqrt 15/390625)) := by
  unfold pairCoupling
  split
  · exact physical_growth_coupling_limit
  · exact original_time_coupling_limit

end
end SaturationMonoid.PhysicsCore.LowEnergy.DrivenInteraction
