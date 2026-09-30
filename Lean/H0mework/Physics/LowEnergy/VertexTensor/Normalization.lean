import H0mework.Physics.LowEnergy.VertexTensor.Polynomial
import H0mework.Physics.LowEnergy.DrivenInteraction.Pairings

/-! Longitudinal vertices use the same original light legs, their own signed
time derivatives, and the unchanged physical clock. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
open LightModes LightInteraction DrivenInteraction Stage9C.Material.SpinPair Filter Topology
noncomputable section

def pairingSign (same : Bool) : ℝ := if same then 1 else -1

def transverseNumerator (same : Bool) (z : ℂ) (q : ℝ) : ℂ :=
  if same then growthNumerator z q else sourceNumerator z q

def longitudinalNumerator (same : Bool) (z : ℂ) (q : ℝ) : ℂ :=
  transverseNumerator same z q+
    (pairingSign same : ℂ)*(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
      rebuild (differenceTerms same) (z^2) ((q : ℂ)^2)

theorem longitudinal_numerator_polynomial (same : Bool) (z : ℂ) (q : ℝ) :
    longitudinalNumerator same z q=
      (pairingSign same : ℂ)*(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
        longitudinalPolynomial same (z^2) ((q : ℂ)^2) := by
  cases same <;>
    simp only [longitudinalNumerator,transverseNumerator,pairingSign,growthNumerator,sourceNumerator,
      longitudinalPolynomial,transversePolynomial,Bool.false_eq_true,↓reduceIte,
      Complex.ofReal_one,Complex.ofReal_neg,one_mul,neg_one_mul] <;> ring

theorem transverse_numerator_root (same : Bool) (q : ℝ) :
    transverseNumerator same (sourceWave .axialPhase q) q=
      (pairingSign same : ℂ)*(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
        ((q^2*transverseNormal same q : ℝ) : ℂ) := by
  cases same
  · simpa only [transverseNumerator,pairingSign,transverseNormal,Bool.false_eq_true,↓reduceIte,
      Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using source_numerator_root q
  · simpa only [transverseNumerator,pairingSign,transverseNormal,↓reduceIte,
      Complex.ofReal_one,one_mul] using growth_numerator_root q

theorem longitudinal_numerator_root (same : Bool) (q : ℝ) :
    longitudinalNumerator same (sourceWave .axialPhase q) q=
      (pairingSign same : ℂ)*(4*(sourceCoefficient .axialPhase : ℂ)^2*(responseScale : ℂ))*
        ((q^2*longitudinalNormal same q : ℝ) : ℂ) := by
  rw [longitudinalNumerator,transverse_numerator_root,source_wave_square]
  simp only [sourcePower,pow_one]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [rebuild_scaling _ (difference_admissible same)]
  rw [show (q : ℂ)^2=((q^2 : ℝ) : ℂ) by norm_cast,complexValue_real]
  simp only [longitudinalNormal,axialRoot,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_pow]
  ring

def transverseCoupling (same : Bool) (q : ℝ) : ℝ := if same then growthCoupling q else coupling q

def longitudinalCoupling (same : Bool) (q : ℝ) : ℝ :=
  responseScale*longitudinalNormal same q/(axialRoot q*(axialDerivative q)^2)

theorem transverse_coupling_normal (same : Bool) (q : ℝ) :
    transverseCoupling same q=responseScale*transverseNormal same q/(axialRoot q*(axialDerivative q)^2) := by
  cases same <;> rfl

theorem longitudinal_coupling_positive (same : Bool) (q : ℝ) (small : |q|≤ momentumRadius) :
    0<longitudinalCoupling same q :=
  div_pos (mul_pos response_scale_positive (longitudinal_normal_positive same q small))
    (mul_pos (axial_root_positive q) (sq_pos_of_pos (axial_derivative_positive q small)))

theorem longitudinal_original_residue (same : Bool) (q : ℝ) (small : |q|≤ momentumRadius) (nonzero : q≠0) :
    longitudinalNumerator same (sourceWave .axialPhase q) q/
      ((pairingSign same : ℂ)*(axialTimeDerivative q)^2)=(longitudinalCoupling same q : ℂ) := by
  rw [longitudinal_numerator_root,source_time_derivative_squared q small nonzero]
  have hn : (q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr nonzero
  have hc : (sourceCoefficient .axialPhase : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (source_coefficient_nonzero .axialPhase)
  have hr : (axialRoot q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_root_positive q).ne'
  have hd : (axialDerivative q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (axial_derivative_positive q small).ne'
  have hs : (pairingSign same : ℂ)≠0 := by cases same <;> norm_num [pairingSign]
  unfold longitudinalCoupling
  push_cast
  field_simp [hn,hc,hr,hd,hs]

def physicalTransverse (same : Bool) (q : ℝ) : ℝ := (lapse*spinScale)^2*transverseCoupling same q
def physicalLongitudinal (same : Bool) (q : ℝ) : ℝ := (lapse*spinScale)^2*longitudinalCoupling same q

theorem physical_transverse_original (same : Bool) (q : ℝ) :
    physicalTransverse same q=(if same then physicalGrowthCoupling q else physicalCoupling q) := by
  cases same <;> rfl

theorem physical_longitudinal_positive (same : Bool) (q : ℝ) (small : |q|≤ momentumRadius) :
    0<physicalLongitudinal same q :=
  mul_pos (sq_pos_of_pos (mul_pos lapse_pos spinScale_pos)) (longitudinal_coupling_positive same q small)

theorem oriented_derivative_product (first second : Bool) (q : ℝ) :
    orientedDerivative first q*orientedDerivative second q=
      (pairingSign (first==second) : ℂ)*(axialTimeDerivative q)^2 := by
  cases first <;> cases second <;>
    norm_num [orientedDerivative,growthSign,pairingSign] <;> ring

theorem longitudinal_pair_physical_residue (first second : Bool) (q : ℝ)
    (small : |q|≤ momentumRadius) (nonzero : q≠0) :
    ((lapse*spinScale : ℝ) : ℂ)^2*
      (longitudinalNumerator (first==second) (sourceWave .axialPhase q) q/
        (orientedDerivative first q*orientedDerivative second q))=
      (physicalLongitudinal (first==second) q : ℂ) := by
  rw [oriented_derivative_product,longitudinal_original_residue _ q small nonzero]
  simp only [physicalLongitudinal,Complex.ofReal_mul,Complex.ofReal_pow]

theorem longitudinal_coupling_limit (same : Bool) :
    Tendsto (longitudinalCoupling same) (𝓝 0) (𝓝 responseScale) := by
  have denom := axial_root_limit.mul (axial_derivative_limit.pow 2)
  have generated := ((longitudinal_normal_limit same).const_mul responseScale).div denom (by norm_num)
  convert! generated using 1
  simp

theorem physical_longitudinal_limit (same : Bool) :
    Tendsto (physicalLongitudinal same) (𝓝 0) (𝓝 (486*Real.sqrt 15/390625)) := by
  have generated := (longitudinal_coupling_limit same).const_mul ((lapse*spinScale)^2)
  have scale : (lapse*spinScale)^2*responseScale=486*Real.sqrt 15/390625 := by
    rw [mul_pow,lapse_sq,spinScale_sq]
    unfold responseScale
    ring
  rw [scale] at generated
  exact generated

end
end SaturationMonoid.PhysicsCore.LowEnergy.VertexTensor
