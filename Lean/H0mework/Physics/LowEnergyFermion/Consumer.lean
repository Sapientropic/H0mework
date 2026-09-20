import H0mework.Physics.LowEnergyFermion.Source

/-! A nonzero four-fermion readout of the actual full-carrier color current. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Fermion
open QuantizationCheck.Fermion DiracExteriorMatterAction StageNineFullDiracAdjointMaterial
open Stage9C.Material.SpinPair Stage9C.Dynamics.Homogeneous
open DiracCliffordRepresentation ProofFreeRicherAnholonomicSource
open scoped BigOperators Matrix
noncomputable section
attribute [local instance] fullIndexOrder

theorem canonical_modePair (action : Module.End ℂ DiracExteriorMatterCarrier)
    (left right : DiracExteriorMatterCarrier) :
    modePair (Quantum.coordinates left)
      (Quantum.operatorMatrix (Quantum.spinExchange.comp action) *ᵥ Quantum.coordinates right) =
      fullCanonicalDiracAdjoint left (action right) := by
  rw [Quantum.matrix_action, Quantum.canonicalDual_full_response, Quantum.spinExchange_selfAdjoint]
  rfl

theorem realVertex_pair (density : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier)
    (left right : DiracExteriorMatterCarrier) :
    modePair (Quantum.coordinates left) (realVertex density action *ᵥ Quantum.coordinates right) =
      ((density : ℂ)/2) * (fullCanonicalDiracAdjoint left (action right) +
        star (fullCanonicalDiracAdjoint right (action left))) := by
  rw [realVertex, Matrix.smul_mulVec, modePair_smul_right, hermitianPart,
    Matrix.smul_mulVec, modePair_smul_right, Matrix.add_mulVec, modePair_add_right,
    modePair_conjTranspose, canonical_modePair, canonical_modePair]
  ring

theorem spinPairDual_full (p q u v : ℂ) :
    spinPairDual p q (spinPairMatter u v) = 2*(p*u+q*v) := by
  change (∑ spin, ∑ state, spinPairCoefficients p q spin state *
    sourceColorDoubletDual state (sourceColorDiracMatter (spinPairCoefficients u v) spin)) = _
  simp only [sourceColorDoubletDual_diracMatter]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

theorem source_color_response (axis : Fin 3) (a b c d : ℂ) :
    fullCanonicalDiracAdjoint (spinPairMatter a b)
      (Exchange.currentOperator (actual.coframe 0) axis.succ (sourceColorP286Generator axis)
        (spinPairMatter c d)) = star a*c+star b*d := by
  rw [Quantum.canonicalDual_pair]
  unfold Exchange.currentOperator
  rw [actual_coframe, homogeneousInverseGamma lapse (ne_of_gt lapse_pos)]
  simp only [Fin.succ_ne_zero, ↓reduceIte, one_smul, LinearMap.smul_apply,
    LinearMap.comp_apply, map_smul, smul_eq_mul, spinPairDual_generatorKinetic]
  rw [spinPairDual_full]
  ring_nf
  simp [Complex.I_sq]

theorem source_color_realVertex (axis : Fin 3) (density : ℝ) (a b c d : ℂ) :
    modePair (Quantum.coordinates (spinPairMatter a b))
      (currentVertex (actual.coframe 0) density axis.succ (sourceColorP286Generator axis) *ᵥ
        Quantum.coordinates (spinPairMatter c d)) =
      ((lapse*density : ℝ) : ℂ)*(star a*c+star b*d) := by
  rw [currentVertex, Matrix.smul_mulVec, modePair_smul_right, realVertex_pair,
    source_color_response, source_color_response, actual_coframe, homogeneousCoframe_det,
    abs_of_pos lapse_pos]
  simp only [star_add, star_mul, star_star]
  push_cast
  ring

theorem spinPair_coordinatePair (a b c d : ℂ) :
    Quantum.coordinatePair (spinPairMatter a b) (spinPairMatter c d) =
      2*(star a*c+star b*d) := by
  have identity := Quantum.canonicalDual_full_response (spinPairMatter b a) (spinPairMatter c d)
  rw [Quantum.canonicalDual_pair, Quantum.spinExchange_pair] at identity
  rw [← identity]
  exact spinPairDual_full _ _ _ _

def sourceDoubleOccupation : Fock Quantum.Index := sourcePair (spinPairMatter 1 0) (spinPairMatter 0 1)

theorem sourceDoubleOccupation_norm : pairing sourceDoubleOccupation sourceDoubleOccupation = 4 := by
  unfold sourceDoubleOccupation sourcePair
  rw [pairing_twoParticle]
  change Quantum.coordinatePair (spinPairMatter 1 0) (spinPairMatter 1 0) *
    Quantum.coordinatePair (spinPairMatter 0 1) (spinPairMatter 0 1) -
      Quantum.coordinatePair (spinPairMatter 1 0) (spinPairMatter 0 1) *
        Quantum.coordinatePair (spinPairMatter 0 1) (spinPairMatter 1 0) = 4
  norm_num [spinPair_coordinatePair]

theorem sourceDoubleOccupation_nonzero : sourceDoubleOccupation ≠ 0 := by
  intro zero
  have identity := sourceDoubleOccupation_norm
  rw [zero] at identity
  norm_num [pairing] at identity

theorem actual_color_fourFermion (first second : Fin 3) :
    pairing sourceDoubleOccupation
      (normalProduct
        (currentVertex (actual.coframe 0) spinScale first.succ (sourceColorP286Generator first))
        (currentVertex (actual.coframe 0) spinScale second.succ (sourceColorP286Generator second))
        sourceDoubleOccupation) = 216/125 := by
  unfold sourceDoubleOccupation sourcePair
  rw [normalProduct_matrixElement]
  simp only [source_color_realVertex, star_one, star_zero, mul_one, mul_zero,
    zero_add, add_zero, sub_zero]
  have lapse_square : ((lapse : ℝ) : ℂ)^2 = 54/125 := by
    rw [← Complex.ofReal_pow, lapse_sq]
    norm_num
  have spin_square : ((spinScale : ℝ) : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow, spinScale_sq]
    norm_num
  push_cast
  calc
    _ = 2*(lapse : ℂ)^2*(spinScale : ℂ)^2 := by ring
    _ = _ := by rw [lapse_square, spin_square]; norm_num

def normalizedDoubleOccupation : Fock Quantum.Index := (1/2 : ℂ) • sourceDoubleOccupation

theorem normalizedDoubleOccupation_norm : pairing normalizedDoubleOccupation normalizedDoubleOccupation = 1 := by
  rw [normalizedDoubleOccupation, pairing_smul_left, pairing_smul_right, sourceDoubleOccupation_norm]
  norm_num

theorem actual_color_fourFermion_normalized (first second : Fin 3) :
    pairing normalizedDoubleOccupation
      (normalProduct
        (currentVertex (actual.coframe 0) spinScale first.succ (sourceColorP286Generator first))
        (currentVertex (actual.coframe 0) spinScale second.succ (sourceColorP286Generator second))
        normalizedDoubleOccupation) = 54/125 := by
  rw [normalizedDoubleOccupation, map_smul, pairing_smul_left, pairing_smul_right, actual_color_fourFermion]
  norm_num

end
end SaturationMonoid.PhysicsCore.LowEnergy.Fermion
