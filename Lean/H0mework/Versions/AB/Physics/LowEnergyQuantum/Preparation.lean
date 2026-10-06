import H0mework.Versions.AB.Physics.LowEnergyQuantum.Carrier
import H0mework.Physics.SpinPair.Adjoint

/-! The native full-matter pairing and the actually prepared independent
dual. The spin exchange remains explicit in the quantum response. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Quantum
open DiracCliffordRepresentation DiracExteriorMatterAction SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction SU7ExteriorBreakingYukawa Stage9C.Material.SpinPair
open StageNineFullDiracAdjointMaterial
open scoped Matrix
noncomputable section

def coordinatePair (left right : DiracExteriorMatterCarrier) : ℂ :=
  ∑ index, star (coordinates left index)*coordinates right index

theorem coordinatePair_full (left right : DiracExteriorMatterCarrier) :
    coordinatePair left right = ∑ spin, fullInternalPair (left spin) (right spin) := by
  simp [coordinatePair, coordinates, wholeBasis, internalBasis, Module.Basis.equivFun_apply,
    Pi.basis_repr, Fintype.sum_sigma, Fintype.sum_sum_type, fullInternalPair, exteriorCoordinatePair, ← add_assoc]

theorem coordinatePair_spinPair (u v : ℂ) :
    coordinatePair (spinPairMatter u v) (spinPairMatter u v) =
      2*(star u*u+star v*v) := by
  rw [coordinatePair_full]
  unfold spinPairMatter
  simp only [sourceColorDiracMatter, fullInternalPair_colorLinear]
  change (∑ spin, ∑ state, star (spinPairCoefficients u v spin state)*
    sourceColorDoubletDual state (sourceColorDiracMatter (spinPairCoefficients u v) spin)) = _
  simp only [sourceColorDoubletDual_diracMatter]
  simp [spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

def spinExchange : Module.End ℂ DiracExteriorMatterCarrier :=
  diracMatrixMatterAction diracAdjointSpinSwap

theorem spinExchange_pair (u v : ℂ) : spinExchange (spinPairMatter u v) = spinPairMatter v u := by
  unfold spinExchange spinPairMatter
  rw [sourceColorDiracMatter_matrix]
  congr 1
  funext spin state
  fin_cases spin <;> fin_cases state <;> simp [diracAdjointSpinSwap, spinPairCoefficients, Fin.sum_univ_four]

theorem canonicalDual_pair (u v : ℂ) :
    fullCanonicalDiracAdjoint (spinPairMatter u v) = spinPairDual (star v) (star u) := by
  apply LinearMap.ext
  intro test
  change (∑ spin, fullInternalPair (spinExchange (spinPairMatter u v) spin) (test spin)) = _
  rw [spinExchange_pair]
  simp only [spinPairMatter, sourceColorDiracMatter, fullInternalPair_colorLinear]
  simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]

theorem canonicalDual_full_response (matter test : DiracExteriorMatterCarrier) :
    fullCanonicalDiracAdjoint matter test = coordinatePair (spinExchange matter) test := by
  rw [coordinatePair_full]
  rfl

theorem spinExchange_selfAdjoint (left right : DiracExteriorMatterCarrier) :
    coordinatePair (spinExchange left) right = coordinatePair left (spinExchange right) := by
  rw [coordinatePair_full, coordinatePair_full]
  simp [spinExchange, diracMatrixMatterAction, diracAdjointSpinSwap, Fin.sum_univ_four]
  ring

theorem coordinatePair_smul (coefficient : ℂ) (left right : DiracExteriorMatterCarrier) :
    coordinatePair (coefficient • left) (coefficient • right) =
      (star coefficient*coefficient)*coordinatePair left right := by
  simp only [coordinatePair, map_smul, Pi.smul_apply, smul_eq_mul, star_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

def phase (angle : ℝ) : ℂ := Complex.exp (Complex.I*(angle : ℂ))

theorem phase_star (angle : ℝ) : star (phase angle) = phase (-angle) := by
  change starRingEnd ℂ (Complex.exp _) = _
  rw [← Complex.exp_conj]
  simp [phase]

theorem phase_opposite (angle : ℝ) : phase (-angle)*phase angle = 1 := by
  rw [phase, phase, ← Complex.exp_add]
  simp

def preparedSpinor (amplitude angle : ℝ) : DiracExteriorMatterCarrier :=
  spinPairMatter ((amplitude : ℂ)*phase angle) ((amplitude : ℂ)*phase (-angle))

private theorem star_real (r : ℝ) : star (r : ℂ) = (r : ℂ) := by simp

theorem prepared_pair (amplitude angle : ℝ) :
    coordinatePair (preparedSpinor amplitude angle) (preparedSpinor amplitude angle) =
      ((4*amplitude^2 : ℝ) : ℂ) := by
  rw [preparedSpinor, coordinatePair_spinPair]
  simp only [star_mul, star_real, phase_star, neg_neg]
  have first := phase_opposite angle
  have second := phase_opposite (-angle)
  simp only [neg_neg] at second
  push_cast
  linear_combination 2*(amplitude : ℂ)^2*first+2*(amplitude : ℂ)^2*second

theorem prepared_unit (angle : ℝ) :
    coordinatePair (preparedSpinor (1/2) angle) (preparedSpinor (1/2) angle) = 1 := by
  rw [prepared_pair]
  norm_num

theorem prepared_normalization (amplitude angle : ℝ) :
    preparedSpinor amplitude angle = (2*(amplitude : ℂ)) • preparedSpinor (1/2) angle := by
  unfold preparedSpinor spinPairMatter
  rw [← sourceColorDiracMatter_smul]
  congr 1
  funext spin state
  simp only [Pi.smul_apply, smul_eq_mul]
  fin_cases spin <;> fin_cases state <;> simp [spinPairCoefficients] <;> ring

theorem prepared_dual (density amplitude angle : ℝ) :
    spinPairDual ((density : ℂ)*(amplitude : ℂ)*phase angle)
      ((density : ℂ)*(amplitude : ℂ)*phase (-angle)) =
      (density : ℂ) • fullCanonicalDiracAdjoint (preparedSpinor amplitude angle) := by
  rw [preparedSpinor, canonicalDual_pair]
  simp only [star_mul, star_real, phase_star, neg_neg]
  apply LinearMap.ext
  intro test
  simp [spinPairDual, sourceColorDiracDual, spinPairCoefficients, Fin.sum_univ_four, Fin.sum_univ_two]
  ring

def normalizedRead (angle : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier) : ℂ :=
  ∑ index, star (coordinates (preparedSpinor (1/2) angle) index) *
    (operatorMatrix (spinExchange.comp action) *ᵥ coordinates (preparedSpinor (1/2) angle)) index

theorem prepared_response (density amplitude angle : ℝ) (action : Module.End ℂ DiracExteriorMatterCarrier) :
    spinPairDual ((density : ℂ)*(amplitude : ℂ)*phase angle)
      ((density : ℂ)*(amplitude : ℂ)*phase (-angle)) (action (preparedSpinor amplitude angle)) =
      ((4*density*amplitude^2 : ℝ) : ℂ)*normalizedRead angle action := by
  rw [prepared_dual]
  change (density : ℂ)*fullCanonicalDiracAdjoint (preparedSpinor amplitude angle)
    (action (preparedSpinor amplitude angle)) = _
  rw [canonicalDual_full_response, spinExchange_selfAdjoint,
    prepared_normalization amplitude angle, map_smul, map_smul, coordinatePair_smul]
  unfold normalizedRead
  rw [matrix_action]
  change _ = ((4*density*amplitude^2 : ℝ) : ℂ)*coordinatePair (preparedSpinor (1/2) angle)
    (spinExchange (action (preparedSpinor (1/2) angle)))
  simp only [star_mul, star_ofNat, star_real]
  push_cast
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.Quantum
