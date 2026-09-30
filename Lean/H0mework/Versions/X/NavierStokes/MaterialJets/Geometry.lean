import H0mework.Versions.X.NavierStokes.ConstitutiveAction.MaterialEnergy

set_option autoImplicit false
open scoped Matrix BigOperators Matrix.Norms.Elementwise

namespace SaturationMonoid.NavierStokes.NativeGeometricMaterial

open PhysicsCore DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair StageNineP286GaugeConnectionVariationDensity StageNineCoframeLocalDifferentiability
open ThreeDimensionalPeriodicCoarseFilterCore
open NativePauliControl NativePauliMotherAction NativePauliCoframeAction NativeCartanClifford
open NativeCartanConstitutive NativeBalancedGaugeEnergy NativeBalancedJetCoefficients

noncomputable section

theorem energy_nonnegative (block : Block) : 0 ≤ energy block :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem energy_add_le (first second : Block) : energy (first + second) ≤ 2 * energy first + 2 * energy second := by
  have parallelogram : energy (first + second) + energy (first - second) = 2 * energy first + 2 * energy second := by
    simp [energy, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Fin.sum_univ_two]
    ring
  linarith [energy_nonnegative (first - second)]

theorem energy_complex_smul (scalar : ℂ) (block : Block) : energy (scalar • block) = Complex.normSq scalar * energy block := by
  simp [energy, Complex.normSq_mul, Fin.sum_univ_two]
  ring

theorem tangent_energy (tangent : Vector) : energy (NativePauliJet.tangent tangent) = 2 * squared tangent := by
  simp [energy, NativePauliJet.tangent, pauli, squared, Fin.sum_univ_two, Fin.sum_univ_three,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem leftPauli_energy (velocity tangent : Vector) :
    energy (blockAction (NativePauliJet.tangent tangent) (hermitianBlock velocity)) =
      NativePauliJet.density velocity * squared tangent := by
  simp [energy, blockAction, NativePauliJet.tangent, hermitianBlock, pauli, squared, NativePauliJet.density,
    Fin.sum_univ_two, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem spinAction_energy (velocity : Vector) (direction : Fin 3) :
    energy (spinAction (hermitianBlock velocity) direction.succ) = NativePauliJet.density velocity := by
  fin_cases direction <;>
    simp [energy, spinAction, spinPrincipal, hermitianBlock, pauli, NativePauliJet.density,
      Fin.sum_univ_two, Fin.sum_univ_three, Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

def rotation (z : Fin 4 → ℝ) : Fin 3 → Vector :=
  !![0, z 3 / 2, -z 2 / 2;
     -z 3 / 2, 0, z 1 / 2;
     z 2 / 2, -z 1 / 2, 0]

def spinBlock (density : ℝ) (z : Fin 4 → ℝ) (block : Block) (direction : Fin 3) : Block :=
  ((-z 0 / (2 * density) : ℝ) : ℂ) • spinAction block direction.succ +
    Complex.I • blockAction (NativePauliJet.tangent (rotation z direction)) block

/-- Full-carrier restriction of the actual Levi–Civita spin lift. -/
theorem spinLift_block (density : ℝ) (z : Fin 4 → ℝ) (block : Block) (direction : Fin 3) :
    diracMatrixMatterAction (NativeCoframeSpin.spinLiftFormula density z direction.succ) (lowerMatter block) =
      lowerMatter (spinBlock density z block direction) := by
  have first := bivector_action 0 block
  have second := bivector_action 1 block
  have third := bivector_action 2 block
  have fourth := bivector_action 3 block
  have fifth := bivector_action 4 block
  have sixth := bivector_action 5 block
  dsimp only [lorentzBivectorFirst, lorentzBivectorSecond] at first second third fourth fifth sixth
  simp only [Matrix.cons_val] at first second third fourth fifth sixth
  fin_cases direction
  case' «0» =>
    change diracMatrixMatterAction (NativeCoframeSpin.spinLiftFormula density z 1) (lowerMatter block) =
      lowerMatter (spinBlock density z block 0)
  case' «1» =>
    change diracMatrixMatterAction (NativeCoframeSpin.spinLiftFormula density z 2) (lowerMatter block) =
      lowerMatter (spinBlock density z block 1)
  case' «2» =>
    change diracMatrixMatterAction (NativeCoframeSpin.spinLiftFormula density z 3) (lowerMatter block) =
      lowerMatter (spinBlock density z block 2)
  all_goals
    dsimp only [NativeCoframeSpin.spinLiftFormula]
    simp only [Matrix.cons_val]
    simp only [
      coframeDiracMatrixMatterAction_add_matrix, coframeDiracMatrixMatterAction_smul_matrix,
      StageNineDiracMatterCoordinateCalculus.diracMatrixMatterAction_sub_matrix,
      first, second, third, fourth, fifth, sixth]
  all_goals
    simp only [← map_smul, ← map_add, ← map_sub]
    congr 1
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [spinBlock, spinAction, spinPrincipal, blockAction, NativePauliJet.tangent, rotation,
        bivectorBlock, pauli, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring_nf <;> simp <;> ring

def spatialBlock (velocity : Vector) (derivative : Fin 4 → Vector) (direction : Fin 3) : Block :=
  spinBlock (NativePauliJet.density velocity) (NativePauliJet.logDerivative velocity derivative) (hermitianBlock velocity) direction

theorem source_increment (velocity : PhysicalSpace) (derivative : Fin 4 → PhysicalSpace) (direction : Fin 3) :
    diracMatrixMatterAction (diracSpinConnectionLift
      (NativeMaterialJetAction.geometry velocity derivative).lorentzSpinConnection direction.succ)
        (NativeCanonicalFluidCoframe.matter velocity) =
      lowerMatter (spatialBlock (normalizedVelocity velocity) (NativeMaterialJetAction.normalizedJet derivative) direction) := by
  rw [NativeMaterialJetAction.geometry, NativeCoframeSpin.jet_connection, NativeCoframeSpin.spinLift_eq,
    source_matter, NativeMaterialJetAction.source_density, spinLift_block]
  rfl

theorem spinBlock_energy_bound (velocity : Vector) (z : Fin 4 → ℝ) (direction : Fin 3) :
    energy (spinBlock (NativePauliJet.density velocity) z (hermitianBlock velocity) direction) ≤
      2 * (-z 0 / (2 * NativePauliJet.density velocity)) ^ 2 * NativePauliJet.density velocity +
        2 * NativePauliJet.density velocity * squared (rotation z direction) := by
  apply (energy_add_le _ _).trans_eq
  rw [energy_smul, spinAction_energy, energy_complex_smul, leftPauli_energy]
  simp only [Complex.normSq_I, one_mul]
  ring

theorem rotation_energy (z : Fin 4 → ℝ) :
    (∑ direction, squared (rotation z direction)) = (∑ direction : Fin 3, z direction.succ ^ 2) / 2 := by
  simp [rotation, squared, Fin.sum_univ_three]
  ring

theorem log_energy_bound (velocity : Vector) (derivative : Fin 4 → Vector) (direction : Fin 4) :
    NativePauliJet.density velocity * NativePauliJet.logDerivative velocity derivative direction ^ 2 ≤
      8 / 9 * squared (derivative direction) := by
  have cauchy : pairing velocity (derivative direction) ^ 2 ≤ squared velocity * squared (derivative direction) := by
    have cross : 0 ≤ squared (crossProduct velocity (derivative direction)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have identity : squared (crossProduct velocity (derivative direction)) = squared velocity * squared (derivative direction) -
        pairing velocity (derivative direction) ^ 2 := by
      simp [squared, pairing, cross_apply, Fin.sum_univ_three]
      ring
    rw [identity] at cross
    linarith
  have nonnegative : 0 ≤ squared (derivative direction) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have value : NativePauliJet.density velocity * NativePauliJet.logDerivative velocity derivative direction ^ 2 =
      16 * pairing velocity (derivative direction) ^ 2 / (9 * NativePauliJet.density velocity) := by
    unfold NativePauliJet.logDerivative pairing
    field_simp [(NativePauliJet.density_pos velocity).ne']
    ring
  rw [value]
  apply (div_le_iff₀ (mul_pos (by norm_num) (NativePauliJet.density_pos velocity))).2
  change _ ≤ _ * (9 * (2 * (1 + squared velocity)))
  nlinarith

theorem spatial_energy_bound (velocity : Vector) (derivative : Fin 4 → Vector) :
    (∑ direction, energy (spatialBlock velocity derivative direction)) ≤ ∑ direction, squared (derivative direction) := by
  let z := NativePauliJet.logDerivative velocity derivative
  have positive := NativePauliJet.density_pos velocity
  have densityLarge : 2 ≤ NativePauliJet.density velocity := by
    unfold NativePauliJet.density
    have nonnegative : 0 ≤ ∑ index, velocity index ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  have temporal : 3 * (2 * (-z 0 / (2 * NativePauliJet.density velocity))^2 * NativePauliJet.density velocity) ≤
      NativePauliJet.density velocity * z 0 ^ 2 := by
    field_simp
    have payment := mul_nonneg (show 0 ≤ 2 * NativePauliJet.density velocity ^ 2 - 3 by nlinarith) (sq_nonneg (z 0))
    nlinarith
  calc
    _ ≤ ∑ direction : Fin 3, (
        2 * (-z 0 / (2 * NativePauliJet.density velocity))^2 * NativePauliJet.density velocity +
          2 * NativePauliJet.density velocity * squared (rotation z direction)) :=
      Finset.sum_le_sum fun direction _ => spinBlock_energy_bound velocity z direction
    _ = 3 * (2 * (-z 0 / (2 * NativePauliJet.density velocity))^2 * NativePauliJet.density velocity) +
        NativePauliJet.density velocity * ∑ direction : Fin 3, z direction.succ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← Finset.mul_sum, rotation_energy]
      ring
    _ ≤ ∑ direction : Fin 4, NativePauliJet.density velocity * z direction ^ 2 := by
      rw [show (∑ direction : Fin 4, NativePauliJet.density velocity * z direction ^ 2) =
        NativePauliJet.density velocity * z 0 ^ 2 +
          ∑ direction : Fin 3, NativePauliJet.density velocity * z direction.succ ^ 2 from Fin.sum_univ_succ _,
        ← Finset.mul_sum]
      linarith
    _ ≤ ∑ direction : Fin 4, squared (derivative direction) := by
      apply Finset.sum_le_sum
      intro direction _
      have bound := log_energy_bound velocity derivative direction
      have nonnegative : 0 ≤ squared (derivative direction) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith

end
end SaturationMonoid.NavierStokes.NativeGeometricMaterial
