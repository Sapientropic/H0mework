import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumResidualChartFlow
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumHalfDensityHilbert
import H0mework.Physics.LowEnergy.Quantum.FockRaising
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.RealScalarFock
import H0mework.Versions.AB.Physics.LowEnergyFermion.Source
import H0mework.Physics.Dirac.FullDiracAdjointLocalOperator

/-! The original full504 Gauss action on the canonical occupation Hilbert fibre.
The CAR pairing adjoint is derived from its original insert/erase signs.
The independent-dual real charge fixes both branches, and the source number
commutator makes every finite residual exponential preserve particle number.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore
open QuantizationCheck.Fermion
open scoped BigOperators ComplexConjugate

section CARPairing
variable {ι : Type*} [Fintype ι] [LinearOrder ι]

private theorem sum_erase_insert (i : ι) (f : Finset ι → ℂ) :
    (∑ s ∈ Finset.univ.filter (fun s : Finset ι => i ∈ s), f s) =
      ∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t), f (insert i t) := by
  apply Finset.sum_bij (fun s _ => s.erase i)
  · intro s hs
    simp
  · intro s hs t ht h
    have hi : i ∈ s := (Finset.mem_filter.mp hs).2
    have hj : i ∈ t := (Finset.mem_filter.mp ht).2
    calc
      s = insert i (s.erase i) := (Finset.insert_erase hi).symm
      _ = insert i (t.erase i) := congrArg (insert i) h
      _ = t := Finset.insert_erase hj
  · intro t ht
    have hi : i ∉ t := (Finset.mem_filter.mp ht).2
    exact ⟨insert i t, by simp, Finset.erase_insert hi⟩
  · intro s hs
    rw [Finset.insert_erase (Finset.mem_filter.mp hs).2]

theorem pairing_create_annihilate (i : ι) (psi phi : Fock ι) :
    pairing (create i psi) phi = pairing psi (annihilate i phi) := by
  calc
    pairing (create i psi) phi =
        ∑ s ∈ Finset.univ.filter (fun s : Finset ι => i ∈ s),
          star (sign i (s.erase i) * psi (s.erase i)) * phi s := by
      simp only [pairing, create, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s _
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
          star (sign i ((insert i t).erase i) * psi ((insert i t).erase i)) * phi (insert i t) :=
      sum_erase_insert i _
    _ = ∑ t ∈ Finset.univ.filter (fun t : Finset ι => i ∉ t),
          star (psi t) * (sign i t * phi (insert i t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.erase_insert (Finset.mem_filter.mp ht).2, star_mul, LowEnergy.Fermion.star_sign]
      ring
    _ = pairing psi (annihilate i phi) := by
      simp [pairing, annihilate, Finset.sum_filter, mul_ite, ite_not]


omit [LinearOrder ι] in
theorem pairing_star (psi phi : Fock ι) : star (pairing psi phi) = pairing phi psi := by
  simp [pairing, star_sum, mul_comm]

theorem pairing_annihilate_create (i : ι) (psi phi : Fock ι) :
    pairing (annihilate i psi) phi = pairing psi (create i phi) := by
  have h := congrArg star (pairing_create_annihilate i phi psi)
  simpa only [pairing_star] using h.symm

omit [LinearOrder ι] in
private theorem pairing_sum_right {κ : Type*} [Fintype κ] (psi : Fock ι) (family : κ → Fock ι) :
    pairing psi (∑ k, family k) = ∑ k, pairing psi (family k) := by
  simp only [pairing, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairing_quantize_adjoint (A : Matrix ι ι ℂ) (psi phi : Fock ι) :
    pairing (LowEnergy.Fermion.quantize A psi) phi = pairing psi (LowEnergy.Fermion.quantize A.conjTranspose phi) := by
  simp only [LowEnergy.Fermion.quantize, LinearMap.sum_apply, LinearMap.smul_apply,
    Module.End.mul_apply, LowEnergy.Fermion.creation_apply, LowEnergy.Fermion.annihilation_apply,
    LowEnergy.Fermion.pairing_sum_left, pairing_sum_right, LowEnergy.Fermion.pairing_smul_left,
    LowEnergy.Fermion.pairing_smul_right, pairing_create_annihilate, pairing_annihilate_create,
    Matrix.conjTranspose_apply]
  rw [Finset.sum_comm]

abbrev Fiber := EuclideanSpace ℂ (Finset ι)

def fiberCoordinates : Fiber (ι := ι) ≃ₗ[ℂ] Fock ι := WithLp.linearEquiv 2 ℂ (Finset ι → ℂ)

omit [LinearOrder ι] in
theorem fiber_pairing (psi phi : Fiber (ι := ι)) :
    inner ℂ psi phi = pairing (fiberCoordinates psi) (fiberCoordinates phi) := by
  simp [PiLp.inner_apply, RCLike.inner_apply, pairing, fiberCoordinates, mul_comm]

def quantizedFiber (A : Matrix ι ι ℂ) : Fiber (ι := ι) →ₗ[ℂ] Fiber (ι := ι) :=
  fiberCoordinates.symm.toLinearMap.comp ((LowEnergy.Fermion.quantize A).comp fiberCoordinates.toLinearMap)

theorem quantizedFiber_adjoint (A : Matrix ι ι ℂ) (psi phi : Fiber (ι := ι)) :
    inner ℂ (quantizedFiber A psi) phi = inner ℂ psi (quantizedFiber A.conjTranspose phi) := by
  rw [fiber_pairing, fiber_pairing]
  simp only [quantizedFiber, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  exact pairing_quantize_adjoint A _ _

private theorem quantize_neg (A : Matrix ι ι ℂ) : LowEnergy.Fermion.quantize (-A) = -LowEnergy.Fermion.quantize A := by
  unfold LowEnergy.Fermion.quantize
  simp only [Matrix.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  exact neg_smul (A i j) (LowEnergy.Fermion.creation i * LowEnergy.Fermion.annihilation j : Module.End ℂ (Fock ι))

theorem quantizedFiber_skew (A : Matrix ι ι ℂ) (hA : A.conjTranspose = -A)
    (psi phi : Fiber (ι := ι)) :
    inner ℂ (quantizedFiber A psi) phi + inner ℂ psi (quantizedFiber A phi) = 0 := by
  rw [quantizedFiber_adjoint, hA]
  have hn : quantizedFiber (-A) phi = -quantizedFiber A phi := by
    simp [quantizedFiber, quantize_neg]
  rw [hn, inner_neg_right, neg_add_cancel]


theorem quantize_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    LowEnergy.Fermion.quantize (c • A) = c • LowEnergy.Fermion.quantize A := by
  simp [LowEnergy.Fermion.quantize, Matrix.smul_apply, Finset.smul_sum, smul_smul]

theorem quantizedFiber_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    quantizedFiber (c • A) = c • quantizedFiber A := by
  ext psi
  simp [quantizedFiber, quantize_smul]

end CARPairing

open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open DiracExteriorMatterAction StageNineHolonomicField StageNineFullDiracAdjointLocalOperator
open LowEnergy.Quantum

abbrev modeOrder : LinearOrder Mode := SourceRealScalarFock.branchOrder
attribute [local instance] modeOrder

def primalGaugeMatrix (a : stabilizer) : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ :=
  LowEnergy.Quantum.operatorMatrix (diracExteriorMotherLieAction
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))))

theorem primalGaugeMatrix_skew (a : stabilizer) : (primalGaugeMatrix a).conjTranspose = -primalGaugeMatrix a := by
  classical
  have hpair (u v : DiracExteriorMatterCarrier) :
      LowEnergy.Quantum.coordinatePair (diracExteriorMotherLieAction
        (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))) u) v +
      LowEnergy.Quantum.coordinatePair u (diracExteriorMotherLieAction
        (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))) v) = 0 := by
    rw [LowEnergy.Quantum.coordinatePair_full, LowEnergy.Quantum.coordinatePair_full, ← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun spin _ => fullInternalPair_motherLie_skew _ (u spin) (v spin))
  ext i j
  have h := hpair (LowEnergy.Quantum.coordinates.symm (Pi.single i 1))
    (LowEnergy.Quantum.coordinates.symm (Pi.single j 1))
  simp only [LowEnergy.Quantum.coordinatePair, ← LowEnergy.Quantum.matrix_action,
    LinearEquiv.apply_symm_apply] at h
  change star (primalGaugeMatrix a j i) = -(primalGaugeMatrix a i j)
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite, ite_mul] at h
  exact eq_neg_of_add_eq_zero_left h

def fullGaugeMatrix (a : stabilizer) : Matrix Mode Mode ℂ :=
  Matrix.fromBlocks (primalGaugeMatrix a) 0 0 ((primalGaugeMatrix a).map (starRingEnd ℂ))

theorem fullGaugeMatrix_skew (a : stabilizer) : (fullGaugeMatrix a).conjTranspose = -fullGaugeMatrix a := by
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact congrFun (congrFun (primalGaugeMatrix_skew a) i) j
    | inr j => simp [fullGaugeMatrix]
  | inr i => cases j with
    | inl j => simp [fullGaugeMatrix]
    | inr j =>
      have h := congrArg star (congrFun (congrFun (primalGaugeMatrix_skew a) i) j)
      simpa [fullGaugeMatrix, Matrix.conjTranspose_apply] using h


abbrev FockFiber := Fiber (ι := Mode)

def fiberGenerator (a : stabilizer) : FockFiber →L[ℂ] FockFiber :=
  (quantizedFiber (fullGaugeMatrix a)).toContinuousLinearMap

theorem fiberGenerator_original (a : stabilizer) (psi : FockFiber) :
    fiberCoordinates (fiberGenerator a psi) = secondQuantize (fullGaugeMatrix a) (fiberCoordinates psi) := by
  change fiberCoordinates (quantizedFiber (fullGaugeMatrix a) psi) = _
  simp only [quantizedFiber, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]
  exact LowEnergy.Fermion.quantize_apply _ _

theorem fiberGenerator_skew (a : stabilizer) (psi phi : FockFiber) :
    inner ℂ (fiberGenerator a psi) phi + inner ℂ psi (fiberGenerator a phi) = 0 :=
  quantizedFiber_skew (fullGaugeMatrix a) (fullGaugeMatrix_skew a) psi phi

local instance : NormedAlgebra ℝ (FockFiber →L[ℂ] FockFiber) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ (FockFiber →L[ℂ] FockFiber) := NormedAlgebra.restrictScalars ℚ ℂ _
local instance : IsTopologicalRing (FockFiber →L[ℂ] FockFiber) where
  continuous_mul := (isBoundedBilinearMap_comp (𝕜 := ℂ) (E := FockFiber) (F := FockFiber) (G := FockFiber)).continuous
local instance : CompleteSpace (FockFiber →L[ℂ] FockFiber) := ContinuousLinearMap.instCompleteSpace

def gamma (a : stabilizer) (t : ℝ) : FockFiber →L[ℂ] FockFiber :=
  NormedSpace.exp (t • fiberGenerator a)

theorem gamma_zero (a : stabilizer) : gamma a 0 = 1 := by
  have h : (0 : ℝ) • fiberGenerator a = 0 := zero_smul ℝ (fiberGenerator a)
  rw [gamma, h, NormedSpace.exp_zero]

theorem gamma_inverse (a : stabilizer) (t : ℝ) : gamma a (-t) * gamma a t = 1 := by
  have hn : (-t) • fiberGenerator a = -(t • fiberGenerator a) := neg_smul t (fiberGenerator a)
  unfold gamma
  rw [hn]
  calc
    _ = NormedSpace.exp (-(t • fiberGenerator a) + t • fiberGenerator a) :=
      (NormedSpace.exp_add_of_commute (𝔸 := FockFiber →L[ℂ] FockFiber)
        (x := -(t • fiberGenerator a)) (y := t • fiberGenerator a) (Commute.refl (t • fiberGenerator a)).neg_left).symm
    _ = 1 := by simp

theorem gamma_apply_inverse (a : stabilizer) (t : ℝ) (psi : FockFiber) :
    gamma a (-t) (gamma a t psi) = psi :=
  congrArg (fun T : FockFiber →L[ℂ] FockFiber => T psi) (gamma_inverse a t)

theorem gamma_deriv (a : stabilizer) (psi : FockFiber) (t : ℝ) :
    HasDerivAt (fun r => gamma a r psi) (fiberGenerator a (gamma a t psi)) t := by
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := FockFiber →L[ℂ] FockFiber) (fiberGenerator a) t
  let evaluate : (FockFiber →L[ℂ] FockFiber) →L[ℝ] FockFiber :=
    (ContinuousLinearMap.apply ℂ FockFiber psi).restrictScalars ℝ
  have hf : HasFDerivAt evaluate evaluate (NormedSpace.exp (t • fiberGenerator a)) := evaluate.hasFDerivAt
  have h := hf.comp_hasDerivAt (𝕜 := ℝ) (l := evaluate) (l' := evaluate) t he
  exact h

theorem gamma_inner (a : stabilizer) (t : ℝ) (psi phi : FockFiber) :
    inner ℂ (gamma a t psi) (gamma a t phi) = inner ℂ psi phi := by
  have hd (r : ℝ) : HasDerivAt (fun s => inner ℂ (gamma a s psi) (gamma a s phi)) 0 r := by
    have h := (gamma_deriv a psi r).inner ℂ (gamma_deriv a phi r)
    rwa [add_comm, fiberGenerator_skew] at h
  have h := is_const_of_deriv_eq_zero (𝕜 := ℝ)
    (f := fun r => inner ℂ (gamma a r psi) (gamma a r phi))
    (fun r => (hd r).differentiableAt) (fun r => (hd r).deriv) t 0
  simpa [gamma_zero] using h

def gammaUnitary (a : stabilizer) (t : ℝ) : FockFiber ≃ₗᵢ[ℂ] FockFiber where
  toFun := gamma a t
  invFun := gamma a (-t)
  left_inv := gamma_apply_inverse a t
  right_inv psi := by simpa only [neg_neg] using gamma_apply_inverse a (-t) psi
  map_add' := (gamma a t).map_add
  map_smul' := (gamma a t).map_smul
  norm_map' psi := by
    change ‖gamma a t psi‖ = ‖psi‖
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), gamma_inner]


def fiberNumber : FockFiber →L[ℂ] FockFiber :=
  (fiberCoordinates.symm.toLinearMap.comp
    ((SourceFockRaising.total (ι := Mode)).comp fiberCoordinates.toLinearMap)).toContinuousLinearMap

theorem fiberNumber_apply (psi : FockFiber) (word : Occupation) :
    fiberNumber psi word = (word.card : ℂ) * psi word := by
  change SourceFockRaising.total (fiberCoordinates psi) word = _
  exact SourceFockRaising.total_apply (fiberCoordinates psi) word

theorem fiberNumber_generator_commute (a : stabilizer) : Commute fiberNumber (fiberGenerator a) := by
  show fiberNumber * fiberGenerator a = fiberGenerator a * fiberNumber
  apply ContinuousLinearMap.ext
  intro psi
  apply fiberCoordinates.injective
  change SourceFockRaising.total (LowEnergy.Fermion.quantize (fullGaugeMatrix a) (fiberCoordinates psi)) =
    LowEnergy.Fermion.quantize (fullGaugeMatrix a) (SourceFockRaising.total (fiberCoordinates psi))
  exact LinearMap.congr_fun (SourceFockRaising.quantize_preserves_number (fullGaugeMatrix a)) (fiberCoordinates psi)

theorem fiberNumber_gamma_commute (a : stabilizer) (t : ℝ) : Commute fiberNumber (gamma a t) := by
  have h : Commute fiberNumber (t • fiberGenerator a) := by
    show fiberNumber * (t • fiberGenerator a) = (t • fiberGenerator a) * fiberNumber
    apply ContinuousLinearMap.ext
    intro psi
    change (fiberNumber.restrictScalars ℝ) (t • fiberGenerator a psi) =
      t • fiberGenerator a (fiberNumber psi)
    rw [map_smul]
    exact congrArg (fun v : FockFiber => t • v)
      (congrArg (fun T : FockFiber →L[ℂ] FockFiber => T psi) (fiberNumber_generator_commute a).eq)
  exact h.exp_right

def gammaMatrix (a : stabilizer) (t : ℝ) : Matrix Occupation Occupation ℂ :=
  fun output input => gamma a t (EuclideanSpace.single input 1) output

theorem gammaMatrix_number_zero (a : stabilizer) (t : ℝ) (output input : Occupation)
    (different : output.card ≠ input.card) : gammaMatrix a t output input = 0 := by
  have hn : fiberNumber (EuclideanSpace.single input 1) = (input.card : ℂ) • EuclideanSpace.single input 1 := by
    ext word
    rw [fiberNumber_apply]
    by_cases h : word = input
    · subst word; simp
    · simp [EuclideanSpace.single, h]
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (EuclideanSpace.single input 1) output)
    (fiberNumber_gamma_commute a t).eq
  change fiberNumber (gamma a t (EuclideanSpace.single input 1)) output =
    gamma a t (fiberNumber (EuclideanSpace.single input 1)) output at h
  rw [fiberNumber_apply, hn, map_smul] at h
  change (output.card : ℂ) * gammaMatrix a t output input = (input.card : ℂ) * gammaMatrix a t output input at h
  have hz : ((output.card : ℂ) - (input.card : ℂ)) * gammaMatrix a t output input = 0 := by
    linear_combination h
  have hc : (output.card : ℂ) - (input.card : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast different)
  exact (mul_eq_zero.mp hz).resolve_left hc

theorem gamma_action (a : stabilizer) (t : ℝ) (psi : FockFiber) (word : Occupation) :
    gamma a t psi word = ∑ input : Occupation, gammaMatrix a t word input * psi input := by
  have h : psi = ∑ input : Occupation, psi input • EuclideanSpace.single input 1 := by
    ext output
    simp [EuclideanSpace.single, Pi.single_apply]
  conv_lhs => rw [h, map_sum]
  simp [gammaMatrix, map_smul, mul_comm]

theorem gammaMatrix_columns (a : stabilizer) (t : ℝ) (first second : Occupation) :
    (∑ output : Occupation, star (gammaMatrix a t output first) * gammaMatrix a t output second) =
      if first = second then 1 else 0 := by
  have h := gamma_inner a t (EuclideanSpace.single first 1) (EuclideanSpace.single second 1)
  simpa [gammaMatrix, PiLp.inner_apply, RCLike.inner_apply, mul_comm, eq_comm] using h

theorem gammaMatrix_inverse (a : stabilizer) (t : ℝ) (output input : Occupation) :
    (∑ middle : Occupation, gammaMatrix a (-t) output middle * gammaMatrix a t middle input) =
      if output = input then 1 else 0 := by
  have h := congrArg (fun psi : FockFiber => psi output) (gamma_apply_inverse a t (EuclideanSpace.single input 1))
  rw [gamma_action] at h
  simpa [gammaMatrix, EuclideanSpace.single, Pi.single_apply, eq_comm] using h


def fullGaussCharge (a : stabilizer) : Matrix Mode Mode ℂ :=
  SourceRealScalarFock.branches (Complex.I • primalGaugeMatrix a)

theorem fullGaussCharge_eq (a : stabilizer) : fullGaussCharge a = Complex.I • fullGaugeMatrix a := by
  ext i j
  cases i <;> cases j <;>
    simp [fullGaussCharge, SourceRealScalarFock.branches, fullGaugeMatrix, Matrix.smul_apply]

theorem original_real_Gauss_charge (a : stabilizer) (p psi : LowEnergy.Quantum.Index → ℂ) :
    (∑ i : Mode, ∑ j : Mode, SourceRealScalarFock.normalizedMomentum p i *
      fullGaussCharge a i j * SourceRealScalarFock.normalizedPrimal psi j) =
      ((SourceRealScalarFock.complexBilinear (Complex.I • primalGaugeMatrix a) p psi).re : ℂ) :=
  SourceRealScalarFock.branches_original_real_bilinear _ p psi

def gaussChargeFiber (a : stabilizer) : FockFiber →L[ℂ] FockFiber :=
  (quantizedFiber (fullGaussCharge a)).toContinuousLinearMap

theorem gaussChargeFiber_eq (a : stabilizer) : gaussChargeFiber a = Complex.I • fiberGenerator a := by
  apply ContinuousLinearMap.ext
  intro psi
  change quantizedFiber (fullGaussCharge a) psi = Complex.I • quantizedFiber (fullGaugeMatrix a) psi
  rw [fullGaussCharge_eq, quantizedFiber_smul]
  rfl

theorem gaussChargeFiber_symmetric (a : stabilizer) : (gaussChargeFiber a).toLinearMap.IsSymmetric := by
  intro psi phi
  change inner ℂ (gaussChargeFiber a psi) phi = inner ℂ psi (gaussChargeFiber a phi)
  rw [gaussChargeFiber_eq]
  simp only [smul_apply, inner_smul_left, inner_smul_right, Complex.conj_I]
  linear_combination -Complex.I * fiberGenerator_skew a psi phi

end LowEnergy.SourceQuantumFockGauge
