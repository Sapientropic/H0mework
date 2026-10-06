import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussNativeForm

/-! Full-CAR matrix multipliers on the same Number-weighted configuration core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussQuantumMultiplier
open GaussNativeMatter GaussFockWeights GaussCoreDifferential GaussFockPair GaussCoreHilbert
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open MeasureTheory
open scoped ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def quantized (A : Matrix Mode Mode ℂ) : FockFiber →L[ℂ] FockFiber :=
  (quantizedFiber A).toContinuousLinearMap

theorem number_commute (A : Matrix Mode Mode ℂ) : Commute fiberNumber (quantized A) := by
  show fiberNumber * quantized A = quantized A * fiberNumber
  apply ContinuousLinearMap.ext
  intro psi
  apply fiberCoordinates.injective
  change SourceFockRaising.total
      (SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (A) (fiberCoordinates psi)) =
    SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (A)
      (SourceFockRaising.total (fiberCoordinates psi))
  exact LinearMap.congr_fun (SourceFockRaising.quantize_preserves_number (A)) (fiberCoordinates psi)

def matrixEntry (A : Matrix Mode Mode ℂ) (output input : Occupation) : ℂ :=
  quantized A (EuclideanSpace.single input 1) output

theorem entry_number_zero (A : Matrix Mode Mode ℂ) (output input : Occupation)
    (different : output.card ≠ input.card) : matrixEntry A output input = 0 := by
  have hn : fiberNumber (EuclideanSpace.single input 1) = (input.card : ℂ) • EuclideanSpace.single input 1 := by
    ext word
    rw [fiberNumber_apply]
    by_cases h : word = input
    · subst word; simp
    · simp [EuclideanSpace.single, h]
  have h := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T (EuclideanSpace.single input 1) output)
    (number_commute A).eq
  change fiberNumber (quantized A (EuclideanSpace.single input 1)) output =
    quantized A (fiberNumber (EuclideanSpace.single input 1)) output at h
  rw [fiberNumber_apply, hn, map_smul] at h
  change (output.card : ℂ) * matrixEntry A output input = (input.card : ℂ) * matrixEntry A output input at h
  have hz : ((output.card : ℂ) - (input.card : ℂ)) * matrixEntry A output input = 0 := by
    linear_combination h
  have hc : (output.card : ℂ) - (input.card : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast different)
  exact (mul_eq_zero.mp hz).resolve_left hc

theorem weight_commute (c : ℕ → ℂ) (A : Matrix Mode Mode ℂ) : Commute (weight c) (quantized A) := by
  show weight c * quantized A = quantized A * weight c
  apply ContinuousLinearMap.ext
  intro psi
  have expansion : psi = ∑ word : Occupation, psi word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have hsingle (input : Occupation) :
      weight c (quantized A (EuclideanSpace.single input 1)) =
        quantized A (weight c (EuclideanSpace.single input 1)) := by
    rw [weight_basis, map_smul]
    apply PiLp.ext
    intro output
    rw [weight_apply]
    change c output.card * matrixEntry A output input = c input.card * matrixEntry A output input
    by_cases h : output.card = input.card
    · rw [h]
    · rw [entry_number_zero A output input h, mul_zero, mul_zero]
  change weight c (quantized A psi) = quantized A (weight c psi)
  rw [expansion, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [map_smul, map_smul, map_smul, map_smul, hsingle]


theorem weighted_pair (c : ℕ → ℂ) (A : Matrix Mode Mode ℂ) (hermitian : A.conjTranspose = A)
    (f g : FockFiber) :
    inner ℂ (weight c f) (quantized A g) = inner ℂ (weight c (quantized A f)) g := by
  have hc := congrArg (fun T : FockFiber →L[ℂ] FockFiber => T f) (weight_commute c A).eq
  change weight c (quantized A f) = quantized A (weight c f) at hc
  rw [hc]
  have h := quantizedFiber_adjoint A (weight c f) g
  rw [hermitian] at h
  exact h.symm

def quantizer : Matrix Mode Mode ℂ →ₗ[ℂ] FockFiber →L[ℂ] FockFiber where
  toFun := quantized
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro f
    exact LinearMap.congr_fun (quantizedFiber_add A B) f
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro f
    exact LinearMap.congr_fun (quantizedFiber_smul c A) f

def action (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => quantized (A w)) z.val) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => quantized (A z)) smooth

theorem action_pair (A : SourceCoordinateSlice → Matrix Mode Mode ℂ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ (fun w => quantized (A w)) z.val)
    (hermitian : ∀ z, (A z).conjTranspose = A z) (f g : QuantumTest) :
    sourcePair f (action A smooth g) = sourcePair (action A smooth f) g := by
  rw [sourcePair_integral, sourcePair_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun z =>
    weighted_pair (fun N => GaussDensityCore.complexDensity N z) (A z) (hermitian z) (f z) (g z))

#print axioms action_pair
end LowEnergy.GaussQuantumMultiplier
