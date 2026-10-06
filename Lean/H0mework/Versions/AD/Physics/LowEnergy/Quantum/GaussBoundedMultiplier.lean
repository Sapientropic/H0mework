import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussYukawaCoefficient
import Mathlib.Analysis.Normed.Operator.Extend

/-! Number-preserving source bounds descend to the actual weighted Gauss Hilbert core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussBoundedMultiplier
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussFockWeights GaussDensityCore
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge MeasureTheory
open scoped ContDiff InnerProductSpace

def halfWeight (c : ℕ → ℝ) : FockFiber →L[ℂ] FockFiber := weight (fun N => (Real.sqrt (c N) : ℂ))

theorem halfWeight_pair (c : ℕ → ℝ) (f g : FockFiber) :
    inner ℂ (halfWeight c f) g = inner ℂ f (halfWeight c g) := by
  simp only [PiLp.inner_apply, halfWeight, weight_apply, RCLike.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  simp only [map_mul]
  have hs : (starRingEnd ℂ) (Real.sqrt (c word.card) : ℂ) = (Real.sqrt (c word.card) : ℂ) := by simp
  rw [hs]
  ring

theorem halfWeight_square (c : ℕ → ℝ) (positive : ∀ N, 0 ≤ c N) :
    halfWeight c * halfWeight c = weight (fun N => (c N : ℂ)) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  change (Real.sqrt (c word.card) : ℂ)*((Real.sqrt (c word.card) : ℂ)*f word) = (c word.card : ℂ)*f word
  have hs : (Real.sqrt (c word.card) : ℂ)^2 = (c word.card : ℂ) := by
    exact_mod_cast Real.sq_sqrt (positive word.card)
  rw [← mul_assoc, ← pow_two, hs]

theorem weighted_square (c : ℕ → ℝ) (positive : ∀ N, 0 ≤ c N) (f : FockFiber) :
    RCLike.re (inner ℂ (weight (fun N => (c N : ℂ)) f) f) = ‖halfWeight c f‖^2 := by
  rw [← halfWeight_square c positive]
  change RCLike.re (inner ℂ (halfWeight c (halfWeight c f)) f) = _
  rw [halfWeight_pair, inner_self_eq_norm_sq]

theorem weighted_bound (c : ℕ → ℝ) (positive : ∀ N, 0 ≤ c N)
    (A : FockFiber →L[ℂ] FockFiber)
    (commutes : ∀ w : ℕ → ℂ, Commute (weight w) A)
    (C : ℝ) (bound : ∀ f, ‖A f‖ ≤ C*‖f‖) (f : FockFiber) :
    RCLike.re (inner ℂ (weight (fun N => (c N : ℂ)) (A f)) (A f)) ≤
      C^2 * RCLike.re (inner ℂ (weight (fun N => (c N : ℂ)) f) f) := by
  rw [weighted_square c positive, weighted_square c positive]
  have hw : halfWeight c (A f) = A (halfWeight c f) :=
    congrArg (fun T : FockFiber →L[ℂ] FockFiber => T f) (commutes (fun N => (Real.sqrt (c N) : ℂ))).eq
  rw [hw]
  exact (pow_le_pow_left₀ (norm_nonneg _) (bound _) 2).trans_eq (mul_pow C ‖halfWeight c f‖ 2)

theorem norm_square_integral (f : QuantumTest) :
    ‖embed f‖^2 = ∫ z, RCLike.re (densityPair f f z) ∂GaussHistoryHilbert.configurationMeasure := by
  rw [integral_re (densityPair_integrable f f), ← sourcePair_integral]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (x := embed f)).symm

theorem action_bound
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (commutes : ∀ z : physicalChart, ∀ w : ℕ → ℂ, Commute (weight w) (A z))
    (C : ℝ) (hC : 0 ≤ C) (bound : ∀ z : physicalChart, ∀ f, ‖A z f‖ ≤ C*‖f‖)
    (f : QuantumTest) : ‖embed (localMultiplier A smooth f)‖ ≤ C*‖embed f‖ := by
  let g := localMultiplier A smooth f
  have hp (z : SourceCoordinateSlice) : RCLike.re (densityPair g g z) ≤ C^2 * RCLike.re (densityPair f f z) := by
    change RCLike.re (inner ℂ (weight (fun N => (density N z : ℂ)) (A z (f z))) (A z (f z))) ≤ _
    by_cases hz : z ∈ physicalChart
    · exact weighted_bound (fun N => density N z) (fun N => (density_pos N ⟨z,hz⟩).le)
        (A z) (commutes ⟨z,hz⟩) C (bound ⟨z,hz⟩) (f z)
    · have hf : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))
      simp [densityPair, hf]
  have hs : ‖embed g‖^2 ≤ C^2 * ‖embed f‖^2 := by
    calc
      _ = ∫ z, RCLike.re (densityPair g g z) ∂GaussHistoryHilbert.configurationMeasure := norm_square_integral g
      _ ≤ ∫ z, C^2 * RCLike.re (densityPair f f z) ∂GaussHistoryHilbert.configurationMeasure :=
        integral_mono (densityPair_integrable g g).re ((densityPair_integrable f f).re.const_mul _) hp
      _ = _ := by rw [integral_const_mul, ← norm_square_integral]
  nlinarith [norm_nonneg (embed g), mul_nonneg hC (norm_nonneg (embed f))]

def coreMap (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) : Core →ₗ[ℂ] H :=
  embed.comp ((localMultiplier A smooth).comp coreEquiv.symm.toLinearMap)

theorem coreMap_bound
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (commutes : ∀ z : physicalChart, ∀ w : ℕ → ℂ, Commute (weight w) (A z))
    (C : ℝ) (hC : 0 ≤ C) (bound : ∀ z : physicalChart, ∀ f, ‖A z f‖ ≤ C*‖f‖)
    (x : Core) : ‖coreMap A smooth x‖ ≤ C*‖x‖ := by
  obtain ⟨f,rfl⟩ := coreEquiv.surjective x
  change ‖embed (localMultiplier A smooth (coreEquiv.symm (coreEquiv f)))‖ ≤ C*‖embed f‖
  rw [coreEquiv.symm_apply_apply]
  exact action_bound A smooth commutes C hC bound f

theorem core_dense : DenseRange (Core.subtypeL : Core →L[ℂ] H) := by
  have h : Set.range (Core.subtypeL : Core →L[ℂ] H) = (Core : Set H) := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩; exact v.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  change Dense (Set.range (Core.subtypeL : Core →L[ℂ] H))
  rw [h]
  exact GaussHistoryHilbert.fockTestDomain_dense

def extension
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (commutes : ∀ z : physicalChart, ∀ w : ℕ → ℂ, Commute (weight w) (A z))
    (C : ℝ) (hC : 0 ≤ C) (bound : ∀ z : physicalChart, ∀ f, ‖A z f‖ ≤ C*‖f‖) : H →L[ℂ] H :=
  ((coreMap A smooth).mkContinuous C (coreMap_bound A smooth commutes C hC bound)).extend Core.subtypeL

theorem extension_core
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (commutes : ∀ z : physicalChart, ∀ w : ℕ → ℂ, Commute (weight w) (A z))
    (C : ℝ) (hC : 0 ≤ C) (bound : ∀ z : physicalChart, ∀ f, ‖A z f‖ ≤ C*‖f‖)
    (f : QuantumTest) : extension A smooth commutes C hC bound (embed f) = embed (localMultiplier A smooth f) := by
  have h := ContinuousLinearMap.extend_eq
    ((coreMap A smooth).mkContinuous C (coreMap_bound A smooth commutes C hC bound)) core_dense
    isometry_subtype_coe.isUniformInducing (coreEquiv f)
  change extension A smooth commutes C hC bound (embed f) =
    embed (localMultiplier A smooth (coreEquiv.symm (coreEquiv f))) at h
  simpa only [coreEquiv.symm_apply_apply] using h

theorem extension_norm
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val)
    (commutes : ∀ z : physicalChart, ∀ w : ℕ → ℂ, Commute (weight w) (A z))
    (C : ℝ) (hC : 0 ≤ C) (bound : ∀ z : physicalChart, ∀ f, ‖A z f‖ ≤ C*‖f‖) :
    ‖extension A smooth commutes C hC bound‖ ≤ C := by
  let f := (coreMap A smooth).mkContinuous C (coreMap_bound A smooth commutes C hC bound)
  have hf : ‖f‖ ≤ C := f.opNorm_le_bound hC (coreMap_bound A smooth commutes C hC bound)
  have he := f.opNorm_extend_le (e := Core.subtypeL) (N := (1 : NNReal)) core_dense
    (fun x => by change ‖x‖ ≤ (1 : ℝ)*‖x‖; rw [one_mul])
  change ‖extension A smooth commutes C hC bound‖ ≤ (1 : ℝ)*‖f‖ at he
  rw [one_mul] at he
  exact he.trans hf

#print axioms action_bound
#print axioms extension_core

end LowEnergy.GaussBoundedMultiplier
