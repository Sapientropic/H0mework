import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActiveMatterSectorCharge
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.MixedSpectatorDynamicResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualSignedSector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoreDifferential GaussCoreHilbert GaussFockPair GaussHistoryHilbert
open ActiveMatterSectorCharge GaussQuantumMultiplier QuantizationCheck.Fermion
open scoped BigOperators InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder

def value (word : Occupation) : ℝ := ∑ i ∈ word, modeWeight i

theorem cast_value (word : Occupation) : (value word : ℂ) = ∑ i ∈ word, (modeWeight i : ℂ) := by
  simp [value]

def fiberWeight (c : ℝ → ℂ) : FockFiber →L[ℂ] FockFiber :=
  LinearMap.toContinuousLinearMap {
    toFun := fun f => WithLp.toLp 2 (fun word => c (value word) * f word)
    map_add' := by intro f g; apply PiLp.ext; intro word; exact mul_add _ _ _
    map_smul' := by intro z f; apply PiLp.ext; intro word; change c (value word) * (z * f word) = z * (c (value word) * f word); ring }

theorem fiberWeight_apply (c : ℝ → ℂ) (f : FockFiber) (word : Occupation) :
    fiberWeight c f word = c (value word) * f word := rfl

theorem fiberWeight_basis (c : ℝ → ℂ) (word : Occupation) :
    fiberWeight c (EuclideanSpace.single word 1) = c (value word) • EuclideanSpace.single word 1 := by
  apply PiLp.ext
  intro output
  by_cases h : output = word
  · subst output; simp [fiberWeight_apply]
  · simp [fiberWeight_apply, EuclideanSpace.single, h]

theorem entry_value (A : Matrix Mode Mode ℂ) (hA : ActiveMatterSectorCharge.Preserves A)
    (output input : Occupation) (nonzero : GaussQuantumMultiplier.matrixEntry A output input ≠ 0) : value output = value input := by
  have hb : fiberCoordinates (EuclideanSpace.single input 1) = occupationBasis input := by
    funext word
    by_cases h : word = input
    · subst word; simp [fiberCoordinates, occupationBasis]
    · simp [fiberCoordinates, occupationBasis, EuclideanSpace.single, h]
  have he : GaussQuantumMultiplier.matrixEntry A output input =
      (LowEnergy.Fermion.quantize A) (occupationBasis input) output := by
    have literal : GaussQuantumMultiplier.matrixEntry A output input =
        (LowEnergy.Fermion.quantize A) (fiberCoordinates (EuclideanSpace.single input 1)) output := rfl
    rw [literal,hb]
  have hc := LowEnergy.Fermion.occupationCharge_quantize (fun i => (modeWeight i : ℂ)) A hA
  have h := congrFun (LinearMap.congr_fun hc (occupationBasis input)) output
  have hi := SourceFockRaising.basis_eigenstate (fun i => (modeWeight i : ℂ)) input
  change (∑ i ∈ output, (modeWeight i : ℂ)) * _ =
    (LowEnergy.Fermion.quantize A) (LowEnergy.Fermion.occupationCharge (fun i => (modeWeight i : ℂ)) (occupationBasis input)) output at h
  rw [hi, map_smul] at h
  change (∑ i ∈ output, (modeWeight i : ℂ)) * _ = (∑ i ∈ input, (modeWeight i : ℂ)) * _ at h
  rw [←cast_value,←cast_value,←he] at h
  have hz : ((value output : ℂ)-(value input : ℂ)) * GaussQuantumMultiplier.matrixEntry A output input = 0 := by linear_combination h
  have equal : (value output : ℂ) = (value input : ℂ) := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right nonzero)
  exact_mod_cast equal

theorem fiberWeight_quantized (c : ℝ → ℂ) (A : Matrix Mode Mode ℂ)
    (hA : ActiveMatterSectorCharge.Preserves A) : Commute (fiberWeight c) (GaussQuantumMultiplier.quantized A) := by
  show fiberWeight c * quantized A = quantized A * fiberWeight c
  apply ContinuousLinearMap.ext
  intro f
  have expansion : f = ∑ word : Occupation, f word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have single (input : Occupation) : fiberWeight c (quantized A (EuclideanSpace.single input 1)) =
      quantized A (fiberWeight c (EuclideanSpace.single input 1)) := by
    rw [fiberWeight_basis,map_smul]
    apply PiLp.ext
    intro output
    rw [fiberWeight_apply]
    simp only [PiLp.smul_apply,smul_eq_mul]
    change c (value output)*GaussQuantumMultiplier.matrixEntry A output input = c (value input)*GaussQuantumMultiplier.matrixEntry A output input
    by_cases hz : GaussQuantumMultiplier.matrixEntry A output input = 0
    · rw [hz,mul_zero,mul_zero]
    · rw [entry_value A hA output input hz]
  change fiberWeight c (quantized A f) = quantized A (fiberWeight c f)
  rw [expansion,map_sum,map_sum,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [map_smul,map_smul,map_smul,map_smul,single]

def fiberPiece (s : ℝ) : FockFiber →L[ℂ] FockFiber := fiberWeight (fun r => if r=s then 1 else 0)

theorem fiberPiece_apply (s : ℝ) (f : FockFiber) (word : Occupation) :
    fiberPiece s f word = if value word=s then f word else 0 := by
  by_cases h : value word=s <;> simp [fiberPiece,fiberWeight_apply,h]

def project (s : ℝ) : QuantumTest →ₗ[ℂ] QuantumTest := (TestFunction.postcompCLM (fiberPiece s)).toLinearMap

theorem project_apply (s : ℝ) (f : QuantumTest) (z : SourceCoordinateSlice) :
    project s f z = fiberPiece s (f z) := rfl

def piece (s : ℝ) (f : H) : H := WithLp.toLp 2 (fun word => if value word=s then f word else 0)

@[simp] theorem piece_apply (s : ℝ) (f : H) (word : Occupation) :
    piece s f word = if value word=s then f word else 0 := rfl

theorem piece_bound (s : ℝ) (f : H) : ‖piece s f‖ ≤ ‖f‖ := by
  have h : ‖piece s f‖^2 ≤ ‖f‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_le_sum
    intro word _
    by_cases hs : value word=s <;> simp [hs]
  nlinarith [norm_nonneg (piece s f),norm_nonneg f]

def projection (s : ℝ) : H →L[ℂ] H :=
  (show H →ₗ[ℂ] H from {
    toFun := piece s
    map_add' := by intro f g; ext word; by_cases h : value word=s <;> simp [h]
    map_smul' := by intro c f; ext word; by_cases h : value word=s <;> simp [h] }).mkContinuous 1
      (fun f => by change ‖piece s f‖ ≤ 1*‖f‖; simpa only [one_mul] using piece_bound s f)

@[simp] theorem projection_apply (s : ℝ) (f : H) (word : Occupation) :
    projection s f word = if value word=s then f word else 0 := rfl

theorem projection_symmetric (s : ℝ) : (projection s).toLinearMap.IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro word _
  by_cases h : value word=s <;> simp [h]

theorem projection_idempotent (s : ℝ) (f : H) : projection s (projection s f) = projection s f := by
  apply PiLp.ext
  intro word
  by_cases h : value word=s <;> simp [h]

theorem embed_project (s : ℝ) (f : QuantumTest) : embed (project s f) = projection s (embed f) := by
  apply PiLp.ext
  intro word
  apply MeasureTheory.Lp.ext
  filter_upwards [embed_ae (project s f) word,embed_ae f word,
    MeasureTheory.Lp.coeFn_zero ℂ 2 (GaussHistoryHilbert.numberMeasure word.card)] with z hp hf hz
  rw [hp,projection_apply]
  change fiberPiece s (f z) word = _
  rw [fiberPiece_apply]
  by_cases h : value word=s
  · simpa only [if_pos h] using hf.symm
  · simpa only [if_neg h,Pi.zero_apply] using hz.symm

theorem project_pair (s : ℝ) (f g : QuantumTest) : sourcePair f (project s g) = sourcePair (project s f) g := by
  simp only [sourcePair,embed_project]
  exact (projection_symmetric s (embed f) (embed g)).symm

theorem projection_preserves_core (s : ℝ) (f : H) (hf : f ∈ GaussHistoryHilbert.fockTestDomain) :
    projection s f ∈ GaussHistoryHilbert.fockTestDomain := by
  intro word
  by_cases h : value word=s
  · simpa only [projection_apply,if_pos h] using hf word
  · simp only [projection_apply,if_neg h]
    exact (GaussHistoryHilbert.testDomain word.card).zero_mem

theorem projection_grade (s : ℝ) (g : NativeHistoryGrade.Label) :
    Commute (projection s) (NativeHistoryGrade.projection g) := by
  show _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro word
  by_cases hs : value word=s <;> by_cases hg : NativeHistoryGrade.sourceLabel word=g <;>
    simp [hs,hg]

end LowEnergy.ActualSignedSector
