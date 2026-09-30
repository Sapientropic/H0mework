import H0mework.Physics.LowEnergy.Quantum.SourceQuantumResidualFlow
import H0mework.Physics.GaugeStanding.GaugeBFAlgebra
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Prod

/-! Original residual flows preserve both native component pairings.
Their product max norm and canonical product volume are handled separately.
Coframe preservation fixes the actual number weight; chart weight transport
uses typed endpoints, and the entire actual source orbit is generated in the chart.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceQuantumResidualFlowMeasure
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCoframeScalarMatterRegularity
open StageNineCoframeGravityGaugeRegularity StageNineP286GaugeAuxiliaryVariation
open StageNineP286LinkedActiveGaugeBFAlgebra StageNineP286LinkedActiveScalarPairingSkew
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumResidualFlow
open scoped RealInnerProductSpace

private theorem scalar_skew (a : stabilizer) (x y : scalarSlice) :
    ⟪scalarAction a x, y⟫ + ⟪x, scalarAction a y⟫ = 0 := by
  have h := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))) (x : Scalar) (y : Scalar)
  rw [original_scalar_pairing, original_scalar_pairing] at h
  exact h

private theorem native_skew (a b c : NativeLie) :
    ⟪(show NativeLie from jointP286CoordinateLieBracket a b), c⟫ + ⟪b, (show NativeLie from jointP286CoordinateLieBracket a c)⟫ = 0 := by
  change p286CoordinateLiePairing (jointP286CoordinateLieBracket a b) c +
    p286CoordinateLiePairing b (jointP286CoordinateLieBracket a c) = 0
  exact p286CoordinateLiePairing_adjoint_skew a b c

private theorem gauge_skew (a : stabilizer) (x y : Gauge) :
    ⟪gaugeAction a x, y⟫ + ⟪x, gaugeAction a y⟫ = 0 := by
  change (∑ i : Fin 3, ⟪(show NativeLie from jointP286CoordinateLieBracket (a : NativeLie) (gaugeCoordinates x i)), gaugeCoordinates y i⟫) +
    (∑ i : Fin 3, ⟪gaugeCoordinates x i, (show NativeLie from jointP286CoordinateLieBracket (a : NativeLie) (gaugeCoordinates y i))⟫) = 0
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero (fun i _ => native_skew (a : NativeLie) (gaugeCoordinates x i) (gaugeCoordinates y i))

local instance : IsTopologicalRing (Configuration →L[ℝ] Configuration) where
  continuous_mul := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := Configuration)
    (F := Configuration) (G := Configuration)).continuous
local instance : CompleteSpace (Configuration →L[ℝ] Configuration) := ContinuousLinearMap.instCompleteSpace

theorem flow_deriv (a : stabilizer) (z : Configuration) (t : ℝ) :
    HasDerivAt (fun r : ℝ => flow (r • a) z) (generator a (flow (t • a) z)) t := by
  have he := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := Configuration →L[ℝ] Configuration) (generator a) t
  have h := he.clm_apply (hasDerivAt_const t z)
  simpa [flow, map_smul, mul_apply_eq_comp] using h

theorem flow_coframe (a : stabilizer) (z : Configuration) : (flow a z).1 = z.1 := by
  have hd (t : ℝ) : HasDerivAt (fun r : ℝ => (flow (r • a) z).1) 0 t := (flow_deriv a z t).fst
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [one_smul, zero_smul, flow_zero] using h

theorem flow_scalar_inner (a : stabilizer) (x y : Configuration) :
    ⟪(flow a x).2.1, (flow a y).2.1⟫ = ⟪x.2.1, y.2.1⟫ := by
  have hd (t : ℝ) : HasDerivAt
      (fun r : ℝ => ⟪(flow (r • a) x).2.1, (flow (r • a) y).2.1⟫) 0 t := by
    have hx : HasDerivAt (fun r : ℝ => (flow (r • a) x).2.1)
        (scalarAction a (flow (t • a) x).2.1) t := (flow_deriv a x t).snd.fst
    have hy : HasDerivAt (fun r : ℝ => (flow (r • a) y).2.1)
        (scalarAction a (flow (t • a) y).2.1) t := (flow_deriv a y t).snd.fst
    have h := hx.inner ℝ hy
    rwa [add_comm, scalar_skew] at h
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [one_smul, zero_smul, flow_zero] using h

theorem flow_gauge_inner (a : stabilizer) (x y : Configuration) :
    ⟪(flow a x).2.2, (flow a y).2.2⟫ = ⟪x.2.2, y.2.2⟫ := by
  have hd (t : ℝ) : HasDerivAt
      (fun r : ℝ => ⟪(flow (r • a) x).2.2, (flow (r • a) y).2.2⟫) 0 t := by
    have hx : HasDerivAt (fun r : ℝ => (flow (r • a) x).2.2)
        (gaugeAction a (flow (t • a) x).2.2) t := (flow_deriv a x t).snd.snd
    have hy : HasDerivAt (fun r : ℝ => (flow (r • a) y).2.2)
        (gaugeAction a (flow (t • a) y).2.2) t := (flow_deriv a y t).snd.snd
    have h := hx.inner ℝ hy
    rwa [add_comm, gauge_skew] at h
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) 1 0
  simpa [one_smul, zero_smul, flow_zero] using h


theorem flow_scalar_norm (a : stabilizer) (z : Configuration) : ‖(flow a z).2.1‖ = ‖z.2.1‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, flow_scalar_inner]

theorem flow_gauge_norm (a : stabilizer) (z : Configuration) : ‖(flow a z).2.2‖ = ‖z.2.2‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, flow_gauge_inner]

theorem flow_norm (a : stabilizer) (z : Configuration) : ‖flow a z‖ = ‖z‖ := by
  simp only [Prod.norm_def, flow_coframe, flow_scalar_norm, flow_gauge_norm]

/-- The actual configuration norm is the product max norm. -/
def flowIsometry (a : stabilizer) : Configuration ≃ₗᵢ[ℝ] Configuration where
  toFun := flow a
  invFun := flow (-a)
  left_inv := flow_neg_apply a
  right_inv z := by simpa only [neg_neg] using flow_neg_apply (-a) z
  map_add' := (flow a).map_add
  map_smul' := (flow a).map_smul
  norm_map' := flow_norm a

def scalarPart (a : stabilizer) : scalarSlice →ₗ[ℝ] scalarSlice :=
  ((LinearMap.fst ℝ scalarSlice Gauge).comp (LinearMap.snd ℝ Coframe (scalarSlice × Gauge))).comp
    ((flow a).toLinearMap.comp ((LinearMap.inr ℝ Coframe (scalarSlice × Gauge)).comp
      (LinearMap.inl ℝ scalarSlice Gauge)))

def gaugePart (a : stabilizer) : Gauge →ₗ[ℝ] Gauge :=
  ((LinearMap.snd ℝ scalarSlice Gauge).comp (LinearMap.snd ℝ Coframe (scalarSlice × Gauge))).comp
    ((flow a).toLinearMap.comp ((LinearMap.inr ℝ Coframe (scalarSlice × Gauge)).comp
      (LinearMap.inr ℝ scalarSlice Gauge)))

def scalarPartIsometry (a : stabilizer) : scalarSlice →ₗᵢ[ℝ] scalarSlice where
  toLinearMap := scalarPart a
  norm_map' x := flow_scalar_norm a (0, (x, 0))

def gaugePartIsometry (a : stabilizer) : Gauge →ₗᵢ[ℝ] Gauge where
  toLinearMap := gaugePart a
  norm_map' x := flow_gauge_norm a (0, (0, x))

def scalarPartEquiv (a : stabilizer) : scalarSlice ≃ₗᵢ[ℝ] scalarSlice :=
  LinearIsometryEquiv.ofSurjective (scalarPartIsometry a)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (scalarPartIsometry a).injective)

def gaugePartEquiv (a : stabilizer) : Gauge ≃ₗᵢ[ℝ] Gauge :=
  LinearIsometryEquiv.ofSurjective (gaugePartIsometry a)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp (gaugePartIsometry a).injective)

theorem flow_scalar_part (a : stabilizer) (z : Configuration) :
    (flow a z).2.1 = scalarPartEquiv a z.2.1 := by
  have h := flow_scalar_norm a (z - (0, (z.2.1, 0)))
  have hz : (flow a (z - (0, (z.2.1, 0)))).2.1 = 0 := norm_eq_zero.mp (by simpa using h)
  change (flow a z).2.1 = (flow a (0, (z.2.1, 0))).2.1
  exact sub_eq_zero.mp (by simpa only [map_sub, Prod.fst_sub, Prod.snd_sub] using hz)

theorem flow_gauge_part (a : stabilizer) (z : Configuration) :
    (flow a z).2.2 = gaugePartEquiv a z.2.2 := by
  have h := flow_gauge_norm a (z - (0, (0, z.2.2)))
  have hz : (flow a (z - (0, (0, z.2.2)))).2.2 = 0 := norm_eq_zero.mp (by simpa using h)
  change (flow a z).2.2 = (flow a (0, (0, z.2.2))).2.2
  exact sub_eq_zero.mp (by simpa only [map_sub, Prod.fst_sub, Prod.snd_sub] using hz)

theorem flow_product (a : stabilizer) : (flow a : Configuration → Configuration) =
    Prod.map id (Prod.map (scalarPartEquiv a) (gaugePartEquiv a)) := by
  funext z
  apply Prod.ext
  · exact flow_coframe a z
  · exact Prod.ext (flow_scalar_part a z) (flow_gauge_part a z)

open MeasureTheory

theorem flow_measurePreserving (a : stabilizer) :
    MeasurePreserving (flow a) configurationMeasure configurationMeasure := by
  have hs : MeasurePreserving (scalarPartEquiv a)
      SourceQuantumScalarHilbert.sliceMeasure SourceQuantumScalarHilbert.sliceMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    exact LinearIsometryEquiv.measurePreserving (E := scalarSlice) (F := scalarSlice) (scalarPartEquiv a)
  have hg : MeasurePreserving (gaugePartEquiv a) gaugeMeasure gaugeMeasure :=
    (gaugePartEquiv a).measurePreserving
  let : IsLocallyFiniteMeasure SourceQuantumScalarHilbert.sliceMeasure := by
    unfold SourceQuantumScalarHilbert.sliceMeasure
    infer_instance
  rw [flow_product]
  exact (MeasurePreserving.id coframeMeasure).prod (hs.prod hg)

def ambientNumberWeight (N : ℕ) (z : Configuration) : ℝ :=
  (z.1 0 * z.1 2 * z.1 5) ^ (N + 2)

theorem ambientNumberWeight_flow (N : ℕ) (a : stabilizer) (z : Configuration) :
    ambientNumberWeight N (flow a z) = ambientNumberWeight N z := by
  simp only [ambientNumberWeight, flow_coframe]

theorem ambientNumberWeight_chart (N : ℕ) (z : chart) :
    ambientNumberWeight N z = numberWeight N z := rfl

theorem chartNumberWeight_flow (N : ℕ) (a : stabilizer) (z : chart)
    (hz : flow a z ∈ chart) :
    numberWeight N ⟨flow a z, hz⟩ = numberWeight N z := ambientNumberWeight_flow N a z

theorem source_flow_mem_chart (a : stabilizer) : flow a source ∈ chart := by
  change 0 < (flow a source).1 0 ∧ 0 < (flow a source).1 2 ∧
    0 < (flow a source).1 5 ∧ (flow a source).2.1 ∈ scalarChart
  rw [flow_coframe, flow_scalar_part]
  change 0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧ 0 < (1 : ℝ) ∧ scalarPartEquiv a 0 ∈ scalarChart
  rw [map_zero]
  exact ⟨by norm_num, by norm_num, by norm_num, zero_mem_scalarChart⟩

def actualSourceOrbit (a : stabilizer) : chart := ⟨flow a source, source_flow_mem_chart a⟩

theorem actualSourceOrbit_weight (N : ℕ) (a : stabilizer) : numberWeight N (actualSourceOrbit a) = 1 := by
  change ambientNumberWeight N (flow a source) = 1
  rw [ambientNumberWeight_flow]
  exact source_weight_one N

end LowEnergy.SourceQuantumResidualFlowMeasure
