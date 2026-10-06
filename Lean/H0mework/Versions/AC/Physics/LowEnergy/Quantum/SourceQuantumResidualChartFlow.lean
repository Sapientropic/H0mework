import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceQuantumResidualFlowMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The same residual action preserves the whole original noncharacteristic chart.
The original scalar representation and native adjoint generate the consistency
commutator, finite conjugacy and determinant invariance. These feed the actual
weighted L² pullback and its original smooth compact test domain.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceQuantumResidualChartFlow
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open StageNineP286BracketCalculus StageNineP286LinkedActiveLieRepresentation
open StageNineP286GaugeConnectionVariationDensity StageNineP286GaugeAuxiliaryVariation
open StageNineP286LinkedActiveGaugeBFAlgebra StageNineP286LinkedActiveScalarPairingSkew
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumResidualFlow SourceQuantumResidualFlowMeasure
open scoped RealInnerProductSpace

private abbrev scalarA (a : NativeLie) : Scalar →ₗ[ℝ] Scalar := scalarP286ActionBilinear a

private theorem native_skew (a b c : NativeLie) :
    ⟪(show NativeLie from jointP286CoordinateLieBracket a b), c⟫ +
      ⟪b, (show NativeLie from jointP286CoordinateLieBracket a c)⟫ = 0 := by
  change p286CoordinateLiePairing (jointP286CoordinateLieBracket a b) c +
    p286CoordinateLiePairing b (jointP286CoordinateLieBracket a c) = 0
  exact p286CoordinateLiePairing_adjoint_skew a b c

private theorem scalar_skew (a : NativeLie) (x y : Scalar) :
    ⟪scalarA a x, y⟫ + ⟪x, scalarA a y⟫ = 0 := by
  have h := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (SU7MotherLieAlgebra.p286LieBlockEmbed (p286CoordinateEquiv.symm a)) x y
  rw [original_scalar_pairing, original_scalar_pairing] at h
  exact h

def nativeAdjoint (a : stabilizer) : NativeLie →ₗ[ℝ] NativeLie where
  toFun b := jointP286CoordinateLieBracket (a : NativeLie) b
  map_add' b c := jointP286CoordinateLieBracket_add_right b c (a : NativeLie)
  map_smul' r b := jointP286CoordinateLieBracket_smul_right r b (a : NativeLie)

theorem nativeAdjoint_stabilizer (a b : stabilizer) : nativeAdjoint a (b : NativeLie) ∈ stabilizer := by
  have h := scalarP286ActionBilinear_coordinateBracket (a : NativeLie) (b : NativeLie) vacuum
  have ha : scalarA (a : NativeLie) vacuum = 0 := a.property
  have hb : scalarA (b : NativeLie) vacuum = 0 := b.property
  change scalarA (nativeAdjoint a b) vacuum = 0
  change scalarA (nativeAdjoint a b) vacuum = scalarA (a : NativeLie) (scalarA (b : NativeLie) vacuum) -
    scalarA (b : NativeLie) (scalarA (a : NativeLie) vacuum) at h
  rw [ha, hb, map_zero, map_zero, sub_self] at h
  exact h

theorem nativeAdjoint_broken (a : stabilizer) (b : broken) : nativeAdjoint a (b : NativeLie) ∈ broken := by
  apply (Submodule.mem_orthogonal _ _).2
  intro c hc
  have h := native_skew (a : NativeLie) c (b : NativeLie)
  have hz := (Submodule.mem_orthogonal _ _).1 b.property (nativeAdjoint a c)
    (nativeAdjoint_stabilizer a ⟨c,hc⟩)
  change ⟪nativeAdjoint a c, (b : NativeLie)⟫ + ⟪c, nativeAdjoint a (b : NativeLie)⟫ = 0 at h
  rw [hz, zero_add] at h
  exact h

def brokenGenerator (a : stabilizer) : broken →ₗ[ℝ] broken :=
  ((nativeAdjoint a).comp broken.subtype).codRestrict broken (nativeAdjoint_broken a)

theorem brokenGenerator_skew (a : stabilizer) (b c : broken) :
    ⟪brokenGenerator a b, c⟫ + ⟪b, brokenGenerator a c⟫ = 0 :=
  native_skew (a : NativeLie) (b : NativeLie) (c : NativeLie)

theorem orbit_intertwine (a : stabilizer) (b : broken) :
    scalarA (a : NativeLie) (brokenOrbit b) = brokenOrbit (brokenGenerator a b) := by
  have h := scalarP286ActionBilinear_coordinateBracket (a : NativeLie) (b : NativeLie) vacuum
  have ha : scalarA (a : NativeLie) vacuum = 0 := a.property
  change brokenOrbit (brokenGenerator a b) = scalarA (a : NativeLie) (brokenOrbit b) - scalarA (b : NativeLie) (scalarA (a : NativeLie) vacuum) at h
  rw [ha, map_zero, sub_zero] at h
  exact h.symm

theorem consistency_commutator (a : stabilizer) (phi : Scalar) :
    consistency (scalarA (a : NativeLie) phi) =
      (brokenGenerator a).comp (consistency phi) - (consistency phi).comp (brokenGenerator a) := by
  apply LinearMap.ext
  intro b
  apply ext_inner_left ℝ
  intro c
  change ⟪c, consistency (scalarA (a : NativeLie) phi) b⟫ =
    ⟪c, brokenGenerator a (consistency phi b) - consistency phi (brokenGenerator a b)⟫
  rw [inner_sub_right, consistency_pairing, consistency_pairing]
  have hcomm := scalarP286ActionBilinear_coordinateBracket (a : NativeLie) (b : NativeLie) phi
  change scalarA (brokenGenerator a b) phi = scalarA (a : NativeLie) (scalarA (b : NativeLie) phi) -
    scalarA (b : NativeLie) (scalarA (a : NativeLie) phi) at hcomm
  have hb : scalarA (b : NativeLie) (scalarA (a : NativeLie) phi) =
      scalarA (a : NativeLie) (scalarA (b : NativeLie) phi) - scalarA (brokenGenerator a b) phi := by
    rw [hcomm]
    abel
  change ⟪brokenOrbit c, scalarA (b : NativeLie) (scalarA (a : NativeLie) phi)⟫ =
    ⟪c, brokenGenerator a (consistency phi b)⟫ - ⟪brokenOrbit c, scalarA (brokenGenerator a b) phi⟫
  rw [hb, inner_sub_right]
  have hs := scalar_skew (a : NativeLie) (brokenOrbit c) (scalarA (b : NativeLie) phi)
  rw [orbit_intertwine] at hs
  have hk := brokenGenerator_skew a c (consistency phi b)
  rw [consistency_pairing] at hk
  change ⟪brokenOrbit (brokenGenerator a c), scalarA (b : NativeLie) phi⟫ +
    ⟪c, brokenGenerator a (consistency phi b)⟫ = 0 at hk
  linarith


def brokenGeneratorL (a : stabilizer) : broken →L[ℝ] broken := (brokenGenerator a).toContinuousLinearMap

def scalarPath (a : stabilizer) (x : scalarSlice) (t : ℝ) : Scalar :=
  vacuum + ((flow (t • a) (0, (x, 0))).2.1 : Scalar)

theorem scalarPath_deriv (a : stabilizer) (x : scalarSlice) (t : ℝ) :
    HasDerivAt (scalarPath a x) (scalarA (a : NativeLie) (scalarPath a x t)) t := by
  have hx : HasDerivAt (fun r : ℝ => (flow (r • a) (0, (x, 0))).2.1)
      (scalarAction a (flow (t • a) (0, (x, 0))).2.1) t := (flow_deriv a (0, (x, 0)) t).snd.fst
  have hc := scalarSlice.subtypeL.hasFDerivAt.comp_hasDerivAt t hx
  have h := hc.const_add vacuum
  have ha : scalarA (a : NativeLie) vacuum = 0 := a.property
  have he : scalarA (a : NativeLie) (scalarPath a x t) =
      (scalarAction a (flow (t • a) (0, (x, 0))).2.1 : Scalar) := by
    change scalarA (a : NativeLie) (vacuum + ((flow (t • a) (0, (x, 0))).2.1 : Scalar)) = _
    rw [map_add, ha, zero_add]
    rfl
  rw [he]
  exact h

def consistencyPath (a : stabilizer) (x : scalarSlice) (t : ℝ) : broken →L[ℝ] broken :=
  consistencyFamily (scalarPath a x t)

theorem consistencyPath_deriv (a : stabilizer) (x : scalarSlice) (t : ℝ) :
    HasDerivAt (consistencyPath a x)
      (brokenGeneratorL a * consistencyPath a x t - consistencyPath a x t * brokenGeneratorL a) t := by
  have hf : HasFDerivAt (fun phi : Scalar => consistencyFamily phi)
      consistencyFamily.toContinuousLinearMap (scalarPath a x t) := consistencyFamily.toContinuousLinearMap.hasFDerivAt
  have h := hf.comp_hasDerivAt (𝕜 := ℝ) (l := fun phi : Scalar => consistencyFamily phi)
    (l' := consistencyFamily.toContinuousLinearMap) (f := scalarPath a x) t (scalarPath_deriv a x t)
  apply h.congr_deriv
  apply ContinuousLinearMap.ext
  intro b
  exact LinearMap.congr_fun (consistency_commutator a (scalarPath a x t)) b

local instance : IsTopologicalRing (broken →L[ℝ] broken) where
  continuous_mul := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := broken) (F := broken) (G := broken)).continuous
local instance : CompleteSpace (broken →L[ℝ] broken) := ContinuousLinearMap.instCompleteSpace

def conjugatedConsistency (a : stabilizer) (x : scalarSlice) (t : ℝ) : broken →L[ℝ] broken :=
  NormedSpace.exp (t • (-brokenGeneratorL a)) * consistencyPath a x t * NormedSpace.exp (t • brokenGeneratorL a)

theorem conjugatedConsistency_deriv (a : stabilizer) (x : scalarSlice) (t : ℝ) :
    HasDerivAt (conjugatedConsistency a x) 0 t := by
  have hl := hasDerivAt_exp_smul_const (𝕂 := ℝ) (𝔸 := broken →L[ℝ] broken) (-brokenGeneratorL a) t
  have hr := hasDerivAt_exp_smul_const' (𝕂 := ℝ) (𝔸 := broken →L[ℝ] broken) (brokenGeneratorL a) t
  have h := (hl.mul (consistencyPath_deriv a x t)).mul hr
  have hz :
      ((NormedSpace.exp (t • -brokenGeneratorL a) * -brokenGeneratorL a * consistencyPath a x t +
        NormedSpace.exp (t • -brokenGeneratorL a) *
          (brokenGeneratorL a * consistencyPath a x t - consistencyPath a x t * brokenGeneratorL a)) *
          NormedSpace.exp (t • brokenGeneratorL a) +
        (NormedSpace.exp (t • -brokenGeneratorL a) * consistencyPath a x t) *
          (brokenGeneratorL a * NormedSpace.exp (t • brokenGeneratorL a))) = 0 := by
    apply ContinuousLinearMap.ext
    intro b
    simp only [mul_apply_eq_comp, add_apply, sub_apply,
      neg_apply, zero_apply, map_sub, map_neg]
    abel
  exact h.congr_deriv (𝕜 := ℝ) hz

theorem consistency_conjugacy (a : stabilizer) (x : scalarSlice) :
    NormedSpace.exp (-brokenGeneratorL a) *
        consistencyFamily (vacuum + (scalarPartEquiv a x : Scalar)) * NormedSpace.exp (brokenGeneratorL a) =
      consistencyFamily (vacuum + (x : Scalar)) := by
  have h := is_const_of_deriv_eq_zero (𝕜 := ℝ) (f := conjugatedConsistency a x)
    (fun t => (conjugatedConsistency_deriv a x t).differentiableAt)
    (fun t => (conjugatedConsistency_deriv a x t).deriv) 1 0
  have he0 (T : broken →L[ℝ] broken) : (0 : ℝ) • T = 0 := zero_smul ℝ T
  have he1 (T : broken →L[ℝ] broken) : (1 : ℝ) • T = T := one_smul ℝ T
  have hx0 : scalarPath a x 0 = vacuum + (x : Scalar) := by
    simp [scalarPath, flow_zero]
  have hx1 : scalarPath a x 1 = vacuum + (scalarPartEquiv a x : Scalar) := by
    simp [scalarPath, flow_scalar_part]
  simp only [conjugatedConsistency, consistencyPath, he0, he1, NormedSpace.exp_zero,
    hx0, hx1, one_mul, mul_one] at h
  exact h

private theorem broken_exp_inverse (a : stabilizer) :
    NormedSpace.exp (-brokenGeneratorL a) * NormedSpace.exp (brokenGeneratorL a) = 1 := by
  calc
    _ = NormedSpace.exp (-brokenGeneratorL a + brokenGeneratorL a) :=
      (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (𝔸 := broken →L[ℝ] broken)
        (x := -brokenGeneratorL a) (y := brokenGeneratorL a) (Commute.refl (brokenGeneratorL a)).neg_left
        (by simp [NormedSpace.expSeries_radius_eq_top])
        (by simp [NormedSpace.expSeries_radius_eq_top])).symm
    _ = 1 := by simp

private def detHom : (broken →L[ℝ] broken) →* ℝ :=
  LinearMap.det.comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom

theorem consistency_determinant_flow (a : stabilizer) (x : scalarSlice) :
    (consistency (vacuum + (scalarPartEquiv a x : Scalar))).det =
      (consistency (vacuum + (x : Scalar))).det := by
  have h := congrArg detHom (consistency_conjugacy a x)
  have hi := congrArg detHom (broken_exp_inverse a)
  rw [map_mul, map_mul] at h
  rw [map_mul, map_one] at hi
  change detHom (NormedSpace.exp (-brokenGeneratorL a)) *
    (consistency (vacuum + (scalarPartEquiv a x : Scalar))).det * detHom (NormedSpace.exp (brokenGeneratorL a)) = _ at h
  calc
    _ = (detHom (NormedSpace.exp (-brokenGeneratorL a)) * detHom (NormedSpace.exp (brokenGeneratorL a))) *
        (consistency (vacuum + (scalarPartEquiv a x : Scalar))).det := by rw [hi, one_mul]
    _ = detHom (NormedSpace.exp (-brokenGeneratorL a)) *
        (consistency (vacuum + (scalarPartEquiv a x : Scalar))).det * detHom (NormedSpace.exp (brokenGeneratorL a)) := by ring
    _ = _ := h

theorem scalarChart_flow_iff (a : stabilizer) (x : scalarSlice) :
    scalarPartEquiv a x ∈ scalarChart ↔ x ∈ scalarChart := by
  change (consistency (vacuum + (scalarPartEquiv a x : Scalar))).det ≠ 0 ↔ _
  rw [consistency_determinant_flow]
  rfl

theorem chart_flow_iff (a : stabilizer) (z : Configuration) : flow a z ∈ chart ↔ z ∈ chart := by
  change (0 < (flow a z).1 0 ∧ 0 < (flow a z).1 2 ∧ 0 < (flow a z).1 5 ∧
    (flow a z).2.1 ∈ scalarChart) ↔ _
  rw [flow_coframe, flow_scalar_part, scalarChart_flow_iff]
  rfl


def chartFlow (a : stabilizer) (z : chart) : chart := ⟨flow a z, (chart_flow_iff a z).mpr z.property⟩

theorem chartFlow_neg_left (a : stabilizer) (z : chart) : chartFlow (-a) (chartFlow a z) = z :=
  Subtype.ext (flow_neg_apply a z)

theorem chartFlow_neg_right (a : stabilizer) (z : chart) : chartFlow a (chartFlow (-a) z) = z := by
  simpa only [neg_neg] using chartFlow_neg_left (-a) z

def chartFlowHomeomorph (a : stabilizer) : chart ≃ₜ chart where
  toFun := chartFlow a
  invFun := chartFlow (-a)
  left_inv := chartFlow_neg_left a
  right_inv := chartFlow_neg_right a
  continuous_toFun := ((flow a).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((flow (-a)).continuous.comp continuous_subtype_val).subtype_mk _

open MeasureTheory Set

theorem chartFlow_measurePreserving (a : stabilizer) :
    MeasurePreserving (chartFlow a) chartMeasure chartMeasure := by
  have hm : Measurable (chartFlow a) := (chartFlowHomeomorph a).continuous.measurable
  have hs : MeasurePreserving (Subtype.val : chart → Configuration) chartMeasure
      (configurationMeasure.restrict chart) := measurePreserving_subtype_coe chart.isOpen.measurableSet
  have hr := (flow_measurePreserving a).restrict_preimage chart.isOpen.measurableSet
  have hp : (flow a) ⁻¹' (chart : Set Configuration) = chart := Set.ext (chart_flow_iff a)
  rw [hp] at hr
  refine ⟨hm, ?_⟩
  apply (MeasurableEmbedding.subtype_coe chart.isOpen.measurableSet).map_injective
  calc
    Measure.map (Subtype.val : chart → Configuration) (Measure.map (chartFlow a) chartMeasure) =
        Measure.map ((Subtype.val : chart → Configuration) ∘ chartFlow a) chartMeasure :=
      Measure.map_map measurable_subtype_coe hm
    _ = Measure.map ((flow a) ∘ (Subtype.val : chart → Configuration)) chartMeasure := rfl
    _ = configurationMeasure.restrict chart := (hr.comp hs).map_eq
    _ = Measure.map (Subtype.val : chart → Configuration) chartMeasure := hs.map_eq.symm

theorem chartFlow_numberWeight (N : ℕ) (a : stabilizer) (z : chart) :
    numberWeight N (chartFlow a z) = numberWeight N z := chartNumberWeight_flow N a z _

theorem chartFlow_numberMeasurePreserving (N : ℕ) (a : stabilizer) :
    MeasurePreserving (chartFlow a) (numberMeasure N) (numberMeasure N) := by
  have hm : Measurable (chartFlow a) := (chartFlowHomeomorph a).continuous.measurable
  refine ⟨hm, ?_⟩
  ext s hs
  rw [Measure.map_apply hm hs, numberMeasure, withDensity_apply _ (hm hs),
    withDensity_apply _ hs]
  have h := (chartFlow_measurePreserving a).setLIntegral_comp_preimage hs
    (numberWeight_continuous N).measurable.ennreal_ofReal
  simpa only [chartFlow_numberWeight] using h


def sectorPullback (N : ℕ) (a : stabilizer) : SectorHilbert N →ₗᵢ[ℂ] SectorHilbert N :=
  Lp.compMeasurePreservingₗᵢ ℂ (chartFlow a) (chartFlow_numberMeasurePreserving N a)

theorem sectorPullback_neg_left (N : ℕ) (a : stabilizer) (f : SectorHilbert N) :
    sectorPullback N (-a) (sectorPullback N a f) = f := by
  change Lp.compMeasurePreserving (chartFlow (-a)) (chartFlow_numberMeasurePreserving N (-a))
    (Lp.compMeasurePreserving (chartFlow a) (chartFlow_numberMeasurePreserving N a) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : chartFlow a ∘ chartFlow (-a) = id := funext (chartFlow_neg_right a)
  simp only [h, Lp.compMeasurePreserving_id_apply]

theorem sectorPullback_neg_right (N : ℕ) (a : stabilizer) (f : SectorHilbert N) :
    sectorPullback N a (sectorPullback N (-a) f) = f := by
  simpa only [neg_neg] using sectorPullback_neg_left N (-a) f

/-- The original weighted complex L² space consumes the generated residual chart action. -/
def sectorUnitary (N : ℕ) (a : stabilizer) : SectorHilbert N ≃ₗᵢ[ℂ] SectorHilbert N where
  toFun := sectorPullback N a
  invFun := sectorPullback N (-a)
  left_inv := sectorPullback_neg_left N a
  right_inv := sectorPullback_neg_right N a
  map_add' := (sectorPullback N a).map_add
  map_smul' := (sectorPullback N a).map_smul
  norm_map' := (sectorPullback N a).norm_map

theorem sectorUnitary_apply_ae (N : ℕ) (a : stabilizer) (f : SectorHilbert N) :
    sectorUnitary N a f =ᵐ[numberMeasure N] fun z => f (chartFlow a z) :=
  Lp.coeFn_compMeasurePreserving f (chartFlow_numberMeasurePreserving N a)


theorem sectorUnitary_testDomain (N : ℕ) (a : stabilizer) (f : SectorHilbert N)
    (hf : f ∈ testDomain N) : sectorUnitary N a f ∈ testDomain N := by
  rcases hf with ⟨g, hfg, hgk, hgc, hgs⟩
  refine ⟨g ∘ flow a, ?_, ?_, hgc.comp (flow a).contDiff, ?_⟩
  · exact (sectorUnitary_apply_ae N a f).trans
      ((chartFlow_numberMeasurePreserving N a).quasiMeasurePreserving.ae_eq hfg)
  · exact hgk.comp_homeomorph (flowIsometry a).toHomeomorph
  · intro z hz
    have h : flow a z ∈ tsupport g := tsupport_comp_subset_preimage g (flow a).continuous hz
    exact (chart_flow_iff a z).mp (hgs h)

theorem sectorUnitary_testDomain_iff (N : ℕ) (a : stabilizer) (f : SectorHilbert N) :
    sectorUnitary N a f ∈ testDomain N ↔ f ∈ testDomain N := by
  constructor
  · intro h
    have hi := sectorUnitary_testDomain N (-a) (sectorUnitary N a f) h
    change sectorPullback N (-a) (sectorPullback N a f) ∈ testDomain N at hi
    simpa only [sectorPullback_neg_left] using hi
  · exact sectorUnitary_testDomain N a f

end LowEnergy.SourceQuantumResidualChartFlow
