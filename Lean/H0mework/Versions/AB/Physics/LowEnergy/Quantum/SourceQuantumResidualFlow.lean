import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceQuantumGaugeSliceCoordinates
import H0mework.Physics.GaugeStanding.LieRepresentation
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-! The original residual scalar and gauge action generates finite source flows.
Its source derivative is the already constructed orbit/slice equivalence, so
the local inverse, open physical slice and finite-flow extension are outputs.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LowEnergy.SourceQuantumResidualFlow
open SaturationMonoid.PhysicsCore
open StageNineHolonomicField StageNineCoframeScalarMatterRegularity
open StageNineCoframeGravityGaugeRegularity StageNineP286BracketCalculus
open StageNineP286LinkedActiveLieRepresentation StageNineP286LinkedActiveScalarPairingSkew
open SU7MotherLieAlgebra
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open scoped RealInnerProductSpace

private theorem scalar_action_orbit (a : stabilizer) (b : NativeLie) :
    StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) (orbit b) =
      orbit (coordinateBracket (a : NativeLie) b) := by
  have h := scalarP286ActionBilinear_coordinateBracket (a : NativeLie) b vacuum
  have ha : StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) vacuum = 0 := a.property
  rw [ha, map_zero, sub_zero] at h
  exact h.symm

private theorem scalar_action_slice (a : stabilizer) (x : scalarSlice) :
    StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) (x : Scalar) ∈ scalarSlice := by
  apply (Submodule.mem_orthogonal _ _).2
  rintro _ ⟨b, rfl⟩
  have hs := scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (p286LieBlockEmbed (p286CoordinateEquiv.symm (a : NativeLie))) (orbit b) (x : Scalar)
  rw [original_scalar_pairing, original_scalar_pairing] at hs
  change ⟪StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) (orbit b), (x : Scalar)⟫ +
    ⟪orbit b, StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) (x : Scalar)⟫ = 0 at hs
  rw [scalar_action_orbit] at hs
  have hx := (Submodule.mem_orthogonal _ _).1 x.property
    (orbit (coordinateBracket (a : NativeLie) b)) ⟨_, rfl⟩
  rw [hx, zero_add] at hs
  exact hs

def scalarAction : stabilizer →ₗ[ℝ] scalarSlice →ₗ[ℝ] scalarSlice where
  toFun a := ((StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie)).comp scalarSlice.subtype).codRestrict
    scalarSlice (scalar_action_slice a)
  map_add' a b := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear (a : NativeLie) (b : NativeLie)) x
  map_smul' r a := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul StageNineP286GaugeConnectionVariationDensity.scalarP286ActionBilinear r (a : NativeLie)) x

def gaugeAction : stabilizer →ₗ[ℝ] Gauge →ₗ[ℝ] Gauge where
  toFun a :=
    { toFun v := WithLp.toLp 2 (fun i => jointP286CoordinateLieBracket (a : NativeLie) (gaugeCoordinates v i))
      map_add' v w := by
        apply gaugeCoordinates.injective
        funext i
        exact jointP286CoordinateLieBracket_add_right (gaugeCoordinates v i) (gaugeCoordinates w i) (a : NativeLie)
      map_smul' r v := by
        apply gaugeCoordinates.injective
        funext i
        exact jointP286CoordinateLieBracket_smul_right r (gaugeCoordinates v i) (a : NativeLie) }
  map_add' a b := by
    ext v
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_add_left (a : NativeLie) (b : NativeLie) (gaugeCoordinates v i)
  map_smul' r a := by
    ext v
    apply gaugeCoordinates.injective
    funext i
    exact jointP286CoordinateLieBracket_smul_left r (a : NativeLie) (gaugeCoordinates v i)

def infinitesimal : stabilizer →ₗ[ℝ] Configuration →ₗ[ℝ] Configuration where
  toFun a :=
    { toFun v := (0, (scalarAction a v.2.1, gaugeAction a v.2.2))
      map_add' := by intros; simp [map_add]
      map_smul' := by intros; simp [map_smul] }
  map_add' := by intros; ext v <;> simp [map_add]
  map_smul' := by intros; ext v <;> simp [map_smul]

def generator : stabilizer →L[ℝ] Configuration →L[ℝ] Configuration :=
  infinitesimal.toContinuousBilinearMap

def source : Configuration := SourceQuantumConfigurationHilbert.sourcePoint.val

theorem generator_source (a : stabilizer) : generator a source = (0, (0, residualOrbit a)) := by
  change (0, (scalarAction a 0, gaugeAction a SourceQuantumConfigurationHilbert.sourceGauge)) = _
  rw [map_zero]
  rfl

abbrev FlowDomain := stabilizer × SourceCoordinateSlice

def sliceInjection : SourceCoordinateSlice →ₗ[ℝ] Configuration :=
  (LinearMap.id : Coframe →ₗ[ℝ] Coframe).prodMap
    ((LinearMap.id : scalarSlice →ₗ[ℝ] scalarSlice).prodMap coordinateSlice.subtype)

local instance : IsTopologicalRing (Configuration →L[ℝ] Configuration) where
  continuous_mul := (isBoundedBilinearMap_comp (𝕜 := ℝ) (E := Configuration)
    (F := Configuration) (G := Configuration)).continuous

local instance : CompleteSpace (Configuration →L[ℝ] Configuration) :=
  ContinuousLinearMap.instCompleteSpace

def flow (a : stabilizer) : Configuration →L[ℝ] Configuration := NormedSpace.exp (generator a)


theorem flow_zero : flow 0 = 1 := by simp [flow]

theorem flow_neg_mul (a : stabilizer) : flow (-a) * flow a = 1 := by
  simp only [flow, map_neg]
  calc
    NormedSpace.exp (-generator a) * NormedSpace.exp (generator a) =
        NormedSpace.exp (-generator a + generator a) :=
      (NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        (𝔸 := Configuration →L[ℝ] Configuration)
        (x := -generator a) (y := generator a) (Commute.refl (generator a)).neg_left
        (by simp [NormedSpace.expSeries_radius_eq_top])
        (by simp [NormedSpace.expSeries_radius_eq_top])).symm
    _ = 1 := by simp

theorem flow_neg_apply (a : stabilizer) (z : Configuration) : flow (-a) (flow a z) = z :=
  congrArg (fun T : Configuration →L[ℝ] Configuration => T z) (flow_neg_mul a)

def orbitMap (v : FlowDomain) : Configuration := flow v.1 (source + sliceInjection v.2)


private def rearrange : FlowDomain ≃ₗ[ℝ] (Coframe × scalarSlice) × (stabilizer × coordinateSlice) where
  toFun v := ((v.2.1, v.2.2.1), (v.1, v.2.2.2))
  invFun v := (v.2.1, (v.1.1, (v.1.2, v.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sourceDerivative : FlowDomain ≃ₗ[ℝ] Configuration :=
  (rearrange.trans ((LinearEquiv.refl ℝ (Coframe × scalarSlice)).prodCongr sourceSplitEquiv)).trans
    (LinearEquiv.prodAssoc ℝ Coframe scalarSlice Gauge)

theorem sourceDerivative_apply (v : FlowDomain) : sourceDerivative v =
    (v.2.1, (v.2.2.1, residualOrbit v.1 + (v.2.2.2 : Gauge))) := rfl

def sourceDerivativeL : FlowDomain ≃L[ℝ] Configuration := sourceDerivative.toContinuousLinearEquiv

theorem orbitMap_zero : orbitMap 0 = source := by
  simp [orbitMap, flow]

set_option backward.isDefEq.respectTransparency false in
theorem orbitMap_strictDerivative :
    HasStrictFDerivAt orbitMap (sourceDerivativeL : FlowDomain →L[ℝ] Configuration) 0 := by
  let A : FlowDomain →L[ℝ] Configuration →L[ℝ] Configuration :=
    generator.comp (ContinuousLinearMap.fst ℝ stabilizer SourceCoordinateSlice)
  let B : FlowDomain →L[ℝ] Configuration :=
    sliceInjection.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℝ stabilizer SourceCoordinateSlice)
  have hA : HasStrictFDerivAt (fun v => NormedSpace.exp (A v)) A 0 := by
    have he : HasStrictFDerivAt NormedSpace.exp
        (1 : (Configuration →L[ℝ] Configuration) →L[ℝ] (Configuration →L[ℝ] Configuration))
        (A (0 : FlowDomain)) := by
      rw [map_zero]
      exact hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Configuration →L[ℝ] Configuration)
    have ha : HasStrictFDerivAt (fun v : FlowDomain => A v) A 0 := A.hasStrictFDerivAt
    have h := HasStrictFDerivAt.comp (𝕜 := ℝ) (E := FlowDomain)
      (F := Configuration →L[ℝ] Configuration) (G := Configuration →L[ℝ] Configuration)
      (f := fun v : FlowDomain => A v) (f' := A) (g := NormedSpace.exp)
      (g' := (1 : (Configuration →L[ℝ] Configuration) →L[ℝ] (Configuration →L[ℝ] Configuration)))
      (0 : FlowDomain) he ha
    exact h.congr_fderiv (by apply ContinuousLinearMap.ext; intro v; rfl)
  have hB : HasStrictFDerivAt (fun v => source + B v) B 0 := B.hasStrictFDerivAt.const_add source
  have h := hA.clm_apply hB
  change HasStrictFDerivAt (fun v => NormedSpace.exp (A v) (source + B v))
    (sourceDerivativeL : FlowDomain →L[ℝ] Configuration) 0
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  change NormedSpace.exp (A 0) (B v) + A v (source + B 0) = sourceDerivative v
  simp only [map_zero, add_zero, NormedSpace.exp_zero, one_apply_eq_self]
  change sliceInjection v.2 + generator v.1 source = sourceDerivative v
  rw [generator_source, sourceDerivative_apply]
  change (v.2.1, (v.2.2.1, (v.2.2.2 : Gauge))) + (0, (0, residualOrbit v.1)) = _
  simp [add_comm]

def sourceOrbitChart : OpenPartialHomeomorph FlowDomain Configuration :=
  orbitMap_strictDerivative.toOpenPartialHomeomorph orbitMap

theorem zero_mem_sourceOrbitChart : (0 : FlowDomain) ∈ sourceOrbitChart.source :=
  orbitMap_strictDerivative.mem_toOpenPartialHomeomorph_source

theorem source_mem_sourceOrbitChart : source ∈ sourceOrbitChart.target := by
  rw [← orbitMap_zero]
  exact orbitMap_strictDerivative.image_mem_toOpenPartialHomeomorph_target


theorem sourceOrbitChart_apply (v : FlowDomain) : sourceOrbitChart v = orbitMap v := rfl

def orbitCoordinates : Configuration → FlowDomain := sourceOrbitChart.symm

theorem orbitCoordinates_strictDerivative :
    HasStrictFDerivAt orbitCoordinates (sourceDerivativeL.symm : Configuration →L[ℝ] FlowDomain) source := by
  rw [← orbitMap_zero]
  exact orbitMap_strictDerivative.to_localInverse

def slicePoint (w : SourceCoordinateSlice) : Configuration := source + sliceInjection w

def sourceSliceDomain : TopologicalSpace.Opens SourceCoordinateSlice :=
  ⟨{w | (0, w) ∈ sourceOrbitChart.source ∧ slicePoint w ∈ chart}, by
    apply IsOpen.inter
    · exact sourceOrbitChart.open_source.preimage (continuous_const.prodMk continuous_id)
    · exact chart.isOpen.preimage (continuous_const.add sliceInjection.continuous_of_finiteDimensional)⟩

theorem zero_mem_sourceSliceDomain : (0 : SourceCoordinateSlice) ∈ sourceSliceDomain := by
  constructor
  · exact zero_mem_sourceOrbitChart
  · simp [slicePoint, source]

def physicalSlicePoint (w : sourceSliceDomain) : chart := ⟨slicePoint w, w.property.2⟩

theorem physicalSlicePoint_zero :
    physicalSlicePoint ⟨0, zero_mem_sourceSliceDomain⟩ = SourceQuantumConfigurationHilbert.sourcePoint := by
  apply Subtype.ext
  simp [physicalSlicePoint, slicePoint, source]

/-- Extension is generated by the actual nonlinear inverse, not an external orbit selector. -/
def extend (f : SourceCoordinateSlice → ℂ) (z : Configuration) : ℂ := f (orbitCoordinates z).2

theorem extend_on_actual_flow (f : SourceCoordinateSlice → ℂ) (v : FlowDomain)
    (hv : v ∈ sourceOrbitChart.source) :
    extend f (flow v.1 (source + sliceInjection v.2)) = f v.2 := by
  change f (sourceOrbitChart.symm (sourceOrbitChart v)).2 = f v.2
  rw [sourceOrbitChart.left_inv hv]

theorem actual_flow_from_coordinates (z : Configuration) (hz : z ∈ sourceOrbitChart.target) :
    flow (orbitCoordinates z).1 (source + sliceInjection (orbitCoordinates z).2) = z :=
  sourceOrbitChart.right_inv hz

end LowEnergy.SourceQuantumResidualFlow
