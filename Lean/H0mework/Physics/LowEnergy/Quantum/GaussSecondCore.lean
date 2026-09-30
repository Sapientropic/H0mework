import H0mework.Physics.LowEnergy.Quantum.GaussInverseSecond
import H0mework.Physics.LowEnergy.Quantum.GaussCoreHilbert

set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace LowEnergy.GaussSecondCore
open GaussLiveMomentum GaussInverseSecond GaussHistoryHilbert GaussCoreDifferential
open GaussNativeMatter SourceQuantumScalarChart SourceQuantumConfigurationHilbert
open SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore.StageNineP286GaugeConnectionVariationDensity
open Set Function
open scoped ContDiff Distributions

private def ambientLinear : NativeLie →ₗ[ℝ] Ambient →ₗ[ℝ] Ambient where
  toFun := ambientAction
  map_add' a b := by
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (map_add scalarP286ActionBilinear a b) v.1)
      (LinearMap.congr_fun (map_add nativeGauge a b) v.2)
  map_smul' r a := by
    apply LinearMap.ext
    intro v
    exact Prod.ext (LinearMap.congr_fun (map_smul scalarP286ActionBilinear r a) v.1)
      (LinearMap.congr_fun (map_smul nativeGauge r a) v.2)

private theorem ambient_smooth {f : SourceCoordinateSlice → NativeLie}
    {g : SourceCoordinateSlice → Ambient} {z : SourceCoordinateSlice}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (fun w => ambientAction (f w) (g w)) z := by
  let B := ambientLinear.toContinuousBilinearMap
  have hb : ContDiff ℝ ∞ (fun a : NativeLie => B a) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := NativeLie) (F := Ambient →L[ℝ] Ambient) B
  exact (hb.contDiffAt.comp z hf).clm_apply hg

private theorem forward_smooth {f g : SourceCoordinateSlice → Split} {z : SourceCoordinateSlice}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (fun w => forwardCurvature w (f w) (g w)) z := by
  have hs : ContDiff ℝ ∞ sourceBase := by
    exact (contDiff_const.add
      (scalarSlice.subtypeL.contDiff.comp (contDiff_fst.comp contDiff_snd))).prodMk
      (coordinateSlice.subtypeL.contDiff.comp (contDiff_snd.comp contDiff_snd))
  have hsf : ContDiffAt ℝ ∞ (fun w => sliceMap (f w).2) z :=
    sliceMap.toContinuousLinearMap.contDiff.contDiffAt.comp z hf.snd
  have hsg : ContDiffAt ℝ ∞ (fun w => sliceMap (g w).2) z :=
    sliceMap.toContinuousLinearMap.contDiff.contDiffAt.comp z hg.snd
  exact ((ambient_smooth hf.fst hsg).add (ambient_smooth hg.fst hsf)).add
    (((ambient_smooth hf.fst (ambient_smooth hg.fst hs.contDiffAt)).add
      (ambient_smooth hg.fst (ambient_smooth hf.fst hs.contDiffAt))).const_smul (1/2 : ℝ))

def correction (v w : Ambient) (z : SourceCoordinateSlice) : Split :=
  -inverseL z (forwardCurvature z (inverseL z v) (inverseL z w))

theorem correction_source (v w : Ambient) (z : physicalChart) :
    correction v w z.val = inverseCurvature z v w := rfl

theorem correction_smooth (v w : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (correction v w) z.val :=
  ((inverse_smooth z).clm_apply
    (forward_smooth ((inverse_smooth z).clm_apply contDiffAt_const)
      ((inverse_smooth z).clm_apply contDiffAt_const))).neg

abbrev FirstDerivative := SourceCoordinateSlice →L[ℝ] FockFiber
abbrev SecondDerivative := SourceCoordinateSlice →L[ℝ] FirstDerivative

local instance : NormedAddCommGroup SecondDerivative :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := SourceCoordinateSlice) (F := FirstDerivative) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℝ SecondDerivative :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ)
    (E := SourceCoordinateSlice) (F := FirstDerivative) (σ₁₂ := RingHom.id ℝ)
local instance : NormedSpace ℂ SecondDerivative :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ)
    (E := SourceCoordinateSlice) (F := FirstDerivative) (σ₁₂ := RingHom.id ℝ)

def firstJet : QuantumTest →L[ℂ] 𝓓(physicalChart, FirstDerivative) :=
  TestFunction.fderivCLM ℂ ⊤ ⊤

def secondJet : QuantumTest →L[ℂ]
    𝓓(physicalChart, SecondDerivative) :=
  (TestFunction.fderivCLM (E := SourceCoordinateSlice) (Ω := physicalChart)
    (F := FirstDerivative) ℂ ⊤ ⊤).comp firstJet

theorem firstJet_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    firstJet f z = fderiv ℝ f z :=
  congrFun (TestFunction.fderivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) f (by simp)) z

theorem secondJet_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    secondJet f z = fderiv ℝ (fderiv ℝ f) z := by
  have he : (⇑(firstJet f) : SourceCoordinateSlice → SourceCoordinateSlice →L[ℝ] FockFiber) =
      fderiv ℝ f := funext (firstJet_apply f)
  change (TestFunction.fderivCLM ℂ ⊤ ⊤ (firstJet f)) z = _
  rw [TestFunction.fderivCLM_apply_of_le (𝕜 := ℂ) (n := ⊤) (k := ⊤) (firstJet f) (by simp), he]

private theorem matter_smooth {f : SourceCoordinateSlice → NativeLie}
    {g : SourceCoordinateSlice → FockFiber} {z : SourceCoordinateSlice}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) :
    ContDiffAt ℝ ∞ (fun w => nativeFock (f w) (g w)) z := by
  let B := (ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ).comp
    nativeFock.toContinuousLinearMap
  have hb : ContDiff ℝ ∞ (fun a : NativeLie => B a) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := NativeLie) (F := FockFiber →L[ℝ] FockFiber) B
  exact (hb.contDiffAt.comp z hf).clm_apply hg

def value (v w : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) : FockFiber :=
  secondJet f z (direction v z) (direction w z) +
    firstJet f z (0, (correction v w z).2) +
    nativeFock (inverseL z v).1 (firstJet f z (direction w z)) +
    nativeFock (inverseL z w).1 (firstJet f z (direction v z)) +
    nativeFock (correction v w z).1 (f z) +
    (1/2 : ℂ) • (nativeFock (inverseL z v).1 (nativeFock (inverseL z w).1 (f z)) +
      nativeFock (inverseL z w).1 (nativeFock (inverseL z v).1 (f z)))

theorem value_zero_outside (v w : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice)
    (hz : z ∉ tsupport f) : value v w f z = 0 := by
  have hj := fderiv_of_notMem_tsupport ℝ hz
  have hjj := fderiv_of_notMem_tsupport ℝ (fun h => hz (tsupport_fderiv_subset ℝ h))
  simp only [value, firstJet_apply, secondJet_apply, hj, hjj,
    image_eq_zero_of_notMem_tsupport hz, zero_apply, map_zero,
    add_zero, smul_zero]

theorem value_support (v w : Ambient) (f : QuantumTest) : tsupport (value v w f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra h
  exact hz (value_zero_outside v w f z h)

theorem value_smooth (v w : Ambient) (f : QuantumTest) : ContDiff ℝ ∞ (value v w f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · let p : physicalChart := ⟨z, f.tsupport_subset hz⟩
    have ha := ((inverse_smooth p).clm_apply (contDiffAt_const (c := v))).fst
    have hb := ((inverse_smooth p).clm_apply (contDiffAt_const (c := w))).fst
    have hc := correction_smooth v w p
    have hdv := direction_smooth v p
    have hdw := direction_smooth w p
    have hdf := (firstJet f).contDiff.contDiffAt (x := z)
    have hddf := (secondJet f).contDiff.contDiffAt (x := z)
    have hf := f.contDiff.contDiffAt (x := z)
    have h1 := (hddf.clm_apply hdv).clm_apply hdw
    have h2 := hdf.clm_apply ((contDiffAt_const (c := (0 : Coframe))).prodMk hc.snd)
    have h3 := matter_smooth ha (hdf.clm_apply hdw)
    have h4 := matter_smooth hb (hdf.clm_apply hdv)
    have h5 := matter_smooth hc.fst hf
    have h6 := ((matter_smooth ha (matter_smooth hb hf)).add
      (matter_smooth hb (matter_smooth ha hf))).const_smul (1/2 : ℂ)
    exact ((((h1.add h2).add h3).add h4).add h5).add h6
  · apply (contDiffAt_const (c := (0 : FockFiber))).congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport f |>.isOpen_compl.mem_nhds hz] with x hx
    exact value_zero_outside v w f x hx

def second (v w : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest where
  toFun f := ⟨value v w f, value_smooth v w f,
    f.hasCompactSupport.of_isClosed_subset isClosed_closure (value_support v w f),
    (value_support v w f).trans f.tsupport_subset⟩
  map_add' f g := by
    apply DFunLike.ext
    intro z
    change value v w (f+g) z = value v w f z + value v w g z
    simp only [value, map_add, add_apply, smul_add]
    abel
  map_smul' c f := by
    apply DFunLike.ext
    intro z
    change value v w (c • f) z = c • value v w f z
    simp only [value, map_smul, smul_apply, smul_add, smul_smul]
    module

def realizedSecond (v w : Ambient) : GaussCoreHilbert.H →ₗ.[ℂ] GaussCoreHilbert.H :=
  GaussCoreHilbert.realize (second v w)

theorem realizedSecond_preserves_core (v w : Ambient) (f : (realizedSecond v w).domain) :
    realizedSecond v w f ∈ (realizedSecond v w).domain :=
  GaussCoreHilbert.realize_preserves_core _ f

#print axioms correction_smooth
#print axioms second
#print axioms realizedSecond_preserves_core
end LowEnergy.GaussSecondCore
