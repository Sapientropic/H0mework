import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussLiveMomentum
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussNativeMatter
import Mathlib.Analysis.Distribution.TestFunction

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCoreDifferential
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open GaussHistoryHilbert GaussLiveMomentum SourceQuantumFockGauge
open Set Function
open scoped ContDiff Distributions Topology

abbrev QuantumTest := 𝓓(physicalChart, FockFiber)

def direction (v : Ambient) (z : SourceCoordinateSlice) : SourceCoordinateSlice :=
  (0, (inverseL z v).2)

theorem direction_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (direction v) z.val :=
  contDiffAt_const.prodMk (((inverse_smooth z).clm_apply contDiffAt_const).snd)

def directionalValue (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) : FockFiber :=
  fderiv ℝ f z (direction v z)

theorem directional_zero_outside (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice)
    (hz : z ∉ tsupport f) : directionalValue v f z = 0 := by
  unfold directionalValue
  rw [fderiv_of_notMem_tsupport ℝ hz]
  rfl

theorem directional_support (v : Ambient) (f : QuantumTest) :
    tsupport (directionalValue v f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra h
  exact hz (directional_zero_outside v f z h)

theorem directional_smooth (v : Ambient) (f : QuantumTest) :
    ContDiff ℝ ∞ (directionalValue v f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := f.contDiff.fderiv_right (by simp)
    exact hdf.contDiffAt.clm_apply (direction_smooth v ⟨z, f.tsupport_subset hz⟩)
  · apply (contDiffAt_const (c := (0 : FockFiber))).congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport f |>.isOpen_compl.mem_nhds hz] with w hw
    exact directional_zero_outside v f w hw

def directional (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest where
  toFun f :=
    { toFun := directionalValue v f
      contDiff' := directional_smooth v f
      hasCompactSupport' := f.hasCompactSupport.of_isClosed_subset isClosed_closure (directional_support v f)
      tsupport_subset' := (directional_support v f).trans f.tsupport_subset }
  map_add' f g := by
    apply DFunLike.ext
    intro z
    change fderiv ℝ (f+g : QuantumTest) z (direction v z) = _
    rw [show (⇑(f+g) : SourceCoordinateSlice → FockFiber) = (⇑f + ⇑g) from rfl,
      fderiv_add (f.contDiff.differentiable (by simp)).differentiableAt
        (g.contDiff.differentiable (by simp)).differentiableAt]
    rfl
  map_smul' c f := by
    apply DFunLike.ext
    intro z
    change fderiv ℝ (c • f : QuantumTest) z (direction v z) = _
    rw [show (⇑(c • f) : SourceCoordinateSlice → FockFiber) = (c • ⇑f) from rfl,
      fderiv_const_smul (f.contDiff.differentiable (by simp)).differentiableAt c]
    rfl

theorem directional_apply (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional v f z = fderiv ℝ f z (0, (inverseL z v).2) := rfl

def multiplierValue (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (f : QuantumTest) (z : SourceCoordinateSlice) : FockFiber := A z (f z)

theorem multiplier_support (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (f : QuantumTest) : tsupport (multiplierValue A f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra h
  have hf := image_eq_zero_of_notMem_tsupport h
  exact hz (by simp [multiplierValue, hf])

theorem multiplier_smooth (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) (f : QuantumTest) :
    ContDiff ℝ ∞ (multiplierValue A f) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport f
  · let R := ContinuousLinearMap.restrictScalarsL ℂ FockFiber FockFiber ℝ ℝ
    have hr : ContDiffAt ℝ ∞ (fun w => (A w).restrictScalars ℝ) z :=
      R.contDiff.contDiffAt.comp z (smooth ⟨z, f.tsupport_subset hz⟩)
    exact hr.clm_apply f.contDiff.contDiffAt
  · apply (contDiffAt_const (c := (0 : FockFiber))).congr_of_eventuallyEq
    filter_upwards [isClosed_tsupport f |>.isOpen_compl.mem_nhds hz] with w hw
    simp [multiplierValue, image_eq_zero_of_notMem_tsupport hw]

def localMultiplier (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ A z.val) : QuantumTest →ₗ[ℂ] QuantumTest where
  toFun f :=
    { toFun := multiplierValue A f
      contDiff' := multiplier_smooth A smooth f
      hasCompactSupport' := f.hasCompactSupport.of_isClosed_subset isClosed_closure (multiplier_support A f)
      tsupport_subset' := (multiplier_support A f).trans f.tsupport_subset }
  map_add' f g := by
    apply DFunLike.ext
    intro z
    exact map_add (A z) (f z) (g z)
  map_smul' c f := by
    apply DFunLike.ext
    intro z
    exact map_smul (A z) c (f z)

def connection (v : Ambient) (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  GaussNativeMatter.nativeFock (inverseL z v).1

theorem connection_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (connection v) z.val := by
  let R := GaussNativeMatter.nativeFock.toContinuousLinearMap
  have hr : ContDiff ℝ ∞ (fun a : NativeLie => R a) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := NativeLie)
      (F := FockFiber →L[ℂ] FockFiber) R
  exact hr.contDiffAt.comp z.val (((inverse_smooth z).clm_apply contDiffAt_const).fst)

def covariantMomentum (v : Ambient) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (-Complex.I) • (directional v + localMultiplier (connection v) (connection_smooth v))

theorem covariantMomentum_apply (v : Ambient) (f : QuantumTest) (z : SourceCoordinateSlice) :
    covariantMomentum v f z = (-Complex.I) •
      (fderiv ℝ f z (0, (inverseL z v).2) +
        GaussNativeMatter.nativeFock (inverseL z v).1 (f z)) := rfl

theorem covariantMomentum_orbit (z : physicalChart) (a : NativeLie) (f : QuantumTest) :
    covariantMomentum (orbitMap z.val a) f z.val =
      (-Complex.I) • GaussNativeMatter.nativeFock a (f z.val) := by
  have he : orbitMap z.val a = splitMap z.val (a, 0) := by simp [splitMap, sliceMap]
  rw [covariantMomentum_apply, he, inverse_left]
  change (-Complex.I) • (fderiv ℝ f z.val 0 + GaussNativeMatter.nativeFock a (f z.val)) = _
  rw [map_zero, zero_add]

theorem covariantMomentum_slice (z : physicalChart) (w : Slice) (f : QuantumTest) :
    covariantMomentum (sliceMap w) f z.val =
      (-Complex.I) • fderiv ℝ f z.val (0, w) := by
  have he : sliceMap w = splitMap z.val (0, w) := by simp [splitMap]
  rw [covariantMomentum_apply, he, inverse_left]
  simp

#print axioms direction_smooth
#print axioms directional
#print axioms covariantMomentum
#print axioms covariantMomentum_orbit
#print axioms covariantMomentum_slice
end LowEnergy.GaussCoreDifferential
