import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussNativePotential

/-! The literal source-native scalar/gauge quadratic form on the Gauss100 core. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussNativeForm
open GaussNativeEnergy GaussNativePotential GaussHistoryHilbert
open GaussCoreDifferential GaussCoreHilbert GaussMomentumAdjoint GaussFockPair
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceQuantumNativeDimensions GaussLiveMomentum
open MeasureTheory
open scoped ContDiff Distributions

abbrev ScalarIndex := Fin (Module.finrank ℝ Scalar)
abbrev LieIndex := Fin (Module.finrank ℝ NativeLie)
def scalarBasis := stdOrthonormalBasis ℝ Scalar
def lieBasis := stdOrthonormalBasis ℝ NativeLie

def scalarDirection (a : ScalarIndex) : Ambient := (scalarBasis a, 0)
def gaugeDirection (i : Fin 3) (a : LieIndex) : Ambient :=
  (0, WithLp.toLp 2 (Pi.single i (lieBasis a)))

def multiply (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun z => (c z : ℂ) • ContinuousLinearMap.id ℂ FockFiber)
    (fun z => (Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (smooth z)).smul contDiffAt_const)

theorem multiply_apply (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : QuantumTest)
    (z : SourceCoordinateSlice) : multiply c smooth f z = (c z : ℂ) • f z := rfl

theorem multiply_pair (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (multiply c smooth g) = sourcePair (multiply c smooth f) g := by
  rw [sourcePair_integral, sourcePair_integral]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun z => ?_)
  rw [densityPair_sum, densityPair_sum]
  apply Finset.sum_congr rfl
  intro word _
  change _ * star (f z word) * ((c z : ℂ) * g z word) =
    _ * star ((c z : ℂ) * f z word) * g z word
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  ring

theorem pair_conjugate (f g : QuantumTest) :
    (starRingEnd ℂ) (sourcePair f g) = sourcePair g f := inner_conj_symm _ _

theorem adjoint_pair (v : Ambient) (f g : QuantumTest) :
    sourcePair f (adjoint v g) = sourcePair (covariantMomentum v f) g := by
  have h := congrArg (starRingEnd ℂ) (momentum_pair v g f)
  rw [pair_conjugate, pair_conjugate] at h
  exact h.symm

def sandwich (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (adjoint v).comp ((multiply c smooth).comp (covariantMomentum w))

theorem sandwich_pair (v w : Ambient) (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f g : QuantumTest) :
    sourcePair f (sandwich v w c smooth g) = sourcePair (sandwich w v c smooth f) g := by
  change sourcePair f (adjoint v (multiply c smooth (covariantMomentum w g))) = _
  rw [adjoint_pair, multiply_pair, momentum_pair]
  rfl

private theorem pair_sum_right {ι : Type*} [Fintype ι] (f : QuantumTest) (g : ι → QuantumTest) :
    sourcePair f (∑ i, g i) = ∑ i, sourcePair f (g i) := by
  unfold sourcePair
  rw [map_sum, inner_sum]

private theorem pair_sum_left {ι : Type*} [Fintype ι] (f : ι → QuantumTest) (g : QuantumTest) :
    sourcePair (∑ i, f i) g = ∑ i, sourcePair (f i) g := by
  unfold sourcePair
  rw [map_sum, sum_inner]

def scalarKinetic : QuantumTest →ₗ[ℂ] QuantumTest :=
  (1/2 : ℂ) • ∑ a : ScalarIndex,
    sandwich (scalarDirection a) (scalarDirection a) scalarWeight scalarWeight_smooth

def gaugeKinetic : QuantumTest →ₗ[ℂ] QuantumTest :=
  (1/2 : ℂ) • ∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3,
    sandwich (gaugeDirection i a) (gaugeDirection j a)
      (fun z => gaugeWeight z i j) (gaugeWeight_smooth i j)

def nativeAction : QuantumTest →ₗ[ℂ] QuantumTest :=
  scalarKinetic + gaugeKinetic + multiply potential potential_smooth

theorem scalarKinetic_pair (f g : QuantumTest) :
    sourcePair f (scalarKinetic g) = sourcePair (scalarKinetic f) g := by
  simp only [scalarKinetic, LinearMap.smul_apply, LinearMap.sum_apply]
  change inner ℂ (embed f) (embed ((1/2 : ℂ) • _)) =
    inner ℂ (embed ((1/2 : ℂ) • _)) (embed g)
  rw [map_smul, map_smul, inner_smul_right, inner_smul_left]
  simp only [map_div₀, map_one, map_ofNat]
  congr 1
  change sourcePair f (∑ a : ScalarIndex, _) = sourcePair (∑ a : ScalarIndex, _) g
  rw [pair_sum_left, pair_sum_right]
  exact Finset.sum_congr rfl (fun a _ => sandwich_pair _ _ _ _ f g)

theorem gaugeKinetic_pair (f g : QuantumTest) :
    sourcePair f (gaugeKinetic g) = sourcePair (gaugeKinetic f) g := by
  simp only [gaugeKinetic, LinearMap.smul_apply, LinearMap.sum_apply]
  change inner ℂ (embed f) (embed ((1/2 : ℂ) • _)) =
    inner ℂ (embed ((1/2 : ℂ) • _)) (embed g)
  rw [map_smul, map_smul, inner_smul_right, inner_smul_left]
  simp only [map_div₀, map_one, map_ofNat]
  congr 1
  change sourcePair f (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3, _) =
    sourcePair (∑ a : LieIndex, ∑ i : Fin 3, ∑ j : Fin 3, _) g
  simp only [pair_sum_left, pair_sum_right]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [sandwich_pair]
  have hc : (fun z => gaugeWeight z i j) = (fun z => gaugeWeight z j i) :=
    funext (fun z => gaugeWeight_symmetric z i j)
  simp only [hc]

theorem nativeAction_pair (f g : QuantumTest) :
    sourcePair f (nativeAction g) = sourcePair (nativeAction f) g := by
  change inner ℂ (embed f) (embed (scalarKinetic g + gaugeKinetic g + multiply potential potential_smooth g)) =
    inner ℂ (embed (scalarKinetic f + gaugeKinetic f + multiply potential potential_smooth f)) (embed g)
  simp only [map_add, inner_add_left, inner_add_right]
  exact congrArg₂ (· + ·) (congrArg₂ (· + ·) (scalarKinetic_pair f g) (gaugeKinetic_pair f g))
    (multiply_pair _ _ f g)

def nativeOperator : H →ₗ.[ℂ] H := realize nativeAction

theorem native_core_pair (f g : Core) :
    inner ℂ (nativeOperator f) (g : H) = inner ℂ (f : H) (nativeOperator g) := by
  obtain ⟨f, rfl⟩ := coreEquiv.surjective f
  obtain ⟨g, rfl⟩ := coreEquiv.surjective g
  change inner ℂ (embed (nativeAction (coreEquiv.symm (coreEquiv f)))) (embed g) =
    inner ℂ (embed f) (embed (nativeAction (coreEquiv.symm (coreEquiv g))))
  rw [coreEquiv.symm_apply_apply, coreEquiv.symm_apply_apply]
  exact (nativeAction_pair f g).symm

#print axioms nativeAction
#print axioms native_core_pair
end LowEnergy.GaussNativeForm
