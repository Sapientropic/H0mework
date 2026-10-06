import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailCoordinateNorm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumTailFourier
open PreparationVacuumWholeTail PreparationVacuumTailSupport PreparationVacuumLocalizedTail
open PreparationVacuumWeyl PreparationVacuumWeylDecay PreparationActualFactor
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology FourierTransform SchwartzMap

def tailSlice (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) : PhysicalMomentum → ℂ :=
  Complex.ofReal∘tailRealSlice B p

theorem tailSlice_smooth (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) :
    ContDiff ℝ ∞ (tailSlice B p) := Complex.ofRealCLM.contDiff.comp (tailRealSlice_smooth B p)

theorem tailSlice_support (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) :
    tsupport (tailSlice B p)⊆positionCompact := by
  apply closure_minimal _ positionCompact_closed
  intro x nonzero
  by_contra outside
  exact nonzero (by simp only [tailSlice,Function.comp_apply,tailRealSlice,
    energyTailFor_position_zero B (flatPosition x,p) outside,Complex.ofReal_zero])

theorem tailSlice_compact (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) :
    HasCompactSupport (tailSlice B p) :=
  positionCompact_compact.of_isClosed_subset isClosed_closure (tailSlice_support B p)

theorem tailSlice_integrable (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) :
    Integrable (tailSlice B p) :=
  (tailSlice_smooth B p).continuous.integrable_of_hasCompactSupport (tailSlice_compact B p)

def tailSchwartzSlice (B : ℕ → Fin 5 → ArrayBound) (p : PhysicalMomentum) : 𝓢(PhysicalMomentum,ℂ) :=
  (tailSlice_compact B p).toSchwartzMap (tailSlice_smooth B p)

theorem tailSlice_derivative_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N m : ℕ) (order : m≤N)
    (input : UnitEnergyInputs B N) (p x : PhysicalMomentum) :
    ‖iteratedFDeriv ℝ m (tailSlice B p) x‖≤tailDerivativeBound B m := by
  rw [show tailSlice B p=Complex.ofRealLI∘tailRealSlice B p from rfl,
    Complex.ofRealLI.norm_iteratedFDeriv_comp_left (tailRealSlice_smooth B p).contDiffAt
      (by exact_mod_cast (le_top : (m : ℕ∞)≤⊤))]
  exact tailRealSlice_derivative_bound B positive N m order input p x

def tailIntegralBound (B : ℕ → Fin 5 → ArrayBound) (m : ℕ) : ℝ :=
  sourcePositionVolume*tailDerivativeBound B m

theorem tailDerivativeBound_nonnegative (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (m : ℕ) : 0 ≤ tailDerivativeBound B m :=
  mul_nonneg (by positivity) (originalTailBudget_nonnegative B positive m)

theorem tailIntegralBound_nonnegative (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (m : ℕ) : 0 ≤ tailIntegralBound B m :=
  mul_nonneg sourcePositionVolume_nonnegative (tailDerivativeBound_nonnegative B positive m)

theorem tailSlice_derivative_integral_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (N m : ℕ) (order : m≤N)
    (input : UnitEnergyInputs B N) (p : PhysicalMomentum) :
    (∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ m (tailSlice B p) x‖)≤tailIntegralBound B m := by
  have coe : (tailSchwartzSlice B p : PhysicalMomentum → ℂ)=tailSlice B p := rfl
  have integrable : Integrable (fun x : PhysicalMomentum=>‖iteratedFDeriv ℝ m (tailSlice B p) x‖) :=
    by simpa only [pow_zero,one_mul,coe] using (tailSchwartzSlice B p).integrable_pow_mul_iteratedFDeriv volume 0 m
  have zero : ∀ x∉positionCompact,iteratedFDeriv ℝ m (tailSlice B p) x=0 := by
    intro x outside
    by_contra nonzero
    exact outside (tailSlice_support B p (support_iteratedFDeriv_subset m nonzero))
  have same : (∫ x in positionCompact,‖iteratedFDeriv ℝ m (tailSlice B p) x‖)=
      ∫ x : PhysicalMomentum,‖iteratedFDeriv ℝ m (tailSlice B p) x‖ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx=>by rw [zero x hx,norm_zero])
  calc
    _=∫ x in positionCompact,‖iteratedFDeriv ℝ m (tailSlice B p) x‖ := same.symm
    _≤∫ _x in positionCompact,tailDerivativeBound B m :=
      setIntegral_mono_on integrable.integrableOn (integrableOn_const positionCompact_compact.measure_ne_top)
        positionCompact_closed.measurableSet (fun x _=>tailSlice_derivative_bound B positive N m order input p x)
    _=tailIntegralBound B m := by
      rw [setIntegral_const]
      change ((volume : Measure PhysicalMomentum) positionCompact).toReal*tailDerivativeBound B m=_
      rw [positionCompact_measure]
      rfl

def tailPartialFourier (B : ℕ → Fin 5 → ArrayBound) (p k : PhysicalMomentum) : ℂ := 𝓕 (tailSlice B p) k

def tailRapidBound (B : ℕ → Fin 5 → ArrayBound) : ℝ :=
  2^101*(tailIntegralBound B 0+2^102*∑ j∈Finset.range 103,tailIntegralBound B j)

theorem tailRapidBound_nonnegative (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) : 0 ≤ tailRapidBound B := by
  unfold tailRapidBound
  exact mul_nonneg (by positivity) (add_nonneg (tailIntegralBound_nonnegative B positive 0)
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _=>tailIntegralBound_nonnegative B positive j)))

theorem tailPartialFourier_rapid_bound (B : ℕ → Fin 5 → ArrayBound)
    (positive : ∀ k i n,0 ≤ B k i n) (input : UnitEnergyInputs B 102) (p k : PhysicalMomentum) :
    (1+‖k‖)^102*‖tailPartialFourier B p k‖≤tailRapidBound B := by
  have zero : ‖tailPartialFourier B p k‖≤tailIntegralBound B 0 := by
    apply (VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ PhysicalMomentum) (tailSlice B p) k).trans
    simpa only [norm_iteratedFDeriv_zero] using tailSlice_derivative_integral_bound B positive 102 0 (by omega) input p
  have high : ‖k‖^102*‖tailPartialFourier B p k‖≤2^102*∑ j∈Finset.range 103,tailIntegralBound B j := by
    have transformed:=Real.pow_mul_norm_iteratedFDeriv_fourier_le
      (K:=(0:ℕ∞)) (N:=(⊤:ℕ∞)) (tailSlice_smooth B p)
      (fun a j _ _=>(tailSchwartzSlice B p).integrable_pow_mul_iteratedFDeriv volume a j)
      (k:=0) (n:=102) (by simp) (by simp) k
    simp at transformed
    apply transformed.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Finset.sum_le_sum (fun j hj=>tailSlice_derivative_integral_bound B positive 102 j
      (by have member:=Finset.mem_range.mp hj;omega) input p)
  have binomial:=add_pow_le (by norm_num:(0:ℝ)≤1) (norm_nonneg k) 102
  simp only [one_pow] at binomial
  calc
    _≤(2^101*(1+‖k‖^102))*‖tailPartialFourier B p k‖ :=
      mul_le_mul_of_nonneg_right binomial (norm_nonneg _)
    _=2^101*(‖tailPartialFourier B p k‖+‖k‖^102*‖tailPartialFourier B p k‖) := by ring
    _≤2^101*(tailIntegralBound B 0+2^102*∑ j∈Finset.range 103,tailIntegralBound B j) :=
      mul_le_mul_of_nonneg_left (add_le_add zero high) (by positivity)
    _=tailRapidBound B := rfl

end LowEnergy.PreparationVacuumTailFourier
