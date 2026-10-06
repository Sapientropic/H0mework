import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussFockLift

/-! Same-source normalized CAR readers and their full two-time weak responses. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussCARHistory
open GaussFockLift GaussCoreHilbert GaussAdjointHistory GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open SaturationMonoid.PhysicsCore QuantizationCheck.Fermion
open scoped BigOperators ContDiff
attribute [local instance] SourceRealScalarFock.branchOrder

def createFiber (i : Mode) : FiberOp :=
  (SourceCARBound.createOp i).mkContinuous 1 (by intro f; simpa only [one_mul] using SourceCARBound.create_norm_le i f)

def annihilateFiber (i : Mode) : FiberOp :=
  (SourceCARBound.annihilateOp i).mkContinuous 1 (by intro f; simpa only [one_mul] using SourceCARBound.annihilate_norm_le i f)

theorem fiber_car (i j : Mode) : annihilateFiber i * createFiber j + createFiber j * annihilateFiber i =
    if i=j then 1 else 0 := by
  apply ContinuousLinearMap.ext
  intro f
  by_cases hij : i=j
  · subst j
    change SourceCARBound.annihilateOp i (SourceCARBound.createOp i f) +
      SourceCARBound.createOp i (SourceCARBound.annihilateOp i f) = _
    simpa using SourceCARBound.car_same i f
  · apply fiberCoordinates.injective
    change fiberCoordinates (SourceCARBound.annihilateOp i (SourceCARBound.createOp j f) +
      SourceCARBound.createOp j (SourceCARBound.annihilateOp i f)) = _
    simp only [map_add, SourceCARBound.createOp, SourceCARBound.annihilateOp, SourceCARBound.coordinates_liftOp,
      LowEnergy.Fermion.creation_apply, LowEnergy.Fermion.annihilation_apply]
    simpa [hij] using LowEnergy.Fermion.annihilate_create_car i j (fiberCoordinates f)

def create (i : Mode) : H →L[ℂ] H := lift (createFiber i)
def annihilate (i : Mode) : H →L[ℂ] H := lift (annihilateFiber i)

theorem create_pair (i : Mode) (f g : H) : inner ℂ (create i f) g = inner ℂ f (annihilate i g) :=
  lift_pair _ _ (SourceCARBound.create_adjoint i) f g

theorem annihilate_pair (i : Mode) (f g : H) : inner ℂ (annihilate i f) g = inner ℂ f (create i g) :=
  lift_pair _ _ (SourceCARBound.annihilate_adjoint i) f g

theorem car (i j : Mode) : annihilate i * create j + create j * annihilate i = if i=j then 1 else 0 := by
  have h := congrArg lift (fiber_car i j)
  rw [lift_add, lift_mul, lift_mul] at h
  by_cases hij : i=j
  · simpa only [create, annihilate, if_pos hij, lift_identity] using h
  · have hz : lift (0 : FiberOp) = 0 := by
      apply ContinuousLinearMap.ext
      intro f
      rw [lift_apply]
      have hflat : flatLift (0 : FiberOp) (GaussHalfDensity.fockHalfDensityEquiv f) = 0 := by
        apply PiLp.ext
        intro w
        simp [flatLift_apply, entry]
      rw [hflat, map_zero]
      rfl
    simpa only [create, annihilate, if_neg hij, hz] using h

theorem norm_partition (i : Mode) (f : H) : ‖create i f‖^2 + ‖annihilate i f‖^2 = ‖f‖^2 := by
  have hcar := congrArg (fun T : H →L[ℂ] H => T f) (car i i)
  simp only [if_true, one_apply_eq_self] at hcar
  have h : inner ℂ (create i f) (create i f) + inner ℂ (annihilate i f) (annihilate i f) = inner ℂ f f := by
    rw [create_pair, annihilate_pair, ← inner_add_right]
    exact congrArg (inner ℂ f) hcar
  simp only [inner_self_eq_norm_sq_to_K] at h
  exact_mod_cast h

theorem create_bound (i : Mode) (f : H) : ‖create i f‖ ≤ ‖f‖ := by
  have h := norm_partition i f
  nlinarith [sq_nonneg ‖annihilate i f‖, norm_nonneg f, norm_nonneg (create i f)]

theorem annihilate_bound (i : Mode) (f : H) : ‖annihilate i f‖ ≤ ‖f‖ := by
  have h := norm_partition i f
  nlinarith [sq_nonneg ‖create i f‖, norm_nonneg f, norm_nonneg (annihilate i f)]

def kernel (A : H →L[ℂ] H) (t s : ℝ) : H →L[ℂ] H :=
  (evolution t).adjoint.comp (A.comp (evolution s))

def response (A : H →L[ℂ] H) (t s : ℝ) (x y : H) : ℂ :=
  inner ℂ (evolution t x) (A (evolution s y))

theorem kernel_pair (A : H →L[ℂ] H) (t s : ℝ) (x y : H) :
    inner ℂ x (kernel A t s y) = response A t s x y :=
  ContinuousLinearMap.adjoint_inner_right (evolution t) x (A (evolution s y))

theorem response_left (A : H →L[ℂ] H) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response A u s x y)
      (Complex.I * response A t s (diagonal x) y) t := by
  have h := (GaussDiagonalGrade.history_derivative x t).inner ℂ (hasDerivAt_const t (A (evolution s y)))
  simpa [response, inner_smul_left] using h

theorem response_right (A : H →L[ℂ] H) (t s : ℝ) (x y : diagonal.domain) :
    HasDerivAt (fun u => response A t u x y)
      (-Complex.I * response A t s x (diagonal y)) s := by
  have hA := A.restrictScalars ℝ |>.hasFDerivAt.comp_hasDerivAt s (GaussDiagonalGrade.history_derivative y s)
  have h := (hasDerivAt_const s (evolution t x)).inner ℂ hA
  simpa [response, inner_smul_right] using h

theorem annihilator_response_bound (i : Mode) (t s : ℝ) (x y : H) :
    ‖response (annihilate i) t s x y‖ ≤ ‖x‖*‖y‖ := by
  have hx := NativeHistoryGrade.history_contraction diagonal diagonal_pair t x
  have hy := (annihilate_bound i (evolution s y)).trans
    (NativeHistoryGrade.history_contraction diagonal diagonal_pair s y)
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul hx hy (norm_nonneg _) (norm_nonneg _))

#print axioms car
#print axioms norm_partition
#print axioms kernel_pair
#print axioms response_left
#print axioms response_right
#print axioms annihilator_response_bound
end LowEnergy.GaussCARHistory
