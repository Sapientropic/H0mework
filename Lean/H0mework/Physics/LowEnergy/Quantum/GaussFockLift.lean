import H0mework.Physics.LowEnergy.Quantum.GaussAdjointHistory
import H0mework.Physics.LowEnergy.Quantum.SourceQuantumCARBound

/-! Bounded full-Fock readers on the original Gauss100 half-density completion. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFockLift
open GaussHalfDensity GaussCoreHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open scoped BigOperators

abbrev Base : Type := GaussHalfDensity.BaseHilbert
abbrev Flat : Type := GaussHalfDensity.FlatFockHilbert
abbrev FiberOp := FockFiber →L[ℂ] FockFiber

def slot (word : Occupation) : Base →L[ℂ] Flat where
  toFun := fun f : Base => WithLp.toLp 2 (fun w : Occupation => if w=word then f else 0)
  map_add' := by
    intro f g
    apply PiLp.ext
    intro w
    change (if w=word then f+g else 0) = (if w=word then f else 0)+(if w=word then g else 0)
    by_cases h : w=word <;> simp [h]
  map_smul' := by
    intro c f
    apply PiLp.ext
    intro w
    change (if w=word then c • f else 0) = c • (if w=word then f else 0)
    by_cases h : w=word <;> simp [h]
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Occupation => Base)).comp
    apply continuous_pi
    intro w
    by_cases h : w=word
    · simp only [if_pos h]
      exact continuous_id
    · simp only [if_neg h]
      exact continuous_const

theorem slot_apply (word output : Occupation) (f : Base) :
    slot word f output = if output=word then f else 0 := rfl

def entry (A : FiberOp) (output input : Occupation) : ℂ :=
  A (EuclideanSpace.single input 1) output

def flatLift (A : FiberOp) : Flat →L[ℂ] Flat :=
  ∑ output : Occupation, ∑ input : Occupation,
    entry A output input • (slot output).comp
      (PiLp.proj 2 (fun _ : Occupation => Base) input)

theorem flatLift_apply (A : FiberOp) (f : Flat) (output : Occupation) :
    flatLift A f output = ∑ input : Occupation, entry A output input • f input := by
  simp only [flatLift, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, slot_apply,
    smul_ite, smul_zero]
  simp [Finset.sum_ite_eq]

theorem entry_identity (output input : Occupation) :
    entry (1 : FiberOp) output input = if output=input then 1 else 0 := by
  simp [entry, EuclideanSpace.single]

theorem flatLift_identity : flatLift (1 : FiberOp) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro output
  simp [flatLift_apply, entry_identity, ite_smul]

theorem entry_add (A B : FiberOp) (output input : Occupation) :
    entry (A+B) output input = entry A output input + entry B output input := rfl

theorem flatLift_add (A B : FiberOp) : flatLift (A+B) = flatLift A+flatLift B := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro output
  simp [flatLift_apply, entry_add, add_smul, Finset.sum_add_distrib]

theorem entry_mul (A B : FiberOp) (output input : Occupation) :
    entry (A*B) output input = ∑ middle : Occupation, entry A output middle * entry B middle input := by
  have expansion : B (EuclideanSpace.single input 1) =
      ∑ middle : Occupation, entry B middle input • EuclideanSpace.single middle 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, entry, EuclideanSpace.single, Pi.single_apply]
  change A (B (EuclideanSpace.single input 1)) output = _
  rw [expansion, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem flatLift_mul (A B : FiberOp) : flatLift (A*B) = flatLift A*flatLift B := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro output
  change flatLift (A*B) f output = flatLift A (flatLift B f) output
  simp only [flatLift_apply, entry_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]

theorem entry_pair (A B : FiberOp)
    (paired : ∀ f g, inner ℂ (A f) g = inner ℂ f (B g)) (output input : Occupation) :
    (starRingEnd ℂ) (entry A output input) = entry B input output := by
  have h := paired (EuclideanSpace.single input 1) (EuclideanSpace.single output 1)
  simpa [PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single, Pi.single_apply,
    mul_ite, ite_mul, entry] using h

theorem flatLift_pair (A B : FiberOp) (paired : ∀ f g, inner ℂ (A f) g = inner ℂ f (B g))
    (f g : Flat) : inner ℂ (flatLift A f) g = inner ℂ f (flatLift B g) := by
  simp only [PiLp.inner_apply, flatLift_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  apply Finset.sum_congr rfl
  intro output _
  rw [entry_pair A B paired]

def lift (A : FiberOp) : H →L[ℂ] H :=
  GaussHalfDensity.fockHalfDensityEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((flatLift A).comp GaussHalfDensity.fockHalfDensityEquiv.toContinuousLinearEquiv.toContinuousLinearMap)

theorem lift_apply (A : FiberOp) (f : H) :
    lift A f = GaussHalfDensity.fockHalfDensityEquiv.symm (flatLift A (GaussHalfDensity.fockHalfDensityEquiv f)) := rfl

theorem lift_identity : lift (1 : FiberOp) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [lift_apply, flatLift_identity, one_apply_eq_self, LinearIsometryEquiv.symm_apply_apply]

theorem lift_add (A B : FiberOp) : lift (A+B) = lift A+lift B := by
  apply ContinuousLinearMap.ext
  intro f
  simp [lift_apply, flatLift_add, map_add]

theorem lift_mul (A B : FiberOp) : lift (A*B) = lift A*lift B := by
  apply ContinuousLinearMap.ext
  intro f
  change lift (A*B) f = lift A (lift B f)
  simp [lift_apply, flatLift_mul]

theorem lift_pair (A B : FiberOp) (paired : ∀ f g, inner ℂ (A f) g = inner ℂ f (B g))
    (f g : H) : inner ℂ (lift A f) g = inner ℂ f (lift B g) := by
  let U := GaussHalfDensity.fockHalfDensityEquiv
  rw [← U.inner_map_map (lift A f) g, ← U.inner_map_map f (lift B g)]
  simp only [lift_apply, U, LinearIsometryEquiv.apply_symm_apply]
  exact flatLift_pair A B paired _ _

#print axioms flatLift_identity
#print axioms flatLift_mul
#print axioms lift_pair
end LowEnergy.GaussFockLift
