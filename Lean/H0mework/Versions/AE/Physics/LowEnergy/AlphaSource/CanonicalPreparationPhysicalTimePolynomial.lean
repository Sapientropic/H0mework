import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationPhysicalFeedbackField

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalHalfAxis
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumGradedTransport
open PreparationVacuumUncutYukawa PreparationVacuumYukawaTransport
open FullYSourceCutoffVolterra
open scoped Topology BigOperators Matrix InnerProductSpace
abbrev Index:=GaussUnitaryHistory.Index
abbrev Op:=H→L[ℂ] H
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointGenerator

def actualC (p : PhysicalMomentum) (F : Index) : Op:=CanonicalPhysicalSpatial.compression p F

def actualA (p : PhysicalMomentum) (F : Index) : Op:=
  uncutOperator 0 (PreparationVacuumYukawaTransport.finiteRetainer p F) 0

theorem actualGenerator_source (p : PhysicalMomentum) (F : Index) :
    jointGenerator p F 0 0=actualC p F+actualA p F :=by
  have h:=(jointGenerator_ray (0:Field289) p F 0).self_of_nhds
  simp only [zero_smul] at h
  rw [h]
  change transportedCompression 0 p F 0+uncutOperator 0 (finiteRetainer p F) 0-(0:ℂ) • (1:Op)=_
  rw [transportedCompression_zero]
  have zero : (0:ℂ) • (1:Op)=0:=by
    apply ContinuousLinearMap.ext;intro x
    exact zero_smul ℂ x
  rw [zero,sub_zero]
  rfl

theorem actualC_symmetric (p : PhysicalMomentum) (F : Index) : IsSelfAdjoint (actualC p F):=
  CanonicalPhysicalSpatial.compression_selfAdjoint p F

theorem actualC_grade (p : PhysicalMomentum) (F : Index) : Commute GaussYukawaGrade.grade (actualC p F):=
  CanonicalPhysicalYResolvent.compression_grade p F

theorem actualA_raises (p : PhysicalMomentum) (F : Index) :
    GaussYukawaGrade.grade*actualA p F=actualA p F*GaussYukawaGrade.grade+actualA p F :=
  uncutOperator_raises _ _ _

private theorem homogeneous_product {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    [SMulCommClass ℂ R R] (G B A : R) (n : ℕ)
    (hB : G*B=B*G+(n:ℂ) • B) (hA : G*A=A*G+A) :
    G*(B*A)=(B*A)*G+((n+1:ℕ):ℂ) • (B*A) :=by
  calc
    _=(G*B)*A :=by rw [mul_assoc]
    _=(B*G+(n:ℂ) • B)*A :=by rw [hB]
    _=B*(A*G+A)+(n:ℂ) • (B*A) :=by rw [add_mul,smul_mul_assoc,mul_assoc,hA]
    _=_ :=by simp only [mul_add,Nat.cast_add,Nat.cast_one,add_smul,one_smul,mul_assoc];abel

theorem actual_prefix_terminal (p : PhysicalMomentum) (F : Index) (t : ℝ) :
    finitePrefix (actualC p F) (actualA p F) 56 t*actualA p F=0 :=by
  have h:=homogeneous_product GaussYukawaGrade.grade
    (finitePrefix (actualC p F) (actualA p F) 56 t) (actualA p F) 56
    (finitePrefix_homogeneous _ _ _ (actualC_grade p F) (actualA_raises p F) 56 t)
    (actualA_raises p F)
  exact source_homogeneous_zero _ 57 h (by norm_num)

theorem actual_prefix_derivative (p : PhysicalMomentum) (F : Index) (t : ℝ) :
    HasDerivAt (partialEvolution (actualC p F) (actualA p F) 56)
      (partialEvolution (actualC p F) (actualA p F) 56 t*((-Complex.I) • jointGenerator p F 0 0)) t :=by
  have h:=partialEvolution_derivative (actualC p F) (actualA p F) 56 t
  simpa only [actualGenerator_source,mul_smul_comm,actual_prefix_terminal,smul_zero,sub_zero] using h

theorem actual_time_finitePrefix (p : PhysicalMomentum) (F : Index) (t : ℝ) :
    physicalTime p F t 0=partialEvolution (actualC p F) (actualA p F) 56 t :=by
  exact (autonomous_evolution_unique _ _ (actual_prefix_derivative p F)
    (partialEvolution_initial _ _ 56) t).symm

/-- This norm is the actual uncut retainer operator at the same p,F. -/
def actualGrowth (p : PhysicalMomentum) (F : Index) (T : ℝ) : ℝ:=
  ∑j∈Finset.range 57,(T*‖actualA p F‖)^j

theorem actualGrowth_nonnegative (p : PhysicalMomentum) (F : Index) (T : ℝ) (hT : 0≤T) :
    0≤actualGrowth p F T:=by
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem actualGrowth_mono (p : PhysicalMomentum) (F : Index) {a b : ℝ} (ha : 0≤a) (hab : a≤b) :
    actualGrowth p F a≤actualGrowth p F b :=by
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (mul_nonneg ha (norm_nonneg _))
    (mul_le_mul_of_nonneg_right hab (norm_nonneg _)) j

theorem actual_time_bound (p : PhysicalMomentum) (F : Index) (t : ℝ) :
    ‖physicalTime p F t 0‖≤actualGrowth p F |t| :=by
  rw [actual_time_finitePrefix]
  exact partialEvolution_bound _ _ (actualC_symmetric p F) 56 t

theorem actual_time_window (p : PhysicalMomentum) (F : Index) (T t : ℝ)
    (within : |t|≤T) : ‖physicalTime p F t 0‖≤actualGrowth p F T:=
  (actual_time_bound p F t).trans (actualGrowth_mono p F (abs_nonneg t) within)

end LowEnergy.PreparationVacuumPhysicalHalfAxis
