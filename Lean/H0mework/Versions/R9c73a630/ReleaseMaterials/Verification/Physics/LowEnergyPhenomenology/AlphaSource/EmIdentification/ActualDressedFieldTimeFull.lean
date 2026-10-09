import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNumberFieldNoether

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedFieldTime
open GaussCoreHilbert CanonicalGradedSpatialSource
open PreparationVacuumJointFieldResponse PreparationVacuumMixedFieldReturn
open PreparationVacuumRawJointFeedback PreparationVacuumYukawaTransport
open ActualDressedNumberSector ActualDressedNumberField
open FullYSourceCutoffVolterra NativeHistoryGrade
open scoped BigOperators Topology
local instance labelFinite : Fintype Label := Fintype.ofFinite _
local instance fieldTimeReal : NormedAlgebra ℝ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance fieldTimeRational : NormedAlgebra ℚ (H→L[ℂ]H) := NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] jointCompression jointY jointGenerator physicalTime

theorem actual_field_C_grade (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (h : Field289) :
    Commute GaussYukawaGrade.grade (jointCompression p F h) := by
  have expansion : GaussYukawaGrade.grade = ∑ g : Label, (g.2.val:ℂ) • projection g := by
    calc
      _ = GaussYukawaGrade.grade * ∑ g : Label, projection g := by rw [projection_resolution,mul_one]
      _ = _ := by simp only [Finset.mul_sum,GaussYukawaInteraction.source_grade_right]
  show GaussYukawaGrade.grade*jointCompression p F h=jointCompression p F h*GaussYukawaGrade.grade
  rw [expansion]
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun A : H→L[ℂ]H=>(g.2.val:ℂ) • A) (actual_joint_compression_blocks p F h g).eq

theorem actual_field_generator_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) : jointGenerator p F 0 h=jointCompression p F h+jointY (finiteRetainer p F) h := by
  unfold jointGenerator
  have zero : (0:ℂ) • (1:H→L[ℂ]H)=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact zero_smul ℂ x
  rw [zero,sub_zero]

private theorem homogeneous_product {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    [SMulCommClass ℂ R R] (G B A : R) (n : ℕ)
    (hB : G*B=B*G+(n:ℂ) • B) (hA : G*A=A*G+A) :
    G*(B*A)=(B*A)*G+((n+1:ℕ):ℂ) • (B*A) := by
  calc
    _=(G*B)*A := by rw [mul_assoc]
    _=(B*G+(n:ℂ) • B)*A := by rw [hB]
    _=B*(A*G+A)+(n:ℂ) • (B*A) := by rw [add_mul,smul_mul_assoc,mul_assoc,hA]
    _=_ := by simp only [mul_add,Nat.cast_add,Nat.cast_one,add_smul,one_smul,mul_assoc];abel

theorem actual_field_prefix_terminal (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) :
    finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) 56 t *
      jointY (finiteRetainer p F) h=0 := by
  have paid := homogeneous_product GaussYukawaGrade.grade
    (finitePrefix (jointCompression p F h) (jointY (finiteRetainer p F) h) 56 t)
    (jointY (finiteRetainer p F) h) 56
    (finitePrefix_homogeneous _ _ _ (actual_field_C_grade p F h)
      (actual_joint_Y_raises h (finiteRetainer p F)) 56 t)
    (actual_joint_Y_raises h (finiteRetainer p F))
  exact source_homogeneous_zero _ 57 paid (by norm_num)

theorem actual_field_prefix_derivative (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) :
    HasDerivAt (partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 56)
      (partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 56 t *
        ((-Complex.I) • jointGenerator p F 0 h)) t := by
  have paid := partialEvolution_derivative (jointCompression p F h) (jointY (finiteRetainer p F) h) 56 t
  simpa only [actual_field_generator_source,mul_smul_comm,
    actual_field_prefix_terminal,smul_zero,sub_zero] using paid

theorem actual_field_time_finitePrefix (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (h : Field289) (t : ℝ) :
    physicalTime p F t h=partialEvolution (jointCompression p F h) (jointY (finiteRetainer p F) h) 56 t := by
  unfold physicalTime SourceFiniteUnitary.time
  exact (autonomous_evolution_unique _ _ (actual_field_prefix_derivative p F h)
    (partialEvolution_initial _ _ 56) t).symm

end LowEnergy.GaussComposite.ActualDressedFieldTime
