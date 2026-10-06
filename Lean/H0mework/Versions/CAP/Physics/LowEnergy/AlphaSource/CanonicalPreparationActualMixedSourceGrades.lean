import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationTailActualPreparation
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalGradedMixedSource
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.EmIdentification.CompositeCurrentResponse
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPhysicalYResolvent

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualPreparedMixed
open GaussCoreHilbert GaussYukawaGrade GaussComposite CanonicalGradedMixed CanonicalGradedMixedSource
open CanonicalGradedCurrent CanonicalGradedSpatialKernel CanonicalGradedSpatialSource
open CanonicalPhysicalSpatial CanonicalPhysicalYResolvent FullYSourceCutoffVolterra
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)
open GaussComposite.SourceGraph
open scoped BigOperators Topology InnerProductSpace
local instance labelFintype : Fintype NativeHistoryGrade.Label := Fintype.ofFinite _

abbrev Op := H →L[ℂ] H

theorem gradeZero_norm : ‖gradeZeroProjection‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖gradeZeroPiece x‖≤1*‖x‖
  simpa only [one_mul] using grade_zero_piece_bound x

theorem gradeZero_left : gradeZeroProjection*GaussYukawaGrade.grade=0 := by
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro word
  rw [mul_apply_eq_comp,grade_zero_projection_apply,source_grade_apply]
  by_cases h : (NativeHistoryGrade.sourceLabel word).2=0 <;> simp [h]

theorem gradeZero_right : GaussYukawaGrade.grade*gradeZeroProjection=0 := by
  apply ContinuousLinearMap.ext
  exact grade_zero_projected

theorem gradeZero_unbalanced (A : Op) (a : ℤ) (hA : Homogeneous A a) (ha : a≠0) :
    gradeZeroProjection*A*gradeZeroProjection=0 := by
  apply ContinuousLinearMap.ext
  intro x
  have hl:=congrArg (fun T : Op=>T (A (gradeZeroProjection x))) gradeZero_left
  have hr:=grade_zero_projected x
  have h:=congrArg (fun T : Op=>gradeZeroProjection (T (gradeZeroProjection x))) hA
  change gradeZeroProjection (GaussYukawaGrade.grade (A (gradeZeroProjection x)))=0 at hl
  change gradeZeroProjection (GaussYukawaGrade.grade (A (gradeZeroProjection x)))=
    gradeZeroProjection (A (GaussYukawaGrade.grade (gradeZeroProjection x))+(a:ℂ) • A (gradeZeroProjection x)) at h
  rw [hl,hr,map_zero,zero_add,map_smul] at h
  exact (smul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast ha)

theorem localGauge_grade (A : NativeCurrent) : Homogeneous (current A) 0 := by
  have commute : GaussYukawaGrade.grade*current A=current A*GaussYukawaGrade.grade := by
    simp only [GaussYukawaGrade.grade,Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm]
    apply Finset.sum_congr rfl
    intro g _
    exact congrArg (fun T : Op=>(g.2.val:ℂ) • T)
      (CanonicalGradedLocalCurrent.localReader_blocks A.localizer A.component A.generator g).eq
  unfold Homogeneous
  rw [commute]
  apply ContinuousLinearMap.ext
  intro x
  simp

def gauge48 (phi : CanonicalGradedSpatial.Localizer) (mu : Fin 4) (a : Fin 12) : NativeCurrent :=
  ⟨phi,Fin.cases .temporal .spatial mu,
    GaussNativeForm.lieBasis (Fin.cast SourceQuantumNativeDimensions.nativeLie_finrank.symm a)⟩

theorem gauge48_grade (phi : CanonicalGradedSpatial.Localizer) (mu : Fin 4) (a : Fin 12) :
    Homogeneous (current (gauge48 phi mu a)) 0 := localGauge_grade _

def rawScalar70 (a : SourceScalarFock.ScalarIndex) : Op := rawScalar (scalarCoordinate a)
def sharpScalar70 (a : SourceScalarFock.ScalarIndex) : Op := dualScalar (scalarCoordinate a)

theorem rawScalar70_grade (a : SourceScalarFock.ScalarIndex) : Homogeneous (rawScalar70 a) 1 :=
  rawScalar_raises (scalarCoordinate a)

theorem sharpScalar70_grade (a : SourceScalarFock.ScalarIndex) : Homogeneous (sharpScalar70 a) (-1) :=
  dualScalar_lowers (scalarCoordinate a)

def actualBand (a : SourceScalarFock.ScalarIndex) (A : NativeCurrent) : Fin 3→Op :=
  ![(1/2:ℂ) • sharpScalar70 a,current A,(1/2:ℂ) • rawScalar70 a]

theorem actualBand_grade (a : SourceScalarFock.ScalarIndex) (A : NativeCurrent) (i : Fin 3) :
    Homogeneous (actualBand a A i) (bandGrade i) := by
  fin_cases i
  · exact homogeneous_smul _ _ (sharpScalar70_grade a) _
  · exact localGauge_grade A
  · exact homogeneous_smul _ _ (rawScalar70_grade a) _

def actualReader (a : SourceScalarFock.ScalarIndex) (A : NativeCurrent) : Op := ∑ i,actualBand a A i

theorem actualReader_source (a : SourceScalarFock.ScalarIndex) (A : NativeCurrent) :
    actualReader a A=current A+realPartScalar (scalarCoordinate a) := by
  simp only [actualReader,actualBand,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,rawScalar70,sharpScalar70,realPartScalar,smul_add]
  abel

theorem actual_path_count : (∑ i : Fin 3, ∑ j : Fin 3,(paths (bandGrade i) (bandGrade j)).card)=15 := by decide

theorem completedLeg_gradeZero (addition : Bool) (a s : Fin 2) (f : Profile) :
    reader gradeZeroProjection (inclusion (completedLeg addition a s f))=
      inclusion (completedLeg addition a s f) := by
  let S : Set Profile := {f | reader gradeZeroProjection (inclusion (completedLeg addition a s f))=
    inclusion (completedLeg addition a s f)}
  have legC : Continuous fun f : Profile=>inclusion (completedLeg addition a s f) :=
    inclusion.continuous.comp (completedLeg addition a s).cont
  have closed : IsClosed S := isClosed_eq ((reader gradeZeroProjection).cont.comp legC) legC
  have covers : Set.univ⊆S := by
    rw [←Dense.closure_eq core_dense]
    apply closure_minimal _ closed
    rintro _ ⟨g,rfl⟩
    change reader gradeZeroProjection (inclusion (completedLeg addition a s (core g)))=
      inclusion (completedLeg addition a s (core g))
    rw [completedLeg_core]
    exact source_leg_grade_zero_fixed addition a s (seedSection g) _ (seedSection_apply g)
  exact covers (Set.mem_univ f)

end LowEnergy.PreparationVacuumActualPreparedMixed
