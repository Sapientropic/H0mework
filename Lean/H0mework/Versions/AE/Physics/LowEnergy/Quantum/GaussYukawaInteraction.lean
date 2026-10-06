import H0mework.Versions.AE.Physics.LowEnergy.Quantum.GaussYukawaGrade
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.FiniteGradeAlgebra

/-! Complete source projections and actual time-conjugated normalized Yukawa insertions. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussYukawaInteraction
open GaussCoreHilbert GaussYukawaGrade GaussYukawaOperator NativeHistoryGrade
open GaussUnitaryHistory (HistorySpace sourceFilter reader)
open scoped BigOperators
local instance labelFintype : Fintype Label := Fintype.ofFinite _

def representation : (H →L[ℂ] H) →ₐ[ℂ] (HistorySpace →L[ℂ] HistorySpace) where
  toFun := reader
  map_zero' := GaussUnitaryHistory.reader_zero
  map_one' := GaussUnitaryHistory.reader_one
  map_add' := GaussUnitaryHistory.reader_add
  map_mul' := GaussUnitaryHistory.reader_mul
  commutes' c := by
    change reader (c • (1 : H →L[ℂ] H)) = c • (1 : HistorySpace →L[ℂ] HistorySpace)
    exact (SourceFamilyOperator.constant_smul sourceFilter c (1 : H →L[ℂ] H)).trans
      (congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => c • A) GaussUnitaryHistory.reader_one)

def block (g : Label) : HistorySpace →L[ℂ] HistorySpace := representation (projection g)
def commonGrade : HistorySpace →L[ℂ] HistorySpace := representation GaussYukawaGrade.grade

theorem block_resolution : ∑ g : Label, block g=1 := by
  have h := congrArg representation projection_resolution
  simpa only [map_sum, map_one, block] using h

theorem source_grade_left (g : Label) : projection g * GaussYukawaGrade.grade = (g.2.val : ℂ) • projection g :=
  FiniteGradeAlgebra.weighted_left projection (fun h : Label => (h.2.val : ℂ)) projection_product g

theorem source_grade_right (g : Label) : GaussYukawaGrade.grade * projection g = (g.2.val : ℂ) • projection g :=
  FiniteGradeAlgebra.weighted_right projection (fun h : Label => (h.2.val : ℂ)) projection_product g

theorem block_grade_left (g : Label) : block g*commonGrade=(g.2.val : ℂ) • block g :=
  (map_mul representation (projection g) GaussYukawaGrade.grade).symm.trans
    ((congrArg representation (source_grade_left g)).trans (SourceFamilyOperator.constant_smul sourceFilter (g.2.val : ℂ) (projection g)))

theorem block_grade_right (g : Label) : commonGrade*block g=(g.2.val : ℂ) • block g :=
  (map_mul representation GaussYukawaGrade.grade (projection g)).symm.trans
    ((congrArg representation (source_grade_right g)).trans (SourceFamilyOperator.constant_smul sourceFilter (g.2.val : ℂ) (projection g)))

theorem common_raises : commonGrade*representation bounded = representation bounded*commonGrade+representation bounded := by
  calc
    _ = representation (GaussYukawaGrade.grade*bounded) :=
      (GaussUnitaryHistory.reader_mul GaussYukawaGrade.grade bounded).symm
    _ = representation (bounded*GaussYukawaGrade.grade+bounded) :=
      congrArg representation GaussYukawaGrade.bounded_raises
    _ = representation (bounded*GaussYukawaGrade.grade)+representation bounded :=
      GaussUnitaryHistory.reader_add (bounded*GaussYukawaGrade.grade) bounded
    _ = _ := congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => A+representation bounded)
      (GaussUnitaryHistory.reader_mul bounded GaussYukawaGrade.grade)

theorem time_grade (t : ℝ) : commonGrade*GaussGradedUnitary.time t = GaussGradedUnitary.time t*commonGrade := by
  have h : commonGrade=∑ g : Label, (g.2.val : ℂ) • block g := by
    change representation (∑ g : Label, (g.2.val : ℂ) • projection g) = _
    exact (map_sum representation _ _).trans
      (Finset.sum_congr rfl (fun g _ => SourceFamilyOperator.constant_smul sourceFilter (g.2.val : ℂ) (projection g)))
  rw [h]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  apply Finset.sum_congr rfl
  intro g _
  exact congrArg (fun A : HistorySpace →L[ℂ] HistorySpace => (g.2.val : ℂ) • A)
    (GaussGradedUnitary.time_blocks t g)

def interaction (t : ℝ) : HistorySpace →L[ℂ] HistorySpace :=
  GaussGradedUnitary.time (-t) * representation bounded * GaussGradedUnitary.time t

private theorem conjugate_raises {A : Type*} [Ring A] (G U V B : A)
    (hU : G*U=U*G) (hV : G*V=V*G) (hB : G*B=B*G+B) :
    G*(V*B*U)=(V*B*U)*G+V*B*U := by
  calc
    _ = (G*V)*B*U := by simp only [mul_assoc]
    _ = V*(G*B)*U := by rw [hV]; simp only [mul_assoc]
    _ = V*(B*G+B)*U := by rw [hB]
    _ = V*B*(G*U)+V*B*U := by noncomm_ring
    _ = _ := by rw [hU]; simp only [mul_assoc]

theorem interaction_raises (t : ℝ) : commonGrade*interaction t=interaction t*commonGrade+interaction t :=
  conjugate_raises commonGrade (GaussGradedUnitary.time t) (GaussGradedUnitary.time (-t))
    (representation bounded) (time_grade t) (time_grade (-t)) common_raises

def weight (g : Label) : ℤ := g.2.val

theorem weight_bounds (g : Label) : 0 ≤ weight g ∧ weight g ≤ 56 := by
  have h := g.2.isLt
  dsimp only [weight]
  constructor <;> omega

theorem state_words_zero (times : List ℝ) (long : 56 < times.length) :
    (times.map interaction).prod=0 :=
  FiniteGradeAlgebra.family_words_zero commonGrade block weight block_resolution
    (fun g => by simpa only [weight, Int.cast_natCast] using block_grade_left g)
    (fun g => by simpa only [weight, Int.cast_natCast] using block_grade_right g)
    0 56 weight_bounds interaction interaction_raises times (by omega)

theorem response_words_zero (times : List ℝ) (long : 112 < times.length) :
    (times.map (fun t => FiniteGradeAlgebra.commutator (interaction t))).prod=0 :=
  FiniteGradeAlgebra.family_commutators_zero commonGrade block weight block_resolution
    (fun g => by simpa only [weight, Int.cast_natCast] using block_grade_left g)
    (fun g => by simpa only [weight, Int.cast_natCast] using block_grade_right g)
    0 56 weight_bounds interaction interaction_raises times (by omega)

#print axioms block_resolution
#print axioms block_grade_left
#print axioms time_grade
#print axioms interaction_raises
#print axioms state_words_zero
#print axioms response_words_zero
end LowEnergy.GaussYukawaInteraction
