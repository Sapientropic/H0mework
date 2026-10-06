import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationNativeCutoff
import Mathlib.LinearAlgebra.Matrix.Block

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationChartGuard
open SaturationMonoid.PhysicsCore
open Stage9C.Material.SpinPair SU7MotherLieAlgebra SU7MotherGaugeTheory
open StageNineHolonomicField StageNineCoframeGravityGaugeRegularity
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumGaugeSliceCoordinates SourceQuantumResidualFlow
open PreparationCoordinates PreparationScalarCoordinates
open GaussHistoryHilbert
open scoped RealInnerProductSpace

private theorem color_entry_re (B : SU3BlockLieMatrix) (i j : Fin 3) :
    (B.val j i).re=-(B.val i j).re := by
  have h:=congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M i j).re) B.property.1
  simpa [Matrix.star_apply] using h

private theorem color_entry_im (B : SU3BlockLieMatrix) (i j : Fin 3) :
    (B.val j i).im=(B.val i j).im := by
  have h:=congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => (M i j).im) B.property.1
  simpa [Matrix.star_apply] using neg_inj.mp h

theorem original_generator_rows (a : P286LieBlockData) (j : Fin 3) :
    (nativeCoordinates (jointP286CoordinateLieBracket (colorGenerator j) (p286CoordinateEquiv a))).1 6 =
      ![-(a.1.val 0 1).re,(a.1.val 0 1).im,0] j ∧
    (nativeCoordinates (jointP286CoordinateLieBracket (colorGenerator j) (p286CoordinateEquiv a))).1 0 =
      ![(a.1.val 0 0).im+(a.1.val 2 2).im/2,0,-(a.1.val 0 1).im] j := by
  have h00:=color_entry_re a.1 0 0
  have h11:=color_entry_re a.1 1 1
  have h01:=color_entry_re a.1 0 1
  have h01i:=color_entry_im a.1 0 1
  have ht:=congrArg Complex.im a.1.property.2
  simp [Matrix.trace,Fin.sum_univ_succ] at ht
  unfold jointP286CoordinateLieBracket colorGenerator
  rw [p286CoordinateEquiv.symm_apply_apply,p286CoordinateEquiv.symm_apply_apply,nativeCoordinates_apply]
  change ((p286LieBracket (sourceColorP286Generator j) a).1.val 0 0).im =
      ![-(a.1.val 0 1).re,(a.1.val 0 1).im,0] j ∧
    ((p286LieBracket (sourceColorP286Generator j) a).1.val 0 1).re =
      ![(a.1.val 0 0).im+(a.1.val 2 2).im/2,0,-(a.1.val 0 1).im] j
  fin_cases j <;> constructor <;>
    norm_num [p286LieBracket,suLieBracket,sourceColorP286Generator_color,
      sourceColorRaw,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_three]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals linarith

private def nativeBracket (b : NativeLie) : NativeLie →ₗ[ℝ] NativeLie where
  toFun a := jointP286CoordinateLieBracket a b
  map_add' a c := jointP286CoordinateLieBracket_add_left a c b
  map_smul' r a := jointP286CoordinateLieBracket_smul_left r a b

private def colorRead : NativeLie →ₗ[ℝ] (Fin 8 → ℝ) :=
  (LinearMap.fst ℝ (Fin 8 → ℝ) ((Fin 3 → ℝ)×ℝ)).comp nativeCoordinates.toLinearMap

private def sixRead (b : NativeLie) : NativeLie →ₗ[ℝ] ℝ :=
  (LinearMap.proj 6).comp (colorRead.comp (nativeBracket b))

private def zeroRead (b : NativeLie) : NativeLie →ₗ[ℝ] ℝ :=
  (LinearMap.proj 0).comp (colorRead.comp (nativeBracket b))

theorem original_combination_rows (x : Fin 3 → ℝ) (b : NativeLie) :
    (nativeCoordinates (jointP286CoordinateLieBracket (colorCombination x) b)).1 6 =
      -(nativeCoordinates b).1 0*x 0+(nativeCoordinates b).1 1*x 1 ∧
    (nativeCoordinates (jointP286CoordinateLieBracket (colorCombination x) b)).1 0 =
      ((nativeCoordinates b).1 6-(nativeCoordinates b).1 7/2)*x 0-
        (nativeCoordinates b).1 1*x 2 := by
  obtain ⟨a,rfl⟩ := p286CoordinateEquiv.surjective b
  change sixRead (p286CoordinateEquiv a) (colorCombination x)=_ ∧
    zeroRead (p286CoordinateEquiv a) (colorCombination x)=_
  have sixth : sixRead (p286CoordinateEquiv a) (colorCombination x)=
      ∑ i : Fin 3,x i*sixRead (p286CoordinateEquiv a) (colorGenerator i) := by
    change sixRead (p286CoordinateEquiv a) (∑ i : Fin 3,x i • colorGenerator i)=_
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
  have zeroth : zeroRead (p286CoordinateEquiv a) (colorCombination x)=
      ∑ i : Fin 3,x i*zeroRead (p286CoordinateEquiv a) (colorGenerator i) := by
    change zeroRead (p286CoordinateEquiv a) (∑ i : Fin 3,x i • colorGenerator i)=_
    rw [map_sum]
    simp only [map_smul,smul_eq_mul]
  have six_values (i : Fin 3) : sixRead (p286CoordinateEquiv a) (colorGenerator i)=
      ![-(a.1.val 0 1).re,(a.1.val 0 1).im,0] i := (original_generator_rows a i).1
  have zero_values (i : Fin 3) : zeroRead (p286CoordinateEquiv a) (colorGenerator i)=
      ![(a.1.val 0 0).im+(a.1.val 2 2).im/2,0,-(a.1.val 0 1).im] i :=
    (original_generator_rows a i).2
  rw [sixth,zeroth,nativeCoordinates_apply]
  simp_rw [six_values,zero_values]
  constructor <;> simp [Fin.sum_univ_three] <;> ring

def variableMinor (A : coordinateSlice) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => orbitRows (gaugeAction (colorStabilizer (Pi.single j 1)) A.val) i

theorem variable_rows (A : coordinateSlice) (x : Fin 3 → ℝ) :
    orbitRows (gaugeAction (colorStabilizer x) A.val) =
      ![-secondGauge A.val*x 0+(nativeCoordinates (gaugeCoordinates A.val 1)).1 1*x 1,
        firstGauge A.val*x 1,
        -(nativeCoordinates (gaugeCoordinates A.val 0)).1 7/2*x 0-firstGauge A.val*x 2] := by
  have zeros := coordinateSlice_mem_iff A.val |>.mp A.property
  ext i
  fin_cases i
  · exact (original_combination_rows x (gaugeCoordinates A.val 1)).1
  · change (nativeCoordinates (jointP286CoordinateLieBracket (colorCombination x)
      (gaugeCoordinates A.val 0))).1 6=firstGauge A.val*x 1
    rw [(original_combination_rows x (gaugeCoordinates A.val 0)).1,zeros.1]
    simp [firstGauge]
  · change (nativeCoordinates (jointP286CoordinateLieBracket (colorCombination x)
      (gaugeCoordinates A.val 0))).1 0=
        -(nativeCoordinates (gaugeCoordinates A.val 0)).1 7/2*x 0-firstGauge A.val*x 2
    rw [(original_combination_rows x (gaugeCoordinates A.val 0)).2,zeros.2.1]
    simp [firstGauge]
    ring

theorem variableMinor_eq (A : coordinateSlice) : variableMinor A =
    !![-secondGauge A.val,(nativeCoordinates (gaugeCoordinates A.val 1)).1 1,0;
       0,firstGauge A.val,0;
       -(nativeCoordinates (gaugeCoordinates A.val 0)).1 7/2,0,-firstGauge A.val] := by
  ext i j
  unfold variableMinor
  rw [variable_rows]
  fin_cases i <;> fin_cases j <;> simp

theorem variableMinor_det (A : coordinateSlice) :
    (variableMinor A).det=(firstGauge A.val)^2*secondGauge A.val := by
  rw [variableMinor_eq,Matrix.det_fin_three]
  simp
  ring

def rowAction (A : Gauge) : stabilizer →ₗ[ℝ] (Fin 3 → ℝ) :=
  orbitRows.comp (gaugeAction.flip A)

theorem rowAction_injective (A : coordinateSlice) (first : firstGauge A.val≠0)
    (second : secondGauge A.val≠0) : Function.Injective (rowAction A.val) := by
  intro a b equal
  obtain ⟨x,rfl⟩:=colorStabilizerEquiv.surjective a
  obtain ⟨y,rfl⟩:=colorStabilizerEquiv.surjective b
  change orbitRows (gaugeAction (colorStabilizer x) A.val)=
    orbitRows (gaugeAction (colorStabilizer y) A.val) at equal
  rw [variable_rows,variable_rows] at equal
  have h0:=congrFun equal 0
  have h1:=congrFun equal 1
  have h2:=congrFun equal 2
  change firstGauge A.val*x 1=firstGauge A.val*y 1 at h1
  change -secondGauge A.val*x 0+(nativeCoordinates (gaugeCoordinates A.val 1)).1 1*x 1=
    -secondGauge A.val*y 0+(nativeCoordinates (gaugeCoordinates A.val 1)).1 1*y 1 at h0
  change -(nativeCoordinates (gaugeCoordinates A.val 0)).1 7/2*x 0-firstGauge A.val*x 2=
    -(nativeCoordinates (gaugeCoordinates A.val 0)).1 7/2*y 0-firstGauge A.val*y 2 at h2
  have eq1 : x 1=y 1 := mul_left_cancel₀ first h1
  have eq0 : x 0=y 0 := by
    rw [eq1] at h0
    exact mul_left_cancel₀ (neg_ne_zero.mpr second) (add_right_cancel h0)
  have eq2 : x 2=y 2 := by
    simp only [eq0,sub_right_inj] at h2
    exact mul_left_cancel₀ first h2
  have hxy : x=y := by ext i; fin_cases i <;> assumption
  exact congrArg colorStabilizerEquiv hxy

theorem combined_injective (A : coordinateSlice) (first : firstGauge A.val≠0)
    (second : secondGauge A.val≠0) : Function.Injective (combined A.val) := by
  rintro ⟨a,x⟩ ⟨b,y⟩ equal
  have rows := congrArg orbitRows equal
  change orbitRows (gaugeAction a A.val+(x : Gauge))=
    orbitRows (gaugeAction b A.val+(y : Gauge)) at rows
  rw [map_add,map_add,x.property,y.property,add_zero,add_zero] at rows
  have hab:=rowAction_injective A first second rows
  apply Prod.ext hab
  apply Subtype.ext
  change gaugeAction a A.val+(x : Gauge)=gaugeAction b A.val+(y : Gauge) at equal
  rw [hab] at equal
  exact add_left_cancel equal

theorem jacobian_positive (A : coordinateSlice) (first : 0<firstGauge A.val)
    (second : 0<secondGauge A.val) : 0<jacobian A.val := by
  have injective : Function.Injective (relative A.val) :=
    sourceSplitEquiv.symm.injective.comp (combined_injective A first.ne' second.ne')
  have determinant : (relativeMatrix A.val).det≠0 := by
    rw [relativeMatrix,LinearMap.det_toMatrix]
    exact (LinearEquiv.ofInjectiveEndo (relative A.val) injective).isUnit_det'.ne_zero
  exact mul_pos source_jacobian_pos (abs_pos.mpr determinant)

end LowEnergy.PreparationChartGuard
