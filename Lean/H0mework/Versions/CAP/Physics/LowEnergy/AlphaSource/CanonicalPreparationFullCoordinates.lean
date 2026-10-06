import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarCoordinates
import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationGaugeRead

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationScalarCoordinates
open SaturationMonoid.PhysicsCore
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice SourceQuantumGaugeSliceCoordinates
open PreparationCoordinates
open scoped RealInnerProductSpace

theorem scalar_build_lex (x : Fin 70 → ℝ) (i : Fin 35) :
    scalarBuild x (lexIndex i)=(x (realSlot i) : ℂ)+x (imagSlot i)*Complex.I := by
  simp [scalarBuild,show lexEquiv.symm (lexIndex i)=i from lexEquiv.symm_apply_apply i]

theorem scalar_inner_lex (phi psi : Scalar) :
    inner ℝ phi psi = ∑ i : Fin 35, ((phi (lexIndex i)).re*(psi (lexIndex i)).re+
      (phi (lexIndex i)).im*(psi (lexIndex i)).im) := by
  rw [← original_scalar_pairing]
  unfold StageNineGlobalIntegratedAction.scalarCoordinatePairingRe
  rw [← lex_bijective.sum_comp]
  simp [Complex.mul_re]

-- Literal R70x61 from the original projector column selection.
def embed61 (x : Fin 61 → ℝ) : Fin 70 → ℝ :=
  ![(1/2)*x 0,x 1,x 2,x 3,x 4,(-1/2)*x 0,x 5,x 6,x 7,x 8,x 9,x 10,x 11,(1/2)*x 12,x 13,(-1/2)*x 12,x 14,x 15,x 16,x 17,x 18,x 19,x 20,(1/2)*x 21,x 22,(-1/2)*x 21,x 23,x 24,x 25,x 26,x 27,x 28,x 29,x 30,x 31,(1/2)*x 32,(1/4)*x 33,x 34,(-1/4)*x 33,x 35,(-1/2)*x 32,x 36,(-1/4)*x 33,x 37,(1/4)*x 33,x 38,x 39,x 40,(1/2)*x 41,x 42,(-1/2)*x 41,x 43,x 44,x 45,x 46,x 47,x 48,x 49,(1/2)*x 50,x 51,(-1/2)*x 50,x 52,x 53,x 54,x 55,x 56,x 57,x 58,x 59,x 60]

-- Literal dual_R^T=Gram(R)^-1 R^T, including the paired and four-slot columns.
def read61 (z : Fin 70 → ℝ) : Fin 61 → ℝ :=
  ![z 0-z 5,z 1,z 2,z 3,z 4,z 6,z 7,z 8,z 9,z 10,z 11,z 12,z 13-z 15,z 14,z 16,z 17,z 18,z 19,z 20,z 21,z 22,z 23-z 25,z 24,z 26,z 27,z 28,z 29,z 30,z 31,z 32,z 33,z 34,z 35-z 40,z 36-z 38-z 42+z 44,z 37,z 39,z 41,z 43,z 45,z 46,z 47,z 48-z 50,z 49,z 51,z 52,z 53,z 54,z 55,z 56,z 57,z 58-z 60,z 59,z 61,z 62,z 63,z 64,z 65,z 66,z 67,z 68,z 69]

def build61 (x : Fin 61 → ℝ) : Scalar := scalarBuild (embed61 x)

def scalarEmbedding : (Fin 61 → ℝ) →ₗ[ℝ] Scalar where
  toFun := build61
  map_add' x y := by
    apply scalarRealify.injective
    change scalarRealify (scalarRealify.symm (embed61 (x+y))) =
      scalarRealify (scalarRealify.symm (embed61 x)+scalarRealify.symm (embed61 y))
    simp only [LinearEquiv.apply_symm_apply,map_add]
    ext i; fin_cases i <;> simp [embed61,mul_add]
  map_smul' r x := by
    apply scalarRealify.injective
    change scalarRealify (scalarRealify.symm (embed61 (r • x))) =
      scalarRealify (r • scalarRealify.symm (embed61 x))
    simp only [LinearEquiv.apply_symm_apply,map_smul]
    ext i; fin_cases i <;> simp [embed61] <;> ring

theorem read_embed (x : Fin 61 → ℝ) : read61 (embed61 x)=x := by
  ext i; fin_cases i <;> simp [read61,embed61] <;> ring

theorem embedding_mem_slice (x : Fin 61 → ℝ) : scalarEmbedding x ∈ scalarSlice := by
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨a,rfl⟩
  rcases hcoord : nativeCoordinates a with ⟨c,w,h⟩
  have ha : a=nativeCoordinates.symm (c,w,h) := by
    apply nativeCoordinates.injective
    simp only [LinearEquiv.apply_symm_apply,hcoord]
  rw [ha,scalar_inner_lex]
  simp_rw [sourceOrbit_all]
  change (∑ i : Fin 35, ((sourceOrbit35 c w h i).re*(build61 x (lexIndex i)).re+
    (sourceOrbit35 c w h i).im*(build61 x (lexIndex i)).im)) = 0
  simp_rw [build61,scalar_build_lex]
  simp [Fin.sum_univ_succ,sourceOrbit35,embed61,realSlot,imagSlot]
  ring

def sliceEmbedding : (Fin 61 → ℝ) →ₗ[ℝ] scalarSlice :=
  scalarEmbedding.codRestrict scalarSlice embedding_mem_slice

theorem embedding_injective : Function.Injective sliceEmbedding := by
  intro x y h
  have hr := congrArg (fun z : scalarSlice => read61 (scalarRealify z.val)) h
  change read61 (scalarRealify (scalarRealify.symm (embed61 x))) =
    read61 (scalarRealify (scalarRealify.symm (embed61 y))) at hr
  simpa only [LinearEquiv.apply_symm_apply,read_embed] using hr

theorem embedding_surjective : Function.Surjective sliceEmbedding := by
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using SourceQuantumScalarOrbitDimensions.scalarSlice_finrank.symm)).mp
  exact embedding_injective

def scalarFree : scalarSlice ≃ₗ[ℝ] (Fin 61 → ℝ) :=
  (LinearEquiv.ofBijective sliceEmbedding ⟨embedding_injective,embedding_surjective⟩).symm

def scalarFreeContinuous : scalarSlice ≃L[ℝ] (Fin 61 → ℝ) :=
  scalarFree.toContinuousLinearEquiv

theorem scalar_free_read (x : scalarSlice) : scalarFree x=read61 (scalarRealify x.val) := by
  obtain ⟨y,rfl⟩ := embedding_surjective x
  change (LinearEquiv.ofBijective sliceEmbedding ⟨embedding_injective,embedding_surjective⟩).symm
    ((LinearEquiv.ofBijective sliceEmbedding ⟨embedding_injective,embedding_surjective⟩) y) = _
  rw [LinearEquiv.symm_apply_apply]
  change y = read61 (scalarRealify (scalarRealify.symm (embed61 y)))
  simp only [LinearEquiv.apply_symm_apply,read_embed]

theorem decode_original_scalar (x : Fin 61 → ℝ) :
    scalarRealify (scalarFree.symm x).val = embed61 x :=
  scalarRealify.apply_symm_apply _

theorem original_scalar_roundtrip (x : scalarSlice) :
    scalarBuild (embed61 (read61 (scalarRealify x.val)))=x.val := by
  rw [← scalar_free_read]
  exact congrArg Subtype.val (scalarFree.symm_apply_apply x)


def scalarGramWeight (i : Fin 61) : ℝ :=
  if i=0 ∨ i=12 ∨ i=21 ∨ i=32 ∨ i=41 ∨ i=50 then 1/2 else
  if i=33 then 1/4 else 1

def scalarGram : Matrix (Fin 61) (Fin 61) ℝ := Matrix.diagonal scalarGramWeight

theorem scalar_original_Gram (x y : Fin 61 → ℝ) :
    inner ℝ (scalarFree.symm x).val (scalarFree.symm y).val =
      ∑ i : Fin 61, scalarGramWeight i*x i*y i := by
  rw [scalar_inner_lex]
  change (∑ i : Fin 35, ((build61 x (lexIndex i)).re*(build61 y (lexIndex i)).re+
    (build61 x (lexIndex i)).im*(build61 y (lexIndex i)).im)) = _
  simp_rw [build61,scalar_build_lex]
  simp [Fin.sum_univ_succ,embed61,realSlot,imagSlot,scalarGramWeight]
  ring

theorem scalar_Gram_det : scalarGram.det=1/256 := by
  rw [scalarGram,Matrix.det_diagonal]
  let exceptional : Finset (Fin 61) := {0,12,21,32,33,41,50}
  have reduce : (∏ i : Fin 61, scalarGramWeight i)=∏ i ∈ exceptional, scalarGramWeight i := by
    apply (Finset.prod_subset (Finset.subset_univ exceptional) ?_).symm
    intro i _ outside
    have hn : i≠0 ∧ i≠12 ∧ i≠21 ∧ i≠32 ∧ i≠33 ∧ i≠41 ∧ i≠50 := by
      simpa [exceptional] using outside
    simp [scalarGramWeight,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2.1,hn.2.2.2.2.2.1,hn.2.2.2.2.2.2]
  rw [reduce]
  change (∏ i ∈ ({0,12,21,32,33,41,50} : Finset (Fin 61)), scalarGramWeight i)=1/256
  rw [Finset.prod_insert (by decide : (0 : Fin 61)∉({12,21,32,33,41,50} : Finset (Fin 61))),
    Finset.prod_insert (by decide : (12 : Fin 61)∉({21,32,33,41,50} : Finset (Fin 61))),
    Finset.prod_insert (by decide : (21 : Fin 61)∉({32,33,41,50} : Finset (Fin 61))),
    Finset.prod_insert (by decide : (32 : Fin 61)∉({33,41,50} : Finset (Fin 61))),
    Finset.prod_insert (by decide : (33 : Fin 61)∉({41,50} : Finset (Fin 61))),
    Finset.prod_insert (by decide : (41 : Fin 61)∉({50} : Finset (Fin 61))),Finset.prod_singleton]
  change (1/2 : ℝ)*((1/2)*((1/2)*((1/2)*((1/4)*((1/2)*(1/2))))))=1/256
  norm_num

theorem scalar_norm_sq (x : Fin 61 → ℝ) :
    ‖(scalarFree.symm x).val‖^2=∑ i : Fin 61, scalarGramWeight i*x i*x i := by
  rw [← real_inner_self_eq_norm_sq,scalar_original_Gram]

abbrev CoordinateBlocks := (Fin 6 → ℝ) × (Fin 61 → ℝ) × (Fin 33 → ℝ)

def joinCoordinates (x : CoordinateBlocks) (i : Fin 100) : ℝ :=
  if h0 : i.val<6 then x.1 ⟨i.val,h0⟩ else
  if h1 : i.val<67 then x.2.1 ⟨i.val-6,by omega⟩ else
  x.2.2 ⟨i.val-67,by omega⟩

def splitCoordinates (x : Fin 100 → ℝ) : CoordinateBlocks :=
  (fun i => x ⟨i.val,by omega⟩,
   fun i => x ⟨6+i.val,by omega⟩,
   fun i => x ⟨67+i.val,by omega⟩)

def flattenCoordinates : CoordinateBlocks ≃ₗ[ℝ] (Fin 100 → ℝ) where
  toFun := joinCoordinates
  invFun := splitCoordinates
  left_inv x := by
    apply Prod.ext
    · ext i; simp [joinCoordinates,splitCoordinates]
    · apply Prod.ext
      · ext i; simp [joinCoordinates,splitCoordinates]; omega
      · ext i; simp [joinCoordinates,splitCoordinates]; omega
  right_inv x := by
    ext i
    by_cases h0 : i.val<6
    · simp [joinCoordinates,splitCoordinates,h0]
    · by_cases h1 : i.val<67
      · simp [joinCoordinates,splitCoordinates,h0,h1]
        congr 1
        apply Fin.ext
        change 6+(i.val-6)=i.val
        omega
      · simp [joinCoordinates,splitCoordinates,h0,h1]
        congr 1
        apply Fin.ext
        change 67+(i.val-67)=i.val
        omega
  map_add' x y := by
    ext i
    by_cases h0 : i.val<6 <;> by_cases h1 : i.val<67 <;>
      simp [joinCoordinates,h0,h1]
  map_smul' r x := by
    ext i
    by_cases h0 : i.val<6 <;> by_cases h1 : i.val<67 <;>
      simp [joinCoordinates,h0,h1]

def blockCoordinates : SourceCoordinateSlice ≃L[ℝ] CoordinateBlocks :=
  coframeCoordinates.prodCongr (scalarFreeContinuous.prodCongr gaugeFreeContinuous)

def fullCoordinates : SourceCoordinateSlice ≃L[ℝ] (Fin 100 → ℝ) :=
  blockCoordinates.trans flattenCoordinates.toContinuousLinearEquiv

theorem full_blocks (z : SourceCoordinateSlice) :
    fullCoordinates z=joinCoordinates (coframeCoordinates z.1,
      read61 (scalarRealify z.2.1.val),gaugeFree z.2.2) := by
  change joinCoordinates (coframeCoordinates z.1,scalarFree z.2.1,gaugeFree z.2.2)=_
  rw [scalar_free_read]

theorem actual_sourcePoint_100 :
    fullCoordinates GaussHistoryHilbert.sourcePoint.val =
      joinCoordinates (![1,0,1,0,0,1],0,sourceGauge33) := by
  rw [full_blocks]
  change joinCoordinates (![1,0,1,0,0,1],read61 (scalarRealify 0),gaugeFree sourceSlice)=_
  rw [map_zero,source_gauge_read]
  congr 1
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ext i; fin_cases i <;> simp [read61]
    · rfl

theorem original_source_decode :
    fullCoordinates.symm (joinCoordinates (![1,0,1,0,0,1],0,sourceGauge33)) =
      GaussHistoryHilbert.sourcePoint.val := by
  rw [← actual_sourcePoint_100]
  exact fullCoordinates.symm_apply_apply _

def displaced100 : Fin 100 → ℝ := fun i =>
  joinCoordinates (![1,0,1,0,0,1],0,sourceGauge33) i+
    if i=6 then 1/1000 else if i=67 then 1/1000 else if i=95 then 1/37 else 0

theorem displaced100_roundtrip :
    fullCoordinates (fullCoordinates.symm displaced100)=displaced100 :=
  fullCoordinates.apply_symm_apply _

theorem displaced_scalar_actual :
    scalarRealify (fullCoordinates.symm displaced100).2.1.val 0=1/2000 ∧
    scalarRealify (fullCoordinates.symm displaced100).2.1.val 5=-(1/2000) := by
  have hr := decode_original_scalar (splitCoordinates displaced100).2.1
  change scalarRealify (scalarFree.symm ((splitCoordinates displaced100).2.1)).val 0=_ ∧
    scalarRealify (scalarFree.symm ((splitCoordinates displaced100).2.1)).val 5=_
  rw [congrFun hr 0,congrFun hr 5]
  have raw0 : embed61 (splitCoordinates displaced100).2.1 0=
      (1/2 : ℝ)*(splitCoordinates displaced100).2.1 0 := rfl
  have raw5 : embed61 (splitCoordinates displaced100).2.1 5=
      (-1/2 : ℝ)*(splitCoordinates displaced100).2.1 0 := rfl
  have d6 : displaced100 (6 : Fin 100)=1/1000 := by
    unfold displaced100
    rw [if_pos rfl]
    change (0 : ℝ)+1/1000=1/1000
    ring
  rw [raw0,raw5]
  change (1/2 : ℝ)*displaced100 6=1/2000 ∧ (-1/2 : ℝ)*displaced100 6=-(1/2000)
  rw [d6]
  norm_num

end LowEnergy.PreparationScalarCoordinates
