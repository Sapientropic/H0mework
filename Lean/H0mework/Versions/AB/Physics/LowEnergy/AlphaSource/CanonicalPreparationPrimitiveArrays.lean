import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveAction
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationPrimitiveJets
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGaugeInverse
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationRawGram

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPrimitiveMatrix
open SaturationMonoid.PhysicsCore
open PreparationScalarCoordinates PreparationCoordinates PreparationChartGuard PreparationMeasure
open PreparationVacuumSourceChartBudget PreparationVacuumSourceMatrixInverse
open SourceQuantumScalarChart SourceQuantumNativeDimensions SourceQuantumResidualGaugeSlice
open StageNineDynamicBreakingVacuum StageNineEnrichedProofFreeSource SU7ExteriorYukawaMassSpectrum
open scoped BigOperators RealInnerProductSpace Matrix

def rawBrokenColumn : Fin 9 → Fin 12 → ℝ :=
  ![Pi.single 2 1,Pi.single 3 1,Pi.single 4 1,Pi.single 5 1,
    Pi.single 6 (1/2)+Pi.single 7 (1/2),Pi.single 8 1,Pi.single 9 1,Pi.single 10 1,Pi.single 11 1]

theorem raw_color (x : Fin 3 → ℝ) : rawCoordinates (colorCombination x)=
    ![x 1/2,x 0/2,0,0,0,0,x 2/2,-(x 2/2),0,0,0,0] := by
  change rawRead (colorCombination x)=_
  unfold rawRead
  rw [colorCombination_coordinates]
  ext i
  fin_cases i <;> simp

theorem rawBroken_mem (j : Fin 9) : rawCoordinates.symm (rawBrokenColumn j)∈broken := by
  apply (Submodule.mem_orthogonal _ _).mpr
  intro a ha
  obtain ⟨v,equal⟩ := colorStabilizerEquiv.surjective ⟨a,ha⟩
  have av : a=colorCombination v := (congrArg Subtype.val equal).symm
  rw [av,←rawCoordinates.symm_apply_apply (colorCombination v),raw_color,original_raw_inner]
  fin_cases j <;> simp [rawBrokenColumn,Pi.single_apply] <;> ring

theorem rawBroken_read (j : Fin 9) :
    normalRead (rawCoordinates.symm (rawBrokenColumn j))=sourceNormal j := by
  change normalRead (rawBuild (rawBrokenColumn j))=sourceNormal j
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [normalRead,rawBuild,rawBrokenColumn,sourceNormal,Pi.single_apply,PiLp.toLp_apply,Fin.isValue] <;> norm_num

theorem sourceBroken_raw (j : Fin 9) : rawCoordinates (sourceBroken j).val=rawBrokenColumn j := by
  let actual : broken := ⟨rawCoordinates.symm (rawBrokenColumn j),rawBroken_mem j⟩
  have read : brokenRead (sourceBroken j)=sourceNormal j := by
    rw [←sourceBroken_build,brokenRead_build]
  have same : actual=sourceBroken j := by
    apply brokenCoordinates.injective
    change brokenRead actual=brokenRead (sourceBroken j)
    rw [read]
    exact rawBroken_read j
  have value := congrArg (fun b : broken => rawCoordinates b.val) same
  change rawCoordinates (rawCoordinates.symm (rawBrokenColumn j))=_ at value
  simpa only [LinearEquiv.apply_symm_apply] using value.symm

def sourceO : Matrix (Fin 70) (Fin 9) ℝ := fun i j =>
  scalarRealify (orbit (normalBuild (sourceNormal j))) i

def literalO (i : Fin 70) (j : Fin 9) : ℝ :=
  if (i=0 ∨ i=5) ∧ j=5 then 1 else
  if (i=13 ∨ i=15) ∧ j=2 then -1 else
  if (i=23 ∨ i=25) ∧ j=0 then 1 else
  if (i=35 ∨ i=40) ∧ j=6 then 1 else
  if i=36 ∧ j=7 then -1 else
  if i=38 ∧ j=8 then -1 else
  if (i=42 ∨ i=44) ∧ j=4 then 1 else
  if i=42 ∧ j=7 then -1 else
  if i=42 ∧ j=8 then 1 else
  if (i=48 ∨ i=50) ∧ j=3 then 1 else
  if (i=58 ∨ i=60) ∧ j=1 then -1 else 0

def rationalO (i : Fin 70) (j : Fin 9) : ℚ :=
  if (i=0 ∨ i=5) ∧ j=5 then 1 else
  if (i=13 ∨ i=15) ∧ j=2 then -1 else
  if (i=23 ∨ i=25) ∧ j=0 then 1 else
  if (i=35 ∨ i=40) ∧ j=6 then 1 else
  if i=36 ∧ j=7 then -1 else
  if i=38 ∧ j=8 then -1 else
  if (i=42 ∨ i=44) ∧ j=4 then 1 else
  if i=42 ∧ j=7 then -1 else
  if i=42 ∧ j=8 then 1 else
  if (i=48 ∨ i=50) ∧ j=3 then 1 else
  if (i=58 ∨ i=60) ∧ j=1 then -1 else 0

theorem rationalO_cast (i : Fin 70) (j : Fin 9) : (rationalO i j : ℝ)=literalO i j := by
  have cast_if (p : Prop) [Decidable p] (a b : ℚ) :
      ((if p then a else b : ℚ) : ℝ)=if p then (a : ℝ) else (b : ℝ) := by
    split_ifs <;> rfl
  unfold rationalO literalO
  simp only [cast_if,Rat.cast_one,Rat.cast_neg,Rat.cast_zero]

theorem sourceO_literal (i : Fin 70) (j : Fin 9) : sourceO i j=literalO i j := by
  refine Fin.addCases (m:=35) (n:=35) (fun k => ?_) (fun k => ?_) i
  · change scalarRead (orbit (normalBuild (sourceNormal j))) (realSlot k)=literalO (realSlot k) j
    rw [scalar_read_real,normalBuild,sourceOrbit_all]
    fin_cases j <;> fin_cases k <;>
      norm_num [sourceOrbit35,sourceNormal,PiLp.toLp_apply,Pi.single_apply,literalO,realSlot,Fin.ext_iff]
    all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals norm_num
  · change scalarRead (orbit (normalBuild (sourceNormal j))) (imagSlot k)=literalO (imagSlot k) j
    rw [scalar_read_imag,normalBuild,sourceOrbit_all]
    fin_cases j <;> fin_cases k <;>
      norm_num [sourceOrbit35,sourceNormal,PiLp.toLp_apply,Pi.single_apply,literalO,imagSlot,Fin.ext_iff]
    all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
    all_goals norm_num

def RowColumnBound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (bound : ℝ) : Prop :=
  (∀ i,∑ j,|A i j|≤bound) ∧ (∀ j,∑ i,|A i j|≤bound)

theorem sourceO_bound : RowColumnBound sourceO 3 := by
  have rows : ∀ i : Fin 70,∑ j : Fin 9,|rationalO i j|≤3 := by decide +kernel
  have cols : ∀ j : Fin 9,∑ i : Fin 70,|rationalO i j|≤3 := by decide +kernel
  constructor
  · intro i
    simp_rw [sourceO_literal,←rationalO_cast]
    exact_mod_cast rows i
  · intro j
    simp_rw [sourceO_literal,←rationalO_cast]
    exact_mod_cast cols j

def sourceR : Matrix (Fin 70) (Fin 61) ℝ := fun i j => embed61 (Pi.single j 1) i

def sourceRColumn : Fin 70→Fin 61 := ![0,1,2,3,4,0,5,6,7,8,9,10,11,12,13,12,14,15,16,17,18,19,20,21,22,21,23,24,25,26,27,28,29,30,31,32,33,34,33,35,32,36,33,37,33,38,39,40,41,42,41,43,44,45,46,47,48,49,50,51,50,52,53,54,55,56,57,58,59,60]
def sourceRWeight : Fin 70→ℚ := ![(1/2),(1),(1),(1),(1),(-1/2),(1),(1),(1),(1),(1),(1),(1),(1/2),(1),(-1/2),(1),(1),(1),(1),(1),(1),(1),(1/2),(1),(-1/2),(1),(1),(1),(1),(1),(1),(1),(1),(1),(1/2),(1/4),(1),(-1/4),(1),(-1/2),(1),(-1/4),(1),(1/4),(1),(1),(1),(1/2),(1),(-1/2),(1),(1),(1),(1),(1),(1),(1),(1/2),(1),(-1/2),(1),(1),(1),(1),(1),(1),(1),(1),(1)]
def rationalR (i : Fin 70) (j : Fin 61) : ℚ := if sourceRColumn i=j then sourceRWeight i else 0

theorem rationalR_cast (i : Fin 70) (j : Fin 61) : (rationalR i j : ℝ)=sourceR i j := by
  fin_cases i <;> norm_num [rationalR,sourceRColumn,sourceRWeight,sourceR,embed61,Pi.single_apply,eq_comm]
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals split_ifs <;> norm_num

theorem sourceR_bound_one : RowColumnBound sourceR 1 := by
  have rows : ∀ i : Fin 70,∑ j : Fin 61,|rationalR i j|≤1 := by decide +kernel
  have cols : ∀ j : Fin 61,∑ i : Fin 70,|rationalR i j|≤1 := by decide +kernel
  constructor
  · intro i
    simp_rw [←rationalR_cast]
    exact_mod_cast rows i
  · intro j
    simp_rw [←rationalR_cast]
    exact_mod_cast cols j

theorem sourceR_original_bound : RowColumnBound sourceR 4 :=
  ⟨fun i => (sourceR_bound_one.1 i).trans (by norm_num),
    fun j => (sourceR_bound_one.2 j).trans (by norm_num)⟩

def scalarUnit (i : Fin 70) : Scalar := scalarBuild (Pi.single i 1)

theorem scalarUnit_read (i : Fin 70) : scalarRealify (scalarUnit i)=Pi.single i 1 :=
  scalarRealify.apply_symm_apply _

theorem scalar_inner_realified (phi psi : Scalar) :
    inner ℝ phi psi=∑ i : Fin 70,scalarRealify phi i*scalarRealify psi i := by
  rw [scalar_inner_lex,Fin.sum_univ_add (a:=35) (b:=35)]
  simp only [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    simp [scalarRealify,scalarRead,Fin.isValue]


open SU7MotherLieAlgebra StageNineHolonomicField SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction StageNineExteriorMotherLieRepresentation
open SaturationMonoid.GaugeProjection.ConcreteBlockDiagonal
open Lean Elab Term in
elab "scalar_source_const%" name:str : term => do
  unless #["native_symm","native_entry","fullMatrix"].contains name.getString do
    throwError "Not a source scalar matrix declaration"
  let ns := Name.str (Name.str (Name.num `_private.H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationScalarCoordinates 0) "LowEnergy") "PreparationScalarCoordinates"
  Lean.Meta.mkConstWithFreshMVarLevels (Name.str ns name.getString)

def literalFundamental (c : Fin 8→ℝ) (w : Fin 3→ℝ) (h : ℝ) : Matrix (Fin 7) (Fin 7) ℂ :=
  !![c 6 * Complex.I, c 0 + c 1 * Complex.I, c 2 + c 3 * Complex.I, 0, 0, 0, 0;
     -c 0 + c 1 * Complex.I, (-c 6 + c 7) * Complex.I, c 4 + c 5 * Complex.I, 0, 0, 0, 0;
     -c 2 + c 3 * Complex.I, -c 4 + c 5 * Complex.I, -c 7 * Complex.I, 0, 0, 0, 0;
     0, 0, 0, w 2 * Complex.I, w 0 + w 1 * Complex.I, 0, 0;
     0, 0, 0, -w 0 + w 1 * Complex.I, -w 2 * Complex.I, 0, 0;
     0, 0, 0, 0, 0, h * Complex.I, 0;
     0, 0, 0, 0, 0, 0, -(h * Complex.I)]

def fundamentalB (b : Fin 9) : SU7MotherLieMatrix :=
  p286LieBlockEmbed (p286CoordinateEquiv.symm (sourceBroken b).val)

theorem fundamentalB_native (b : Fin 9) (i j : Fin 7) :
    (fundamentalB b).val (smBlockIndexEquivFin7.symm i) (smBlockIndexEquivFin7.symm j)=
      literalFundamental
        (nativeCoordinates (rawBuild (rawBrokenColumn b))).1
        (nativeCoordinates (rawBuild (rawBrokenColumn b))).2.1
        (nativeCoordinates (rawBuild (rawBrokenColumn b))).2.2 i j := by
  have bv : (sourceBroken b).val=rawCoordinates.symm (rawBrokenColumn b) := by
    apply rawCoordinates.injective
    simpa only [LinearEquiv.apply_symm_apply] using sourceBroken_raw b
  unfold fundamentalB
  rw [bv]
  change rawP286LieBlock (p286CoordinateEquiv.symm (rawBuild (rawBrokenColumn b))) _ _=_
  unfold rawBuild
  rw [scalar_source_const% "native_symm"]
  simp only [LinearEquiv.apply_symm_apply]
  exact (scalar_source_const% "native_entry") _ _ _ i j

theorem fundamentalB_column (b : Fin 9) (j : SU7MotherIndex) :
    (∑ i : SU7MotherIndex,complexAbs ((fundamentalB b).val i j))≤1 := by
  obtain ⟨j,rfl⟩ := smBlockIndexEquivFin7.symm.surjective j
  rw [← smBlockIndexEquivFin7.symm.sum_comp]
  simp_rw [fundamentalB_native]
  fin_cases b <;> fin_cases j <;>
    norm_num [rawBuild,rawBrokenColumn,Pi.single_apply,literalFundamental,
      complexAbs,Fin.sum_univ_succ,Fin.ext_iff]
  all_goals try dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num

theorem source_exterior_column (b : Fin 9) (input : ExteriorBasisIndex 4) :
    exteriorL1 (exteriorBasisLieAction 4 (fundamentalB b) input)≤4 :=
  exterior_action_column_bound (fundamentalB b) (fundamentalB_column b) input


def scalarL1 (v : Scalar) : ℝ := ∑ i : Fin 70,|scalarRealify v i|

theorem scalarL1_exterior (v : Scalar) : scalarL1 v=exteriorL1 (scalarCoordinateEquiv.symm v) := by
  unfold scalarL1 exteriorL1
  rw [Fin.sum_univ_add (a:=35) (b:=35),← lex_bijective.sum_comp]
  simp only [complexAbs,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    simp [scalarRealify,scalarRead,complexAbs,scalarCoordinateEquiv]


theorem source_exterior_operator (b : Fin 9) (v : ⋀[ℂ]^4 SU7FundamentalCarrier) :
    exteriorL1 (exteriorMotherLieAction 4 (fundamentalB b) v)≤4*exteriorL1 v := by
  unfold exteriorMotherLieAction
  change exteriorL1 (∑ i : ExteriorBasisIndex 4,(su7ExteriorBasis 4).repr v i •
    exteriorBasisLieAction 4 (fundamentalB b) i)≤_
  refine (exteriorL1_sum _ _).trans ?_
  unfold exteriorL1
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact (exteriorL1_smul _ _).trans (by
    have h:=mul_le_mul_of_nonneg_left (source_exterior_column b i)
      (complexAbs_nonnegative ((su7ExteriorBasis 4).repr v i))
    simpa [mul_comm] using h)

theorem source_action_L1 (b : Fin 9) (v : Scalar) :
    scalarL1 (action v (sourceBroken b).val)≤4*scalarL1 v := by
  rw [scalarL1_exterior,scalarL1_exterior]
  change exteriorL1 (scalarCoordinateEquiv.symm (scalarCoordinateEquiv
    (exteriorMotherLieAction 4 (fundamentalB b) (scalarCoordinateEquiv.symm v))))≤_
  rw [LinearEquiv.symm_apply_apply]
  exact source_exterior_operator b _

def sourceRho (b : Fin 9) : Matrix (Fin 70) (Fin 70) ℝ := fun i j =>
  scalarRealify (action (scalarUnit j) (sourceBroken b).val) i

theorem scalarUnit_L1 (j : Fin 70) : scalarL1 (scalarUnit j)=1 := by
  unfold scalarL1
  rw [scalarUnit_read]
  simp [Pi.single_apply,apply_ite]

theorem sourceRho_column (b : Fin 9) (j : Fin 70) : (∑ i,|sourceRho b i j|)≤4 := by
  change scalarL1 (action (scalarUnit j) (sourceBroken b).val)≤4
  simpa only [scalarUnit_L1,mul_one] using source_action_L1 b (scalarUnit j)

theorem scalarUnit_inner (i : Fin 70) (v : Scalar) : inner ℝ (scalarUnit i) v=scalarRealify v i := by
  rw [scalar_inner_realified,scalarUnit_read]
  simp [Pi.single_apply]

theorem sourceRho_skew (b : Fin 9) (i j : Fin 70) : sourceRho b i j= -sourceRho b j i := by
  have h := StageNineP286LinkedActiveScalarPairingSkew.scalarCoordinatePairingRe_scalarMotherLieAction_skew
    (fundamentalB b) (scalarUnit j) (scalarUnit i)
  rw [original_scalar_pairing,original_scalar_pairing] at h
  change inner ℝ (action (scalarUnit j) (sourceBroken b).val) (scalarUnit i)+
    inner ℝ (scalarUnit j) (action (scalarUnit i) (sourceBroken b).val)=0 at h
  rw [real_inner_comm,scalarUnit_inner,scalarUnit_inner] at h
  exact eq_neg_of_add_eq_zero_left h

theorem sourceRho_bound (b : Fin 9) : RowColumnBound (sourceRho b) 4 := by
  refine ⟨?_,sourceRho_column b⟩
  intro i
  simp_rw [sourceRho_skew b i,abs_neg]
  exact sourceRho_column b i

open PreparationVacuumCoframeBudget CanonicalPreparationCutoff

theorem scalarL1_smul (r : ℝ) (v : Scalar) : scalarL1 (r•v)=|r| * scalarL1 v := by
  simp [scalarL1,map_smul,abs_mul,Finset.mul_sum]

theorem scalarL1_sum {ι : Type*} (s : Finset ι) (f : ι→Scalar) :
    scalarL1 (∑ i∈s,f i)≤∑ i∈s,scalarL1 (f i) := by
  classical
  unfold scalarL1
  simp only [map_sum,Finset.sum_apply]
  calc
    _ ≤ ∑ j : Fin 70,∑ i∈s,|scalarRealify (f i) j| := Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := Finset.sum_comm

theorem scalarFree_L1 (v : Fin 61→ℝ) : scalarL1 (scalarFree.symm v).val≤∑ i,|v i| := by
  have expand : v=∑ i : Fin 61,v i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  have one (i : Fin 61) : scalarL1 (scalarFree.symm (Pi.single i 1)).val≤1 := by
    unfold scalarL1
    rw [decode_original_scalar]
    exact sourceR_bound_one.2 i
  conv_lhs => rw [expand]
  simp only [map_sum,map_smul,Submodule.coe_sum,Submodule.coe_smul_of_tower]
  refine (scalarL1_sum _ _).trans ?_
  apply Finset.sum_le_sum
  intro i hi
  rw [scalarL1_smul]
  exact (mul_le_mul_of_nonneg_left (one i) (abs_nonneg _)).trans_eq (mul_one _)

def scalarInput : Phase →L[ℝ] (Fin 61→ℝ) :=
  ContinuousLinearMap.pi (fun i => phaseCoordinate ⟨6+i.val,by omega⟩)

def sourceScalar : Phase →L[ℝ] Scalar :=
  scalarSlice.subtypeL.comp (scalarFreeContinuous.symm.toContinuousLinearMap.comp scalarInput)

theorem sourceScalar_native (x : Phase) : sourceScalar x=(fullCoordinates.symm x.1).2.1.val := rfl

theorem sourceScalar_L1 (x : Phase) : scalarL1 (sourceScalar x)≤∑ i,|scalarInput x i| :=
  scalarFree_L1 _

theorem sourceScalar_direction_L1 (s : Slot) : scalarL1 (sourceScalar (slotDirection s))≤1 := by
  refine (sourceScalar_L1 _).trans ?_
  change (∑ i : Fin 61,|phaseCoordinate ⟨6+i.val,by omega⟩ (slotDirection s)|)≤1
  simp only [phaseCoordinate_direction]
  by_cases hex : ∃ i : Fin 61,s=(⟨6+i.val,by omega⟩,false)
  · obtain ⟨i,rfl⟩ := hex
    have equal (j : Fin 61) : ((⟨6+i.val,by omega⟩ : Fin 100),false)=(⟨6+j.val,by omega⟩,false) ↔ i=j := by
      simp [Fin.ext_iff]
    simp [equal,apply_ite]
  · push Not at hex
    simp [hex]

theorem sourceScalar_box_L1 (x : Phase) (box : x.1∈sourceClosedBox) : scalarL1 (sourceScalar x)≤915 := by
  refine (sourceScalar_L1 x).trans ?_
  calc
    _ ≤ ∑ _i : Fin 61,(15 : ℝ) := Finset.sum_le_sum (fun i _ => source_coordinate_j15 x box ⟨6+i.val,by omega⟩)
    _ = 915 := by norm_num

theorem sourceD9_L1_entry (v : Scalar) (i j : Fin 9) : |sourceD9 v i j|≤12*scalarL1 v := by
  have entry (k : Fin 70) : |sourceO k i|≤3 :=
    (Finset.single_le_sum (fun a _ => abs_nonneg (sourceO a i)) (Finset.mem_univ k)).trans (sourceO_bound.2 i)
  unfold sourceD9
  rw [scalar_inner_realified]
  calc
    _ ≤ ∑ k : Fin 70,|scalarRealify (orbit (normalBuild (sourceNormal i))) k*
        scalarRealify (action v (sourceBroken j).val) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin 70,3*|scalarRealify (action v (sourceBroken j).val) k| := by
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (entry k) (abs_nonneg _)
    _ = 3*scalarL1 (action v (sourceBroken j).val) := by simp only [scalarL1,Finset.mul_sum]
    _ ≤ 3*(4*scalarL1 v) := mul_le_mul_of_nonneg_left (source_action_L1 j v) (by norm_num)
    _ = 12*scalarL1 v := by ring

def linearD (i j : Fin 9) : Phase →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := fun x => sourceD9 (sourceScalar x) i j
    map_add' := by intro x y; simp only [map_add,sourceD9_add]; rfl
    map_smul' := by intro r x; simp only [map_smul,sourceD9_smul]; rfl }

def originalD (i j : Fin 9) : Symbol := fun x =>
  sourceD9 (vacuum+(fullCoordinates.symm x.1).2.1.val) i j

theorem originalD_readback (x : Phase) (i j : Fin 9) : originalD i j x=sourceGram i j+linearD i j x := by
  unfold originalD
  rw [sourceD9_add]
  change sourceD9 vacuum i j+sourceD9 (fullCoordinates.symm x.1).2.1.val i j=_
  rw [sourceGram_actual]
  rfl

theorem originalD_jet_one (w : Word 1) (x : Phase) (i j : Fin 9) :
    jet 1 (originalD i j) w x=linearD i j (slotDirection (w 0)) := by
  rw [show originalD i j=(fun y => sourceGram i j+linearD i j y) by funext y; exact originalD_readback y i j]
  simp [jet,fderiv_const_add,ContinuousLinearMap.fderiv]

theorem originalD_jet_higher (n : ℕ) (w : Word (n+2)) (x : Phase) (i j : Fin 9) :
    jet (n+2) (originalD i j) w x=0 := by
  rw [show originalD i j=(fun y => sourceGram i j+linearD i j y) by funext y; exact originalD_readback y i j]
  unfold jet
  rw [iteratedFDeriv_succ_apply_right]
  simp only [fderiv_const_add,ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

def originalDArray : ℕ→ℕ | 0=>98928 | 1=>108 | _=>0

theorem originalD_entry_budget (n : ℕ) (w : Word n) (x : Phase) (box : x.1∈sourceClosedBox)
    (i j : Fin 9) : |jet n (originalD i j) w x|≤(originalDArray n : ℝ)/9 := by
  cases n with
  | zero =>
    simp only [jet,iteratedFDeriv_zero_apply,originalD_readback]
    have h:=sourceD9_L1_entry (sourceScalar x) i j
    change |linearD i j x|≤12*scalarL1 (sourceScalar x) at h
    have h2:=sourceScalar_box_L1 x box
    have h3:=sourceGram_entry_bound i j
    have h4:=abs_add_le (sourceGram i j) (linearD i j x)
    norm_num [originalDArray]
    linarith
  | succ n =>
    cases n with
    | zero =>
      rw [originalD_jet_one]
      have h:=sourceD9_L1_entry (sourceScalar (slotDirection (w 0))) i j
      change |linearD i j (slotDirection (w 0))|≤12*scalarL1 (sourceScalar (slotDirection (w 0))) at h
      have h2:=sourceScalar_direction_L1 (w 0)
      norm_num [originalDArray]
      linarith
    | succ n => simp [originalD_jet_higher,originalDArray]

theorem actual_D9_row_budget (n : ℕ) (w : Word n) (x : Phase) (box : x.1∈sourceClosedBox) (i : Fin 9) :
    (∑ j,|jet n (originalD i j) w x|)≤(originalDArray n : ℝ) := by
  calc
    _ ≤ ∑ _j : Fin 9,(originalDArray n : ℝ)/9 := Finset.sum_le_sum (fun j _ => originalD_entry_budget n w x box i j)
    _ = _ := by simp; ring

theorem actual_D9_column_budget (n : ℕ) (w : Word n) (x : Phase) (box : x.1∈sourceClosedBox) (j : Fin 9) :
    (∑ i,|jet n (originalD i j) w x|)≤(originalDArray n : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin 9,(originalDArray n : ℝ)/9 := Finset.sum_le_sum (fun i _ => originalD_entry_budget n w x box i j)
    _ = _ := by simp; ring

end LowEnergy.PreparationVacuumPrimitiveMatrix
