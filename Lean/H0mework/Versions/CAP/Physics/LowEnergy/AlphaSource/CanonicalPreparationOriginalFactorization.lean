import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationOriginalJacobi

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.PreparationVacuumOriginalGreenFeedback
open scoped BigOperators

def coefficientMap : SourceCoefficient →+* ℂ where
  toFun:=coefficientValue
  map_one':=by
    simp [coefficientValue,QuadraticAlgebra.re_one,QuadraticAlgebra.im_one]
  map_mul':=coefficient_mul
  map_zero':=coefficient_zero
  map_add':=coefficient_add

def negativeTerms (ts : List SourceTerm) : List SourceTerm :=
  ts.map (fun a=>{a with coefficient:= -a.coefficient})

def rowTerms (i : Fin 289) (ts : List SourceTerm) : List SourceTerm :=
  ts.filter (fun a=>a.row=i)

theorem negativeTerms_value (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (negativeTerms ts) p= -sourceMatrix ts p := by
  induction ts with
  | nil=>simp [negativeTerms,sourceMatrix]
  | cons a rest ih=>
    have hc : coefficientValue (-a.coefficient)= -coefficientValue a.coefficient := coefficientMap.map_neg _
    simp only [negativeTerms,List.map_cons,sourceMatrix_cons] at ih ⊢
    rw [ih]
    simp [SourceTerm.matrix,hc,neg_mul,Matrix.single_neg]
    abel

theorem rowTerms_entry (ts : List SourceTerm) (p : Fin 4→ℂ) (i j : Fin 289) :
    sourceMatrix (rowTerms i ts) p i j=sourceMatrix ts p i j := by
  induction ts with
  | nil=>rfl
  | cons a rest ih=>
    simp only [rowTerms] at ih
    by_cases same : a.row=i
    · simp [rowTerms,same,sourceMatrix_cons,ih]
    · have zero : a.matrix p i j=0 := by simp [SourceTerm.matrix,Matrix.single,same]
      simp [rowTerms,same,sourceMatrix_cons,zero,ih]

theorem row_product_entry (left right : List SourceTerm) (p : Fin 4→ℂ) (i j : Fin 289) :
    sourceMatrix (productTerms (rowTerms i left) right) p i j=
      (sourceMatrix left p*sourceMatrix right p) i j := by
  rw [productTerms_value]
  simp only [Matrix.mul_apply,rowTerms_entry]

def termOrder (a : SourceTerm) : ℕ :=
  (((((a.row.val*289+a.column.val)*8+a.powers.temporal)*8+a.powers.first)*8+a.powers.second)*8+a.powers.third)

def bitFlag (depth : ℕ) (a : SourceTerm) : Bool := decide ((termOrder a/2^depth)%2=0)

-- Every leaf uses exact normalization, so the fuel is an algorithmic grouping
-- choice and cannot omit a term or change a source coefficient.
def bucketNormalize (fuel depth : ℕ) (ts : List SourceTerm) : List SourceTerm :=
  Nat.rec (fun (_ : ℕ) (terms : List SourceTerm)=>normalizeTerms terms)
    (fun _ previous (level : ℕ) (terms : List SourceTerm)=>
      if terms.length≤16 then normalizeTerms terms else
        previous (level+1) (terms.filter (bitFlag level))++
        previous (level+1) (terms.filter (fun a=> !(bitFlag level a)))) fuel depth ts

def fastNormalizeTerms (ts : List SourceTerm) : List SourceTerm := bucketNormalize 32 0 ts

private theorem partition_value (flag : SourceTerm→Bool) (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (ts.filter flag) p+sourceMatrix (ts.filter (fun a=> !(flag a))) p=sourceMatrix ts p := by
  induction ts with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    cases h : flag a
    · simp [h,sourceMatrix_cons]
      rw [←ih]
      abel
    · simp [h,sourceMatrix_cons]
      rw [←ih]
      abel

theorem bucketNormalize_value (fuel depth : ℕ) (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (bucketNormalize fuel depth ts) p=sourceMatrix ts p := by
  induction fuel generalizing depth ts with
  | zero=>exact normalizeTerms_value ts p
  | succ fuel ih=>
    change sourceMatrix (if ts.length≤16 then normalizeTerms ts else
      bucketNormalize fuel (depth+1) (ts.filter (bitFlag depth))++
      bucketNormalize fuel (depth+1) (ts.filter (fun a=> !(bitFlag depth a)))) p=_
    split_ifs
    · exact normalizeTerms_value ts p
    · rw [sourceMatrix_append,ih,ih,partition_value]

theorem fastNormalizeTerms_value (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (fastNormalizeTerms ts) p=sourceMatrix ts p := bucketNormalize_value 32 0 ts p

theorem normalization_equal (left right : List SourceTerm)
    (equal : fastNormalizeTerms (left++negativeTerms right)=[]) (p : Fin 4→ℂ) :
    sourceMatrix left p=sourceMatrix right p := by
  have h:=fastNormalizeTerms_value (left++negativeTerms right) p
  rw [equal,sourceMatrix_nil,sourceMatrix_append,negativeTerms_value] at h
  exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using h.symm)

def identityTerms : List SourceTerm :=
  (List.finRange 289).map (fun i=>⟨i,i,⟨0,0,0,0⟩,1⟩)

theorem identityTerms_value (p : Fin 4→ℂ) : sourceMatrix identityTerms p=1 := by
  unfold sourceMatrix identityTerms
  rw [List.map_map,←List.ofFn_eq_map,List.sum_ofFn]
  have one : coefficientValue (1:SourceCoefficient)=1 := coefficientMap.map_one
  simpa only [Function.comp_apply,SourceTerm.matrix,one,Powers.value,pow_zero,mul_one] using
    (Matrix.sum_single_one (m:=Fin 289) (α:=ℂ))

def sourceRow (block offset : Fin 17) : Fin 289 :=
  ⟨block.val*17+offset.val,by have hb:=block.isLt;have ho:=offset.isLt;omega⟩

private theorem inverse_block0 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 0 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 0 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block1 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 1 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 1 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block2 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 2 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 2 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block3 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 3 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 3 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block4 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 4 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 4 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block5 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 5 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 5 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block6 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 6 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 6 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block7 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 7 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 7 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block8 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 8 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 8 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block9 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 9 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 9 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block10 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 10 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 10 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block11 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 11 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 11 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block12 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 12 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 12 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block13 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 13 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 13 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block14 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 14 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 14 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block15 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 15 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 15 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_block16 (i : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow 16 i) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow 16 i) identityTerms))=[] := by
  fin_cases i <;> decide +kernel

private theorem inverse_blocks (block offset : Fin 17) :
    fastNormalizeTerms (productTerms (rowTerms (sourceRow block offset) originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms (sourceRow block offset) identityTerms))=[] := by
  fin_cases block
  · exact inverse_block0 offset
  · exact inverse_block1 offset
  · exact inverse_block2 offset
  · exact inverse_block3 offset
  · exact inverse_block4 offset
  · exact inverse_block5 offset
  · exact inverse_block6 offset
  · exact inverse_block7 offset
  · exact inverse_block8 offset
  · exact inverse_block9 offset
  · exact inverse_block10 offset
  · exact inverse_block11 offset
  · exact inverse_block12 offset
  · exact inverse_block13 offset
  · exact inverse_block14 offset
  · exact inverse_block15 offset
  · exact inverse_block16 offset

private theorem inverse_rows (i : Fin 289) :
    fastNormalizeTerms (productTerms (rowTerms i originalInverseTerms) originalChangeTerms++
      negativeTerms (rowTerms i identityTerms))=[] := by
  let block : Fin 17:=⟨i.val/17,by have hi:=i.isLt;omega⟩
  let offset : Fin 17:=⟨i.val%17,Nat.mod_lt _ (by decide)⟩
  have eq : i=sourceRow block offset := by apply Fin.ext;dsimp [sourceRow,block,offset];omega
  rw [eq]
  exact inverse_blocks block offset

theorem original_inverse_change (p : Fin 4→ℂ) : originalInverse p*originalChange p=1 := by
  ext i j
  have h:=congrFun (congrFun (normalization_equal (productTerms (rowTerms i originalInverseTerms) originalChangeTerms) (rowTerms i identityTerms) (inverse_rows i) p) i) j
  rw [row_product_entry,rowTerms_entry,identityTerms_value] at h
  exact h


theorem original_change_inverse (p : Fin 4→ℂ) : originalChange p*originalInverse p=1 :=
  mul_eq_one_comm.mp (original_inverse_change p)

def Powers.total (a : Powers) : ℕ := a.temporal+a.first+a.second+a.third

theorem Powers.value_neg (a : Powers) (p : Fin 4→ℂ) :
    a.value (-p)=(-1:ℂ)^a.total*a.value p := by
  have power (x : ℂ) (n : ℕ) : (-x)^n=(-1:ℂ)^n*x^n := by
    rw [show -x=(-1:ℂ)*x by ring,mul_pow]
  simp only [value,Pi.neg_apply]
  rw [power (p 0) a.temporal,power (p 1) a.first,power (p 2) a.second,power (p 3) a.third]
  simp only [total,pow_add]
  ring

def reflectedTerms (ts : List SourceTerm) : List SourceTerm :=
  ts.map (fun a=>⟨a.column,a.row,a.powers,(-1)^a.powers.total*a.coefficient⟩)

theorem reflectedTerms_value (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (reflectedTerms ts) p=(sourceMatrix ts (-p)).transpose := by
  induction ts with
  | nil=>rfl
  | cons a rest ih=>
    have hc : coefficientValue ((-1)^a.powers.total*a.coefficient)=
        (-1:ℂ)^a.powers.total*coefficientValue a.coefficient := by
      change coefficientMap _=_
      rw [map_mul,map_pow,map_neg,map_one]
      rfl
    simp only [reflectedTerms,List.map_cons,sourceMatrix_cons] at ih ⊢
    rw [ih,Matrix.transpose_add]
    congr 1
    simp only [SourceTerm.matrix,Matrix.transpose_single,hc,Powers.value_neg]
    congr 1
    ring

def originalRowLift (p : Fin 4→ℂ) := (originalInverse (-p)).transpose
def originalReadback (p : Fin 4→ℂ) := (originalChange (-p)).transpose

theorem original_row_readback (p : Fin 4→ℂ) : originalRowLift p*originalReadback p=1 := by
  rw [originalRowLift,originalReadback,←Matrix.transpose_mul,original_change_inverse,Matrix.transpose_one]

def activeFlag (i : Fin 289) : Bool := decide ((9 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < 112)
def nullFlag (i : Fin 289) : Bool := decide ((112 : ℕ) ≤ (i : ℕ) ∧ (i : ℕ) < 121)
def contactFlag (i : Fin 289) : Bool := decide ((i : ℕ) < 9 ∨ (121 : ℕ) ≤ (i : ℕ))
def projectionMatrix (flag : Fin 289→Bool) : Matrix (Fin 289) (Fin 289) ℂ :=
  Matrix.diagonal (fun i=>if flag i then 1 else 0)
def activeProjection := projectionMatrix activeFlag
def nullProjection := projectionMatrix nullFlag
def contactProjection := projectionMatrix contactFlag

def projectionTerms (flag : Fin 289→Bool) : List SourceTerm :=
  (List.finRange 289).map (fun i=>⟨i,i,⟨0,0,0,0⟩,if flag i then 1 else 0⟩)

theorem projectionTerms_value (flag : Fin 289→Bool) (p : Fin 4→ℂ) :
    sourceMatrix (projectionTerms flag) p=projectionMatrix flag := by
  unfold sourceMatrix projectionTerms
  rw [List.map_map,←List.ofFn_eq_map,List.sum_ofFn]
  have value (i : Fin 289) : coefficientValue (if flag i then 1 else 0)=
      (if flag i then 1 else 0:ℂ) := by
    split <;> simp [coefficient_zero,show coefficientValue (1:SourceCoefficient)=1 from coefficientMap.map_one]
  simpa only [Function.comp_apply,SourceTerm.matrix,value,Powers.value,pow_zero,mul_one,projectionMatrix] using!
    (Matrix.sum_single_eq_diagonal (fun i : Fin 289=>if flag i then (1:ℂ) else 0))

def columnTerms (flag : Fin 289→Bool) (ts : List SourceTerm) : List SourceTerm :=
  ts.filter (fun a=>flag a.column)

private theorem term_projection (a : SourceTerm) (flag : Fin 289→Bool) (p : Fin 4→ℂ) :
    a.matrix p*projectionMatrix flag=if flag a.column then a.matrix p else 0 := by
  ext i j
  simp only [projectionMatrix,Matrix.mul_diagonal]
  by_cases same : a.column=j
  · rw [←same]
    split_ifs <;> simp [SourceTerm.matrix,Matrix.single]
  · split_ifs <;> simp [SourceTerm.matrix,Matrix.single,same]

theorem columnTerms_value (flag : Fin 289→Bool) (ts : List SourceTerm) (p : Fin 4→ℂ) :
    sourceMatrix (columnTerms flag ts) p=sourceMatrix ts p*projectionMatrix flag := by
  induction ts with
  | nil=>simp [columnTerms,sourceMatrix]
  | cons a rest ih=>
    simp only [columnTerms,List.filter_cons] at ih ⊢
    split_ifs with h
    · rw [sourceMatrix_cons,ih,sourceMatrix_cons,add_mul,term_projection,if_pos h]
    · rw [ih,sourceMatrix_cons,add_mul,term_projection,if_neg h,zero_add]

theorem projection_partition : contactProjection+activeProjection+nullProjection=1 := by
  ext i j
  by_cases same : i=j
  · subst j
    simp only [contactProjection,activeProjection,nullProjection,projectionMatrix,
      Matrix.add_apply,Matrix.diagonal_apply_eq,Matrix.one_apply_eq]
    unfold contactFlag activeFlag nullFlag
    simp only [decide_eq_true_eq]
    split_ifs <;> norm_num <;> omega
  · simp [contactProjection,activeProjection,nullProjection,projectionMatrix,same]

private def canonicalTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(432/625:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-12/25:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-12/25:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-12/25:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(144/125:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-72/125:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(72/125:ℚ),0⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(12/25:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(36/125:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-36/125:ℚ),0⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,(12/25:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨0,0⟩,⟨0,(12/25:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-72/125:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-24/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,-2⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-144/125:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(72/125:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-72/125:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(72/125:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1667/5625:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(72/125:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-72/125:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-2153/5625:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4097/5625:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/18:ℚ)⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4/5:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(10/9:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(10/9:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-12/25:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-8/3:ℚ),0⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨0,(-10/9:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(4/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(-10/9:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(4/3:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(8/3:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-8/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-4/3:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(4/3:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(2/3:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-2/3:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-4/3:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,8⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(24/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4/25:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-4/3:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(3/5:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(4/3:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(11/25:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(5/9:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(5/9:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-5/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(5/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-1/5:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(6/25:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(10/9:ℚ)⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(-10/9:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨(-10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨(-36/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(5/9:ℚ)⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(-5/9:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(5/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-5/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(-10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(2/5:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-2/5:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(16/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,4⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,-4⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨(10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨(-10/3:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,-1⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-18/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-12/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(12/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(6/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-6/5:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-18/125:ℚ)⟩⟩),
  (⟨1,0,1,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/18:ℚ)⟩⟩),
  (⟨1,0,0,1⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(18/125:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,1⟩,⟨0,0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨1,1,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,-1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,1⟩,⟨0,0⟩⟩),
  (⟨0,0,0,2⟩,⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩),
  (⟨2,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,0,1,1⟩,⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(3/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,(-1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-3/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,(1/2:ℚ)⟩,⟨0,0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,1,0,1⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(3/25:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-6/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,0,2,0⟩,⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩),
  (⟨0,1,1,0⟩,⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-3/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(3/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(6/25:ℚ),0⟩⟩),
  (⟨0,2,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(3/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-3/25:ℚ),0⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-36/125:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(54/125:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-18/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-54/125:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-27/125:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(9/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-9/25:ℚ)⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,-2⟩,⟨0,0⟩⟩)]
private def canonicalTermsCodes : List ℕ := [
  506340,506341,506342,506343,506538,507509,507704,508675,509840,510035,511006,513335,513530,515859,516248,516831,520130,520519,
  521295,562424,562600,562601,562602,562603,563589,563784,564935,567266,568235,568428,569411,569595,571926,572322,572905,574256,
  574644,575421,618884,618861,618862,618863,619079,619268,619448,621195,621779,623526,623912,625855,626047,632456,633621,674952,
  675144,675121,675122,675123,675319,675528,677455,677650,679786,680172,681918,682115,686582,687747,731011,731192,731404,731381,
  731382,731383,731600,733523,733715,735657,736046,738375,738566,744007,745170,787063,787271,787471,787664,787641,787642,787643,
  789394,789975,791917,792306,794439,794635,798133,799296,842742,842950,843927,843901,843902,843903,844122,844123,844124,844125,
  844708,844903,845073,846235,846456,847594,848566,848785,850895,851114,852279,852668,853251,854392,855557,898807,899015,899994,
  899995,899996,899997,900187,900161,900162,900163,900774,900969,901138,902328,902495,903661,904657,904826,906986,907155,908348,
  908737,909320,910071,911234,956463,956421,956422,956423,958755,961086,963415,1012723,1012681,1012682,1012683,1015015,1017346,1019675,
  1068196,1068390,1068983,1068941,1068942,1068943,1069166,1071275,1073606,1075935,1124263,1124457,1125038,1125243,1125229,1125230,1125231,1127562,
  1129891,1132220,1134335,1134722,1135498,1135887,1179139,1180304,1180499,1181504,1181505,1181506,1181507,1181702,1183837,1184032,1185003,1185198,
  1186169,1186364,1187335,1187530,1188501,1188845,1189259,1189436,1189666,1190019,1190203,1192754,1193530,1193918,1235399,1237585,1237780,1237765,
  1237766,1237767,1238751,1238946,1239914,1240097,1241081,1241276,1242247,1242429,1243390,1243590,1244576,1244912,1245308,1245547,1245891,1246323,
  1246492,1246877,1247656,1248041,1291659,1292243,1294048,1294025,1294026,1294027,1294243,1294430,1296357,1296572,1296760,1296942,1298689,1298893,
  1299094,1299274,1304692,1305856,1347919,1348114,1350117,1350308,1350285,1350286,1350287,1350690,1352446,1352617,1352813,1353020,1354766,1354949,
  1355145,1355354,1358818,1359982,1403987,1404179,1406173,1406568,1406545,1406546,1406547,1406765,1408503,1408686,1408877,1409094,1410840,1411018,
  1411209,1411414,1417403,1418567,1459858,1460439,1462433,1462635,1462828,1462805,1462806,1462807,1464557,1464763,1464964,1465137,1466889,1467100,
  1467285,1467469,1471529,1472693,1515537,1516699,1516920,1518112,1519093,1519065,1519066,1519067,1519288,1519289,1519290,1519291,1519874,1520069,
  1520236,1520442,1521397,1521622,1522568,1522787,1523729,1523952,1524923,1525265,1525506,1525847,1526283,1526478,1526626,1527792,1571602,1572792,
  1572959,1574177,1575160,1575161,1575162,1575163,1575353,1575325,1575326,1575327,1575940,1576135,1576301,1576507,1577494,1577657,1578633,1578859,
  1579824,1579989,1580994,1581334,1581577,1581916,1582354,1582549,1582689,1583467,1584631,1629219,1631632,1631585,1631586,1631587,1633917,1636249,
  1685479,1687892,1687845,1687846,1687847,1690177,1692509,1741739,1743362,1743556,1744152,1744105,1744106,1744107,1744332,1746437,1748769,1798026,
  1799429,1799623,1800204,1800412,1800395,1800396,1800397,1802728,1805058,1807731,1808122,1808895,1851934,1854301,1854506,1855467,1855662,1856640,
  1856625,1856673,1856627,1856822,1857798,1858003,1859002,1859164,1860116,1860316,1861302,1861691,1862025,1862220,1862803,1863049,1863218,1863603,
  1864382,1864767,1908194,1909163,1909356,1910368,1910561,1911545,1911740,1912705,1912884,1912885,1912933,1912887,1915035,1915262,1916194,1916387,
  1917397,1917703,1918174,1918294,1918563,1918675,1919070,1921609,1922385,1922773,1964454,1964840,1966821,1967038,1967224,1967406,1969168,1969145,
  1969193,1969147,1969363,1969747,1971522,1971674,1971871,1972080,1975544,1976708,2020714,2021100,2022908,2023081,2023277,2023484,2025237,2025428,
  2025405,2025453,2025407,2025608,2027545,2027782,2027954,2028131,2033547,2034711,2076585,2076974,2078967,2079150,2079341,2079556,2081491,2081688,
  2081665,2081713,2081667,2081885,2083616,2083824,2084042,2084193,2088258,2089422,2132845,2133234,2135021,2135227,2135430,2135601,2137352,2137755,
  2137948,2137925,2137973,2137927,2139698,2139876,2140066,2140302,2146261,2147425,2188522,2189494,2189713,2190700,2190906,2191861,2192086,2193041,
  2194213,2194185,2194233,2194187,2194408,2194409,2194432,2194411,2194994,2195189,2195385,2195553,2196562,2196761,2197732,2197915,2198058,2198640,
  2199081,2199269,2199419,2202521,2244589,2245585,2245754,2246765,2246971,2247958,2248121,2249096,2250280,2250281,2250304,2250283,2250473,2250445,
  2250493,2250447,2251060,2251255,2251457,2251620,2252633,2252822,2253799,2253976,2254127,2254709,2255142,2255340,2255482,2258199,2259363,2302014,
  2304381,2306752,2306705,2306753,2306707,2309082,2358274,2360641,2363012,2362965,2363013,2362967,2365342,2414534,2416901,2418482,2418676,2419272,
  2419225,2419273,2419227,2419452,2421602,2470819,2473192,2474549,2474743,2475324,2475532,2475515,2475538,2475517,2477867,2482463,2482851,2483627,
  2524727,2524922,2527097,2527292,2528263,2528458,2529466,2529628,2530617,2530817,2531744,2531746,2531793,2531747,2532918,2533123,2534130,2534319,
  2534431,2534907,2535102,2535676,2535789,2538529,2538920,2539693,2580803,2580987,2583175,2583357,2584355,2584555,2585499,2585726,2586658,2586851,
  2588004,2588006,2588053,2588007,2588991,2589186,2590199,2590585,2590734,2590974,2591087,2591548,2591863,2592655,2593043,2593819,2637247,2637439,
  2639617,2639821,2640024,2640202,2641986,2642138,2642335,2642546,2644288,2644266,2644313,2644267,2644670,2644867,2650855,2652019,2693310,2693507,
  2695694,2695877,2696073,2696284,2698009,2698246,2698416,2698595,2700548,2700526,2700573,2700527,2700728,2700930,2704981,2706145,2749767,2749958,
  2751766,2751946,2752137,2752342,2754080,2754290,2754506,2754657,2756413,2756611,2756808,2756786,2756833,2756787,2762405,2763569,2805831,2806027,
  2807817,2808026,2808213,2808397,2810160,2810340,2810530,2810766,2812472,2812673,2813068,2813046,2813093,2813047,2816531,2817695,2862287,2862506,
  2863496,2863678,2864657,2864880,2865812,2866017,2867026,2867225,2868161,2868352,2869328,2869306,2869353,2869307,2869560,2869530,2869552,2869531,
  2870114,2870309,2870531,2870854,2871436,2871819,2872014,2872209,2872791,2873955,2918378,2918547,2919561,2919750,2920752,2920917,2921884,2922084,
  2923097,2923286,2924216,2924417,2925432,2925402,2925424,2925403,2925588,2925566,2925613,2925567,2926180,2926375,2926598,2926917,2927499,2927888,
  2928083,2928278,2928469,2929633,2974807,2977177,2979546,2981872,2981826,2981873,2981827,3031067,3033437,3035806,3038132,3038086,3038133,3038087,
  3087327,3089697,3092066,3093602,3093796,3094392,3094346,3094393,3094347,3094572,3143612,3145986,3148331,3149669,3149863,3150444,3150652,3150636,
  3150658,3150637,3152733,3153121,3153897,3154285,3199931,3200096,3201088,3201277,3202230,3202415,3203429,3203622,3204601,3204796,3205763,3205958,
  3206931,3207320,3207321,3207322,3207711,3207712,3207902,3207903,3207907,3208296,3208297,3208492,3208493,3208678,3208680,3208683,3208882,3209271,
  3209460,3209848,3210046,3210435,3210624,3211203,3211403,3211794,3211979,3212367,3212567,3253596,3253782,3254778,3254969,3259478,3259677,3260616,
  3263205,3263206,3263595,3263790,3263985,3264180,3264375,3264761,3264958,3265346,3265541,3265929,3266124,3266512,3266707,3267278,3267484,3267873,
  3268054,3268439,3268649,3311990,3312176,3313172,3313363,3314363,3314512,3315501,3315692,3316728,3316841,3317830,3318021,3319064,3319065,3319066,
  3319478,3319673,3320060,3320062,3320063,3320258,3320647,3320836,3320842,3320839,3321030,3321425,3321620,3322008,3322194,3322589,3322784,3323367,
  3323368,3324143,3324144,3324531,3324533,3365720,3365913,3366911,3367102,3369287,3369476,3372981,3375339,3375545,3375725,3375750,3375945,3376334,
  3376701,3376903,3377111,3377499,3377677,3378065,3378276,3378664,3378840,3379404,3379613,3380003,3380180,3380605,3380779,3424139,3424307,3426450,
  3426718,3428779,3428965,3431240,3431200,3431406,3431817,3431998,3432017,3432018,3432213,3432602,3432797,3432992,3433187,3433188,3433577,3433576,
  3434351,3434354,3434741,3434742,3435490,3435692,3436101,3436266,3436654,3436856,3480179,3480427,3481370,3481561,3482508,3482701,3483699,3483890,
  3484837,3485119,3486028,3486219,3487262,3487263,3487267,3487473,3487676,3487678,3487679,3488094,3488258,3488456,3488677,3489034,3489066,3489037,
  3489228,3489623,3490392,3490787,3491565,3491566,3491783,3492172,3492341,3492342,3492729,3492731,3492947,3534008,3534201,3535107,3535304,3536329,
  3538812,3543540,3543746,3543950,3544328,3544506,3544530,3544725,3544896,3545289,3545677,3545872,3546260,3546455,3546843,3547034,3547640,3547832,
  3548219,3548416,3548763,3548995,3592595,3593547,3593746,3594924,3595876,3596075,3597244,3598158,3598349,3599437,3599401,3599607,3600218,3600421,
  3600597,3600778,3600813,3600798,3600993,3601008,3601203,3601398,3601787,3601942,3602330,3602562,3602951,3603106,3603922,3603910,3604279,3604296,
  3605086,3605072,3648467,3649619,3649808,3650796,3651941,3652140,3653116,3654225,3654416,3655468,3655472,3655879,3656061,3656285,3656640,3656874,
  3656880,3657038,3657079,3657058,3657274,3657469,3657858,3658017,3658034,3658405,3658422,3658633,3659022,3659181,3659200,3659948,3660343,3661112,
  3704452,3704691,3705631,3705828,3706825,3706965,3707960,3708157,3709190,3709383,3710289,3710486,3711526,3711528,3711531,3711737,3711940,3711946,
  3711943,3712135,3712352,3712522,3712554,3712525,3712955,3713150,3713298,3713492,3713887,3714082,3714470,3714656,3715051,3715246,3715830,3716047,
  3716436,3716606,3716995,3717211,3759543,3760319,3760732,3762866,3766549,3767325,3767602,3767808,3768006,3768216,3768421,3768422,3768588,3768777,
  3769015,3769214,3769364,3769605,3769994,3770185,3770771,3772126,3815221,3817186,3819320,3822227,3825868,3826445,3827788,3827809,3828386,3871480,
  3872450,3872861,3874995,3878487,3879457,3879735,3879940,3880145,3880348,3880551,3880554,3880727,3880909,3881146,3881345,3881503,3881738,3882125,
  3883291,3884039,3884069,3926576,3930091,3930867,3933583,3935833,3936005,3936233,3936396,3936974,3937174,3937408,3937396,3937591,3937793,3938390,
  3938779,3939556,3940299,3940329,3983030,3985769,3987906,3990037,3994053,3994648,3996002,3996559,3996589,4038708,4042032,4043002,4045715,4047965,
  4048137,4048365,4048528,4049106,4049306,4049540,4049528,4049723,4050523,4050910,4051485,4051688,4052828,4052853,4053426,4095938,4096714,4097128,
  4099262,4102945,4103721,4103998,4104202,4104402,4104611,4104817,4104816,4104984,4105175,4105411,4105610,4105760,4106003,4107165,4107554,4107745,
  4109088,4109113,4109686,4151616,4153582,4155716,4158623,4163428,4164005,4165348,4165373,4165946,4207877,4208847,4209257,4211391,4214883,4215853,
  4216131,4216334,4216541,4216743,4216947,4216948,4217123,4217307,4217542,4217741,4217899,4218523,4219093,4219298,4219685,4221042,4221599,4221633,
  4262973,4266487,4267263,4269979,4272229,4272403,4272629,4272793,4273372,4273570,4273804,4273790,4273987,4274788,4275176,4275353,4275950,4277302,
  4277859,4277893,4319427,4322165,4324302,4326433,4331613,4332208,4333562,4334119,4334153,4375687,4377652,4380171,4382693,4386499,4386533,4387102,
  4388468,4389045,4433330,4435849,4440428,4440587,4440838,4440809,4441009,4441186,4441420,4441391,4441551,4442167,4442768,4442793,4444725,4487042,
  4493079,4493855,4494049,4496462,4496669,4497053,4497281,4497480,4497655,4497843,4497860,4498028,4498256,4498458,4499028,4499053,4500990,4501380,
  4502156,4543496,4546235,4548757,4550503,4554718,4555288,4555313,4556653,4557248,4599175,4605017,4605987,4606184,4608591,4608800,4609187,4609392,
  4609611,4609788,4610006,4609994,4610167,4610387,4611539,4611569,4612142,4613124,4613510,4614085,4614287,4657594,4660113,4664692,4664851,4665102,
  4665073,4665273,4665450,4665684,4665655,4665815,4666431,4667799,4667829,4668402,4669765,4670153,4670345,4712082,4714048,4716567,4719089,4724059,
  4724089,4724662,4726028,4726605,4769726,4772245,4776824,4776986,4777234,4777204,4777368,4777582,4777816,4777786,4777988,4778562,4779758,4780328,
  4780349,4781693,4781897,4782285,4823439,4829475,4830251,4830445,4832858,4833064,4833451,4833677,4833876,4834052,4834239,4834258,4834424,4834652,
  4836018,4836588,4836609,4837388,4837775,4837953,4838550,4879893,4882631,4885153,4886899,4892278,4892848,4892869,4894213,4894808]
def canonicalTerms : List SourceTerm := decodeTerms canonicalTermsAtoms canonicalTermsCodes

private def independentDualTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(27/125:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-9/25:ℚ)⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,-2⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(36/125:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(54/125:ℚ)⟩⟩),
  (⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(12/25:ℚ),0⟩⟩),
  (⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨1,0,0,0⟩,⟨⟨0,2⟩,⟨0,0⟩⟩),
  (⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-12/25:ℚ),0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(9/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-54/125:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-18/25:ℚ)⟩⟩)]
private def independentDualTermsCodes : List ℕ := [
  382800,382846,382862,382892,382952,382983,382984,383030,387156,387186,387196,387333,387334,387380,391507,391546,391683,391684,
  391730,395813,395826,395856,395990,396039,396034,400142,400163,400200,400232,400292,400340,400389,400384,404513,404557,404690,
  404739,404734,408812,408872,408900,408946,408962,409083,409090,409130,413256,413286,413296,413433,413440,413480,417607,417646,
  417783,417790,417830,421913,421926,421956,422090,422139,422140,426152,426212,426242,426263,426300,426440,426489,426490,430613,
  430657,430790,430839,430840,434829,434830,434876,435000,435046,435072,435092,435162,439179,439180,439226,439356,439393,439396,
  439454,443529,443530,443576,443707,443746,447836,447873,447880,448013,448033,448056,448154,452186,452223,452230,452352,452363,
  452400,452442,452492,456536,456573,456580,456713,456757,460929,460924,460976,461012,461082,461100,461146,461172,465279,465274,
  465326,465374,465456,465493,465496,469629,469624,469676,469807,469846,473936,473973,473974,474074,474113,474133,474156,478286,
  478323,478324,478362,478412,478452,478463,478500,482636,482673,482674,482813,482857]
def independentDualTerms : List SourceTerm := decodeTerms independentDualTermsAtoms independentDualTermsCodes

private def contactInverseTermsAtoms : List SourceAtom := [
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/18:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(10/27:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/27:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/9:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-4/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(2/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-6/25:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨-1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨1,0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-3/50:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(3/50:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/36:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/36:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/48:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/144:ℚ)⟩⟩),
  (⟨0,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/144:ℚ)⟩⟩)]
private def contactInverseTermsCodes : List ℕ := [
  1258600,1264400,1270200,1276000,1281800,1287600,1293401,1293422,1299182,1299201,1305000,1310800,1316600,1322403,1328200,1334000,1339800,1345600,
  1351400,1357200,1363001,1363022,1368782,1368801,1374600,1380400,1386200,1392003,1397800,1403600,1409400,1415200,1421000,1426800,1432601,1432622,
  1438382,1438401,1444200,1450000,1455800,1461603,1467404,1473204,1479004,1484804,1490604,1496404,1502205,1502226,1507986,1508005,1513804,1519604,
  1525404,1531207,1537004,1542804,1548604,1554404,1560204,1566004,1571805,1571826,1577586,1577605,1583404,1589204,1595004,1600807,1606604,1612404,
  1618204,1624004,1629804,1635604,1641405,1641426,1647186,1647205,1653004,1658804,1664604,1670407,841788,847588,853388,859068,864868,870668,
  876588,882388,888188,893868,899668,905468,911388,917188,922988,928668,934468,940268,946189,951989,957789,963469,969269,975069,
  980989,986789,992589,998269,1004069,1009869,1015789,1021589,1027389,1033069,1038869,1044669,1049148,1050229,1054948,1056029,1060748,1061829,
  1066428,1067509,1072228,1073309,1078028,1079109,1083948,1085029,1089748,1090829,1095548,1096629,1101228,1102309,1107028,1108109,1112828,1113909,
  1118748,1119829,1124548,1125629,1130348,1131429,1136028,1137109,1141828,1142909,1147628,1148709,1153549,1153909,1159349,1159709,1165149,1165509,
  1170829,1171189,1176629,1176989,1182429,1182789,1188349,1188709,1194149,1194509,1199949,1200309,1205629,1205989,1211429,1211789,1217229,1217589,
  1223149,1223509,1228949,1229309,1234749,1235109,1240429,1240789,1246229,1246589,1252029,1252389,701810,702151,702252,707610,707812,708011,
  713410,713571,713672,719213,719431,719532,725013,725092,725291,730813,730851,730952,736614,736755,736895,742371,742414,742514,
  748132,748214,748414,754015,754154,754294,759651,759815,759915,765412,765615,765815,771272,771314,771414,777075,777214,777355,
  782791,783014,783114,788552,788715,788815,794474,794615,794754,800071,800415,800515,805931,806014,806214,811692,811914,812014,
  817535,817675,817814,823211,823415,823615,828972,829315,829415,834934,835074,835215,16,5816,11616,17416,23217,23278,
  23299,29016,34816,40558,40617,40638,46339,46398,46417]
def contactInverseTerms : List SourceTerm := decodeTerms contactInverseTermsAtoms contactInverseTermsCodes

def activeTerms : List SourceTerm := canonicalTerms++independentDualTerms
def activeKernel (p : Fin 4→ℂ) := sourceMatrix activeTerms p
def contactInverse (p : Fin 4→ℂ) := sourceMatrix contactInverseTerms p

def jacobiChangeRow (i : Fin 289) : List SourceTerm :=
  fastNormalizeTerms (productTerms (rowTerms i originalJacobiTerms) originalChangeTerms)

def activeDifference (i : Fin 289) : List SourceTerm :=
  columnTerms activeFlag (jacobiChangeRow i)++negativeTerms
    (productTerms (rowTerms i (reflectedTerms originalInverseTerms)) activeTerms)
def contactDifference (i : Fin 289) : List SourceTerm :=
  productTerms (jacobiChangeRow i) contactInverseTerms++negativeTerms
    (columnTerms contactFlag (rowTerms i (reflectedTerms originalInverseTerms)))
def nullDifference (i : Fin 289) : List SourceTerm :=
  columnTerms nullFlag (jacobiChangeRow i)
def transposeDifference (i : Fin 289) : List SourceTerm :=
  rowTerms i (reflectedTerms originalJacobiTerms)++negativeTerms (rowTerms i originalJacobiTerms)

private theorem cover_rows (P : Fin 289→Prop) (all : ∀ block offset,P (sourceRow block offset)) (i : Fin 289) : P i := by
  let block : Fin 17:=⟨i.val/17,by have hi:=i.isLt;omega⟩
  let offset : Fin 17:=⟨i.val%17,Nat.mod_lt _ (by decide)⟩
  have eq : i=sourceRow block offset := by apply Fin.ext;dsimp [sourceRow,block,offset];omega
  rw [eq]
  exact all block offset

private theorem active_block0 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 0 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block1 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 1 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block2 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 2 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block3 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 3 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block4 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 4 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block5 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 5 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block6 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 6 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block7 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 7 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block8 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 8 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block9 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 9 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block10 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 10 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block11 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 11 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block12 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 12 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block13 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 13 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block14 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 14 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block15 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 15 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_block16 (i : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow 16 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem active_blocks (block offset : Fin 17) : fastNormalizeTerms (activeDifference (sourceRow block offset))=[] := by
  fin_cases block
  · exact active_block0 offset
  · exact active_block1 offset
  · exact active_block2 offset
  · exact active_block3 offset
  · exact active_block4 offset
  · exact active_block5 offset
  · exact active_block6 offset
  · exact active_block7 offset
  · exact active_block8 offset
  · exact active_block9 offset
  · exact active_block10 offset
  · exact active_block11 offset
  · exact active_block12 offset
  · exact active_block13 offset
  · exact active_block14 offset
  · exact active_block15 offset
  · exact active_block16 offset
private theorem active_rows (i : Fin 289) : fastNormalizeTerms (activeDifference i)=[] :=
  cover_rows (fun j=>fastNormalizeTerms (activeDifference j)=[]) active_blocks i

private theorem contact_block0 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 0 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block1 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 1 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block2 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 2 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block3 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 3 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block4 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 4 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block5 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 5 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block6 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 6 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block7 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 7 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block8 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 8 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block9 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 9 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block10 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 10 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block11 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 11 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block12 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 12 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block13 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 13 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block14 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 14 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block15 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 15 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_block16 (i : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow 16 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem contact_blocks (block offset : Fin 17) : fastNormalizeTerms (contactDifference (sourceRow block offset))=[] := by
  fin_cases block
  · exact contact_block0 offset
  · exact contact_block1 offset
  · exact contact_block2 offset
  · exact contact_block3 offset
  · exact contact_block4 offset
  · exact contact_block5 offset
  · exact contact_block6 offset
  · exact contact_block7 offset
  · exact contact_block8 offset
  · exact contact_block9 offset
  · exact contact_block10 offset
  · exact contact_block11 offset
  · exact contact_block12 offset
  · exact contact_block13 offset
  · exact contact_block14 offset
  · exact contact_block15 offset
  · exact contact_block16 offset
private theorem contact_rows (i : Fin 289) : fastNormalizeTerms (contactDifference i)=[] :=
  cover_rows (fun j=>fastNormalizeTerms (contactDifference j)=[]) contact_blocks i

private theorem null_block0 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 0 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block1 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 1 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block2 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 2 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block3 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 3 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block4 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 4 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block5 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 5 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block6 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 6 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block7 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 7 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block8 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 8 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block9 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 9 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block10 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 10 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block11 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 11 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block12 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 12 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block13 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 13 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block14 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 14 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block15 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 15 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_block16 (i : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow 16 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem null_blocks (block offset : Fin 17) : fastNormalizeTerms (nullDifference (sourceRow block offset))=[] := by
  fin_cases block
  · exact null_block0 offset
  · exact null_block1 offset
  · exact null_block2 offset
  · exact null_block3 offset
  · exact null_block4 offset
  · exact null_block5 offset
  · exact null_block6 offset
  · exact null_block7 offset
  · exact null_block8 offset
  · exact null_block9 offset
  · exact null_block10 offset
  · exact null_block11 offset
  · exact null_block12 offset
  · exact null_block13 offset
  · exact null_block14 offset
  · exact null_block15 offset
  · exact null_block16 offset
private theorem null_rows (i : Fin 289) : fastNormalizeTerms (nullDifference i)=[] :=
  cover_rows (fun j=>fastNormalizeTerms (nullDifference j)=[]) null_blocks i

private theorem transpose_block0 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 0 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block1 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 1 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block2 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 2 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block3 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 3 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block4 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 4 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block5 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 5 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block6 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 6 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block7 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 7 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block8 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 8 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block9 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 9 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block10 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 10 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block11 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 11 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block12 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 12 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block13 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 13 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block14 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 14 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block15 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 15 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_block16 (i : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow 16 i))=[] := by
  fin_cases i <;> decide +kernel
private theorem transpose_blocks (block offset : Fin 17) : fastNormalizeTerms (transposeDifference (sourceRow block offset))=[] := by
  fin_cases block
  · exact transpose_block0 offset
  · exact transpose_block1 offset
  · exact transpose_block2 offset
  · exact transpose_block3 offset
  · exact transpose_block4 offset
  · exact transpose_block5 offset
  · exact transpose_block6 offset
  · exact transpose_block7 offset
  · exact transpose_block8 offset
  · exact transpose_block9 offset
  · exact transpose_block10 offset
  · exact transpose_block11 offset
  · exact transpose_block12 offset
  · exact transpose_block13 offset
  · exact transpose_block14 offset
  · exact transpose_block15 offset
  · exact transpose_block16 offset
private theorem transpose_rows (i : Fin 289) : fastNormalizeTerms (transposeDifference i)=[] :=
  cover_rows (fun j=>fastNormalizeTerms (transposeDifference j)=[]) transpose_blocks i

theorem jacobiChangeRow_value (i : Fin 289) (p : Fin 4→ℂ) :
    sourceMatrix (jacobiChangeRow i) p=sourceMatrix (rowTerms i originalJacobiTerms) p*originalChange p := by
  rw [jacobiChangeRow,fastNormalizeTerms_value,productTerms_value]
  rfl

theorem original_active_intertwiner (p : Fin 4→ℂ) :
    originalJacobi p*originalChange p*activeProjection=originalRowLift p*activeKernel p := by
  ext i j
  have h:=congrFun (congrFun (normalization_equal (columnTerms activeFlag (jacobiChangeRow i)) (productTerms (rowTerms i (reflectedTerms originalInverseTerms)) activeTerms) (active_rows i) p) i) j
  rw [columnTerms_value,jacobiChangeRow_value,row_product_entry,reflectedTerms_value] at h
  simpa only [originalJacobi,originalChange,originalRowLift,originalInverse,activeKernel,
    activeProjection,Matrix.mul_apply,rowTerms_entry] using h

theorem original_contact_intertwiner (p : Fin 4→ℂ) :
    originalJacobi p*originalChange p*contactInverse p=originalRowLift p*contactProjection := by
  ext i j
  have h:=congrFun (congrFun (normalization_equal (productTerms (jacobiChangeRow i) contactInverseTerms) (columnTerms contactFlag (rowTerms i (reflectedTerms originalInverseTerms))) (contact_rows i) p) i) j
  rw [productTerms_value,jacobiChangeRow_value,columnTerms_value] at h
  simpa only [originalJacobi,originalChange,originalRowLift,originalInverse,contactInverse,
    contactProjection,Matrix.mul_apply,rowTerms_entry,reflectedTerms_value] using h

theorem original_null_intertwiner (p : Fin 4→ℂ) :
    originalJacobi p*originalChange p*nullProjection=0 := by
  ext i j
  have h:=fastNormalizeTerms_value (nullDifference i) p
  rw [null_rows,sourceMatrix_nil] at h
  have hi:=congrFun (congrFun h.symm i) j
  rw [nullDifference,columnTerms_value,jacobiChangeRow_value] at hi
  simpa only [originalJacobi,originalChange,nullProjection,Matrix.mul_apply,rowTerms_entry] using hi

theorem original_jacobi_reciprocity (p : Fin 4→ℂ) : (originalJacobi (-p)).transpose=originalJacobi p := by
  ext i j
  have h:=congrFun (congrFun (normalization_equal (rowTerms i (reflectedTerms originalJacobiTerms)) (rowTerms i originalJacobiTerms) (transpose_rows i) p) i) j
  rw [rowTerms_entry,rowTerms_entry,reflectedTerms_value] at h
  exact h

end LowEnergy.PreparationVacuumOriginalGreenFeedback
