import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceQuantumGaugeSliceCoordinates
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussHistoryHilbert

/-! The original raw gauge coordinates. Raw Cartan D02,D12 become native
D01,D12 by c7=x6+x7; this is required before deleting rows 0,6,18. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationCoordinates
open SourceQuantumScalarChart SourceQuantumNativeDimensions
open SourceQuantumConfigurationHilbert SourceQuantumResidualGaugeSlice
open SourceQuantumGaugeSliceCoordinates

def rawRead (a : NativeLie) : Fin 12 → ℝ :=
  let c := nativeCoordinates a
  ![c.1 0,c.1 1,c.1 2,c.1 3,c.1 4,c.1 5,c.1 6,c.1 7-c.1 6,
    c.2.1 0,c.2.1 1,c.2.1 2,c.2.2]

def rawBuild (x : Fin 12 → ℝ) : NativeLie :=
  nativeCoordinates.symm (![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 6+x 7],![x 8,x 9,x 10],x 11)

def rawCoordinates : NativeLie ≃ₗ[ℝ] (Fin 12 → ℝ) where
  toFun := rawRead
  invFun := rawBuild
  left_inv a := by
    apply nativeCoordinates.injective
    simp only [rawBuild, LinearEquiv.apply_symm_apply]
    apply Prod.ext
    · ext i; fin_cases i <;> simp [rawRead]
    · apply Prod.ext
      · ext i; fin_cases i <;> simp [rawRead]
      · rfl
  right_inv x := by
    ext i; fin_cases i <;> simp [rawRead,rawBuild]
  map_add' a b := by
    ext i; fin_cases i <;> simp [rawRead,map_add,sub_add_sub_comm]
  map_smul' r a := by
    ext i; fin_cases i <;> simp [rawRead,map_smul,mul_sub]

def spatialRow (j : Fin 36) : Fin 3 := ⟨j.val/12, by omega⟩
def nativeRow (j : Fin 36) : Fin 12 := ⟨j.val%12, by omega⟩
def combinedRow (i : Fin 3) (j : Fin 12) : Fin 36 := ⟨12*i.val+j.val, by omega⟩

theorem combined_rows (j : Fin 36) : combinedRow (spatialRow j) (nativeRow j)=j := by
  apply Fin.ext
  simp only [combinedRow,spatialRow,nativeRow]
  omega

theorem spatial_combined (i : Fin 3) (j : Fin 12) : spatialRow (combinedRow i j)=i := by
  apply Fin.ext
  simp only [spatialRow,combinedRow]
  omega

theorem native_combined (i : Fin 3) (j : Fin 12) : nativeRow (combinedRow i j)=j := by
  apply Fin.ext
  simp only [nativeRow,combinedRow]
  omega

def gaugeRead (A : Gauge) (j : Fin 36) : ℝ :=
  rawCoordinates (gaugeCoordinates A (spatialRow j)) (nativeRow j)

def gaugeBuild (x : Fin 36 → ℝ) : Gauge :=
  gaugeCoordinates.symm (fun i => rawCoordinates.symm (fun j => x (combinedRow i j)))

def gaugeRaw : Gauge ≃ₗ[ℝ] (Fin 36 → ℝ) where
  toFun := gaugeRead
  invFun := gaugeBuild
  left_inv A := by
    apply gaugeCoordinates.injective
    funext i
    apply rawCoordinates.injective
    ext j
    simp [gaugeBuild,gaugeRead,spatial_combined,native_combined]
  right_inv x := by
    ext j
    simp [gaugeRead,gaugeBuild,combined_rows]
  map_add' A B := by ext j; simp [gaugeRead,map_add]
  map_smul' r A := by ext j; simp [gaugeRead,map_smul]

-- Rows of the actual 36x33 coordinate_embedding, in the saved ascending order.
def freeRow : Fin 33 → Fin 36 :=
  ![1,2,3,4,5,7,8,9,10,11,12,13,14,15,16,17,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]

def insertFree (x : Fin 33 → ℝ) : Fin 36 → ℝ :=
  ![0,x 0,x 1,x 2,x 3,x 4,0,x 5,x 6,x 7,x 8,x 9,x 10,x 11,x 12,x 13,x 14,x 15,
    0,x 16,x 17,x 18,x 19,x 20,x 21,x 22,x 23,x 24,x 25,x 26,x 27,x 28,x 29,x 30,x 31,x 32]

theorem raw_slice (A : Gauge) : A ∈ coordinateSlice ↔
    gaugeRaw A 0=0 ∧ gaugeRaw A 6=0 ∧ gaugeRaw A 18=0 := by
  rw [coordinateSlice_mem_iff]
  rfl

def gaugeFree : coordinateSlice ≃ₗ[ℝ] (Fin 33 → ℝ) where
  toFun A := fun i => gaugeRaw A.val (freeRow i)
  invFun x := ⟨gaugeRaw.symm (insertFree x), (raw_slice _).mpr (by simp [insertFree])⟩
  left_inv A := by
    apply Subtype.ext
    apply gaugeRaw.injective
    simp only [LinearEquiv.apply_symm_apply]
    have rows := (raw_slice A.val).mp A.property
    ext j
    fin_cases j <;> simp [insertFree,freeRow,rows.1,rows.2.1,rows.2.2]
  right_inv x := by
    ext i
    simp only [LinearEquiv.apply_symm_apply]
    fin_cases i <;> rfl
  map_add' A B := by ext i; simp
  map_smul' r A := by ext i; simp

def gaugeFreeContinuous : coordinateSlice ≃L[ℝ] (Fin 33 → ℝ) :=
  gaugeFree.toContinuousLinearEquiv

theorem decode_original_rows (x : Fin 33 → ℝ) :
    gaugeRaw (gaugeFree.symm x).val=insertFree x :=
  gaugeRaw.apply_symm_apply _

theorem decode_free_rows (x : Fin 33 → ℝ) (i : Fin 33) :
    gaugeRaw (gaugeFree.symm x).val (freeRow i)=x i := by
  exact congrFun (gaugeFree.apply_symm_apply x) i

end LowEnergy.PreparationCoordinates
#print axioms LowEnergy.PreparationCoordinates.rawCoordinates
#print axioms LowEnergy.PreparationCoordinates.gaugeFreeContinuous
#print axioms LowEnergy.PreparationCoordinates.decode_original_rows
