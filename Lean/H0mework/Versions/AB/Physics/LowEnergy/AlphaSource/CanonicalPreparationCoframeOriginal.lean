import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCoframeRationalEntries
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCutoff
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationFullCoordinates
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussCoframeKinetic

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeBudget
open scoped BigOperators ContDiff Topology Matrix

def sourceKEntries : Matrix (Fin 6) (Fin 6) RationalEntry :=
  !![⟨[((-1/4 : ℚ),![1,0,0,0,0,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,0,0,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![0,0,0,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,1,0,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,1,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![0,0,1,0,0,0]⟩;
    ⟨[((1/4 : ℚ),![0,1,0,0,0,0])],![0,0,1,0,0,1]⟩, ⟨[((-1 : ℚ),![2,0,0,0,0,0]),((-1/4 : ℚ),![0,2,0,0,0,0])],![1,0,1,0,0,1]⟩, ⟨[((-1/4 : ℚ),![0,1,0,0,0,0])],![1,0,0,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,1,0,0])],![1,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,0,1,0])],![1,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,0,0,0])],![1,0,1,0,0,0]⟩;
    ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![0,0,0,0,0,1]⟩, ⟨[((-1/4 : ℚ),![0,1,0,0,0,0])],![1,0,0,0,0,1]⟩, ⟨[((-1/4 : ℚ),![0,0,1,0,0,0])],![1,0,0,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,1,0,0])],![1,0,0,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,1,0])],![1,0,0,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![1,0,0,0,0,0]⟩;
    ⟨[((1/4 : ℚ),![0,0,0,1,0,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,1,0,0])],![1,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,1,0,0])],![1,0,0,0,0,1]⟩, ⟨[((-1 : ℚ),![2,0,0,0,0,0]),((-1 : ℚ),![0,2,0,0,0,0]),((-1/4 : ℚ),![0,0,0,2,0,0])],![1,0,1,0,0,1]⟩, ⟨[((-1 : ℚ),![0,1,1,0,0,0]),((-1/4 : ℚ),![0,0,0,1,1,0])],![1,0,1,0,0,1]⟩, ⟨[((-1/4 : ℚ),![0,0,0,1,0,0])],![1,0,1,0,0,0]⟩;
    ⟨[((1/4 : ℚ),![0,0,0,0,1,0])],![0,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,1,0,0,1,0])],![1,0,1,0,0,1]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,1,0])],![1,0,0,0,0,1]⟩, ⟨[((-1 : ℚ),![0,1,1,0,0,0]),((-1/4 : ℚ),![0,0,0,1,1,0])],![1,0,1,0,0,1]⟩, ⟨[((-1 : ℚ),![0,0,2,0,0,0]),((-1/4 : ℚ),![0,0,0,0,2,0])],![1,0,1,0,0,1]⟩, ⟨[((-1/4 : ℚ),![0,0,0,0,1,0])],![1,0,1,0,0,0]⟩;
    ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![0,0,1,0,0,0]⟩, ⟨[((1/4 : ℚ),![0,1,0,0,0,0])],![1,0,1,0,0,0]⟩, ⟨[((1/4 : ℚ),![0,0,0,0,0,0])],![1,0,0,0,0,0]⟩, ⟨[((-1/4 : ℚ),![0,0,0,1,0,0])],![1,0,1,0,0,0]⟩, ⟨[((-1/4 : ℚ),![0,0,0,0,1,0])],![1,0,1,0,0,0]⟩, ⟨[((-1/4 : ℚ),![0,0,0,0,0,1])],![1,0,1,0,0,0]⟩]

def sourceInverseEntries : Matrix (Fin 3) (Fin 3) RationalEntry :=
  !![⟨[((1 : ℚ),![0,0,0,0,0,0])],![1,0,0,0,0,0]⟩, ⟨[],![0,0,0,0,0,0]⟩, ⟨[],![0,0,0,0,0,0]⟩;
    ⟨[((-1 : ℚ),![0,1,0,0,0,0])],![1,0,1,0,0,0]⟩, ⟨[((1 : ℚ),![0,0,0,0,0,0])],![0,0,1,0,0,0]⟩, ⟨[],![0,0,0,0,0,0]⟩;
    ⟨[((1 : ℚ),![0,1,0,0,1,0]),((-1 : ℚ),![0,0,1,1,0,0])],![1,0,1,0,0,1]⟩, ⟨[((-1 : ℚ),![0,0,0,0,1,0])],![0,0,1,0,0,1]⟩, ⟨[((1 : ℚ),![0,0,0,0,0,0])],![0,0,0,0,0,1]⟩]

def sourceVolumeEntry : RationalEntry := ⟨[((1 : ℚ),![1,0,1,0,0,1])],![0,0,0,0,0,0]⟩
def sourceInverseVolumeEntry : RationalEntry := ⟨[((1 : ℚ),![0,0,0,0,0,0])],![1,0,1,0,0,1]⟩

def K0Array (n : ℕ) : ℕ := matrixArray sourceKEntries n
def LInverseArray (n : ℕ) : ℕ := matrixArray sourceInverseEntries n
def volumeArray (n : ℕ) : ℕ := entryArray sourceVolumeEntry n
def inverseVolumeArray (n : ℕ) : ℕ := entryArray sourceInverseVolumeEntry n

open CanonicalPreparationCutoff PreparationScalarCoordinates
open SourceQuantumGaugeSliceCoordinates GaussNativeEnergy GaussHistoryHilbert

def sourceBox (x : Phase) : Prop := ∀ i,|x.1 i-flatSource i| ≤ sourceRadius

def sourceK (i j : Fin 6) : Symbol := fun x =>
  GaussCoframeKinetic.coefficient i j (fullCoordinates.symm x.1)/sourceTime 0

def sourceLInverse (i j : Fin 3) : Symbol := fun x => triadInverse (fullCoordinates.symm x.1).1 i j

def sourceVolume : Symbol := fun x => volume (fullCoordinates.symm x.1)
def sourceVolumeInverse : Symbol := fun x => (volume (fullCoordinates.symm x.1))⁻¹

theorem qCoordinate_native (x : Phase) (i : Fin 6) :
    (fullCoordinates.symm x.1).1 i=qCoordinate i x := rfl

theorem sourceBox_guards (x : Phase) (box : sourceBox x) :
    x∈coframeDomain ∧ (∀ i,|qCoordinate i x|≤15) ∧
      (∀ i,diagonal i → |(qCoordinate i x)⁻¹|≤15) := by
  have lower (i : Fin 6) (hi : diagonal i) : (1/15 : ℝ)≤qCoordinate i x := by
    have center : flatSource (qSlot i).1=1 := by
      rcases hi with rfl|rfl|rfl <;> norm_num [flatSource,qSlot,Fin.ext_iff]
    have near := abs_le.mp (box (qSlot i).1)
    rw [center] at near
    change (1/15 : ℝ)≤x.1 (qSlot i).1
    linarith [radius_small.2]
  refine ⟨?_,?_,?_⟩
  · intro i hi
    exact (lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/15) (lower i hi)).ne'
  · intro i
    have center : |flatSource (qSlot i).1|≤1 := by
      fin_cases i <;> norm_num [flatSource,qSlot,Fin.ext_iff]
    have near := abs_le.mp (box (qSlot i).1)
    have centerBounds := abs_le.mp center
    change |x.1 (qSlot i).1|≤15
    rw [abs_le]
    constructor <;> linarith [radius_small.2]
  · intro i hi
    have positive : 0<qCoordinate i x := lt_of_lt_of_le (by norm_num) (lower i hi)
    rw [abs_of_pos (inv_pos.mpr positive)]
    have estimate := one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1/15) (lower i hi)
    simpa using estimate

theorem sourceK_poles (i j : Fin 6) : poleSupported (sourceKEntries i j).poles := by
  revert i j
  unfold poleSupported
  decide

theorem sourceInverse_poles (i j : Fin 3) : poleSupported (sourceInverseEntries i j).poles := by
  revert i j
  unfold poleSupported
  decide

theorem sourceVolume_poles : poleSupported sourceVolumeEntry.poles := by unfold poleSupported; decide

theorem sourceInverseVolume_poles : poleSupported sourceInverseVolumeEntry.poles := by unfold poleSupported; decide

/-- The actual native lapse cancels from the original kinetic coefficient. -/
theorem sourceK_readback (i j : Fin 6) (x : Phase) (hx : x∈coframeDomain) :
    entryValue (sourceKEntries i j) x=sourceK i j x := by
  have h0 : x.1 0≠0 := hx 0 (by decide)
  have h2 : x.1 2≠0 := hx 2 (by decide)
  have h5 : x.1 5≠0 := hx 5 (by decide)
  unfold sourceK GaussCoframeKinetic.coefficient volume GaussCoframeKinetic.polynomial
  simp_rw [qCoordinate_native]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceKEntries,entryValue,polynomialValue,monomial,powerFactor,
      Fin.prod_univ_succ,qCoordinate,qSlot]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [source_time_nonzero,h0,h2,h5]
  all_goals ring

theorem sourceInverse_readback (i j : Fin 3) (x : Phase) (hx : x∈coframeDomain) :
    entryValue (sourceInverseEntries i j) x=sourceLInverse i j x := by
  have h0 : x.1 0≠0 := hx 0 (by decide)
  have h2 : x.1 2≠0 := hx 2 (by decide)
  have h5 : x.1 5≠0 := hx 5 (by decide)
  unfold sourceLInverse triadInverse
  simp_rw [qCoordinate_native]
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceInverseEntries,entryValue,polynomialValue,monomial,powerFactor,
      Fin.prod_univ_succ,qCoordinate,qSlot]
  all_goals dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  all_goals norm_num
  all_goals field_simp [h0,h2,h5]
  all_goals ring

theorem sourceVolume_readback (x : Phase) : entryValue sourceVolumeEntry x=sourceVolume x := by
  unfold sourceVolume volume
  simp_rw [qCoordinate_native]
  norm_num [sourceVolumeEntry,entryValue,polynomialValue,monomial,powerFactor,Fin.prod_univ_succ]
  dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  norm_num
  ring

theorem sourceInverseVolume_readback (x : Phase) :
    entryValue sourceInverseVolumeEntry x=sourceVolumeInverse x := by
  unfold sourceVolumeInverse volume
  simp_rw [qCoordinate_native]
  norm_num [sourceInverseVolumeEntry,entryValue,polynomialValue,monomial,powerFactor,Fin.prod_univ_succ,mul_inv_rev]
  dsimp [Matrix.vecCons,Fin.cons,Fin.cases,Fin.induction,Fin.induction.go]
  norm_num
  ring

theorem sourceK_jet (i j : Fin 6) (m : ℕ) (w : Word m) (x : Phase) (hx : x∈coframeDomain) :
    jet m (entryValue (sourceKEntries i j)) w x=jet m (sourceK i j) w x := by
  apply jet_germ
  filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
  exact sourceK_readback i j y hy

theorem sourceInverse_jet (i j : Fin 3) (m : ℕ) (w : Word m) (x : Phase) (hx : x∈coframeDomain) :
    jet m (entryValue (sourceInverseEntries i j)) w x=jet m (sourceLInverse i j) w x := by
  apply jet_germ
  filter_upwards [coframeDomain_open.mem_nhds hx] with y hy
  exact sourceInverse_readback i j y hy

theorem actual_K0_row_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (i : Fin 6) :
    (∑ j,|jet m (sourceK i j) w x|)≤(K0Array m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := matrix_row_budget sourceKEntries sourceK_poles m w x hx bound inverse i
  simp_rw [sourceK_jet (x:=x) (hx:=hx)] at read
  simpa only [K0Array] using read

theorem actual_K0_column_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (j : Fin 6) :
    (∑ i,|jet m (sourceK i j) w x|)≤(K0Array m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := matrix_column_budget sourceKEntries sourceK_poles m w x hx bound inverse j
  simp_rw [sourceK_jet (x:=x) (hx:=hx)] at read
  simpa only [K0Array] using read

theorem actual_LInverse_row_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (i : Fin 3) :
    (∑ j,|jet m (sourceLInverse i j) w x|)≤(LInverseArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := matrix_row_budget sourceInverseEntries sourceInverse_poles m w x hx bound inverse i
  simp_rw [sourceInverse_jet (x:=x) (hx:=hx)] at read
  simpa only [LInverseArray] using read

theorem actual_LInverse_column_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) (j : Fin 3) :
    (∑ i,|jet m (sourceLInverse i j) w x|)≤(LInverseArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := matrix_column_budget sourceInverseEntries sourceInverse_poles m w x hx bound inverse j
  simp_rw [sourceInverse_jet (x:=x) (hx:=hx)] at read
  simpa only [LInverseArray] using read

theorem actual_volume_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) :
    |jet m sourceVolume w x|≤(volumeArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := actual_entry_budget sourceVolumeEntry sourceVolume_poles m w x hx bound inverse
  have same : entryValue sourceVolumeEntry=sourceVolume := funext sourceVolume_readback
  simpa only [same,volumeArray] using read

theorem actual_inverseVolume_budget (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x) :
    |jet m sourceVolumeInverse w x|≤(inverseVolumeArray m : ℝ) := by
  obtain ⟨hx,bound,inverse⟩ := sourceBox_guards x box
  have read := actual_entry_budget sourceInverseVolumeEntry sourceInverseVolume_poles m w x hx bound inverse
  have same : entryValue sourceInverseVolumeEntry=sourceVolumeInverse := funext sourceInverseVolume_readback
  simpa only [same,inverseVolumeArray] using read

theorem actual_K0_p_zero (i j : Fin 6) (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x)
    (k : Fin m) (momentum : (w k).2=true) : jet m (sourceK i j) w x=0 := by
  have hx := (sourceBox_guards x box).1
  rw [←sourceK_jet i j m w x hx]
  exact entry_p_zero (sourceKEntries i j) (sourceK_poles i j) m w x hx k momentum

theorem actual_LInverse_p_zero (i j : Fin 3) (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x)
    (k : Fin m) (momentum : (w k).2=true) : jet m (sourceLInverse i j) w x=0 := by
  have hx := (sourceBox_guards x box).1
  rw [←sourceInverse_jet i j m w x hx]
  exact entry_p_zero (sourceInverseEntries i j) (sourceInverse_poles i j) m w x hx k momentum

theorem actual_volume_p_zero (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x)
    (k : Fin m) (momentum : (w k).2=true) : jet m sourceVolume w x=0 := by
  have same : entryValue sourceVolumeEntry=sourceVolume := funext sourceVolume_readback
  rw [←same]
  exact entry_p_zero sourceVolumeEntry sourceVolume_poles m w x (sourceBox_guards x box).1 k momentum

theorem actual_inverseVolume_p_zero (m : ℕ) (w : Word m) (x : Phase) (box : sourceBox x)
    (k : Fin m) (momentum : (w k).2=true) : jet m sourceVolumeInverse w x=0 := by
  have same : entryValue sourceInverseVolumeEntry=sourceVolumeInverse := funext sourceInverseVolume_readback
  rw [←same]
  exact entry_p_zero sourceInverseVolumeEntry sourceInverseVolume_poles m w x (sourceBox_guards x box).1 k momentum


end LowEnergy.PreparationVacuumCoframeBudget
