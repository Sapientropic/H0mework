import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussDiagonalHistory
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.NativeHistoryGrade

/-! The source Number/G labels of all native, Clifford and spatial-matter currents. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussFockLabel
open SaturationMonoid.PhysicsCore
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineHolonomicField SU7MotherLieAlgebra
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussNativeMatter GaussQuantumMultiplier NativeHistoryGrade
open QuantizationCheck.Fermion
open scoped Matrix
attribute [local instance] SourceRealScalarFock.branchOrder

def charge (i : Mode) : ℂ := if i ∈ target then 1 else 0
def Preserves (A : Matrix Mode Mode ℂ) : Prop := ∀ i j, (charge i-charge j)*A i j=0

theorem preserves_add {A B : Matrix Mode Mode ℂ} (hA : Preserves A) (hB : Preserves B) :
    Preserves (A+B) := by
  intro i j
  rw [Matrix.add_apply, mul_add, hA i j, hB i j, add_zero]

theorem preserves_smul {A : Matrix Mode Mode ℂ} (hA : Preserves A) (c : ℂ) :
    Preserves (c • A) := by
  intro i j
  change (charge i-charge j)*(c*A i j)=0
  rw [mul_left_comm, hA i j, mul_zero]

theorem preserves_mul {A B : Matrix Mode Mode ℂ} (hA : Preserves A) (hB : Preserves B) :
    Preserves (A*B) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro k _
  calc
    (charge i-charge j)*(A i k*B k j) =
      ((charge i-charge k)*A i k)*B k j + A i k*((charge k-charge j)*B k j) := by ring
    _ = 0 := by rw [hA i k, hB k j, zero_mul, mul_zero, add_zero]

set_option backward.isDefEq.respectTransparency false in
theorem native_preserves (a : SourceQuantumScalarChart.NativeLie) : Preserves (nativeFull a) := by
  have hp (i j : LowEnergy.Quantum.Index) :
      ((if isSix i then (1 : ℂ) else 0)-(if isSix j then (1 : ℂ) else 0))*nativePrimal a i j = 0 := by
    have h := matrix_grade (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))) 0
      (by
        simp only [Nat.cast_zero, zero_smul, add_zero]
        exact LowEnergy.MixedSymbol.degreeSix_gauge _) i j
    have he : nativePrimal a = LowEnergy.Quantum.operatorMatrix
        (diracExteriorMotherLieAction (p286LieBlockEmbed (p286CoordinateEquiv.symm a))) := rfl
    rw [he]
    simpa only [Nat.cast_zero, sub_zero] using h
  intro i j
  cases i with
  | inl i => cases j with
    | inl j =>
        have he : nativeFull a (Sum.inl i) (Sum.inl j) = nativePrimal a i j := rfl
        rw [he]
        simpa only [charge, mem_target_left] using hp i j
    | inr j => simp [nativeFull]
  | inr i => cases j with
    | inl j => simp [nativeFull]
    | inr j =>
      have h := congrArg star (hp i j)
      simpa [charge, nativeFull, mem_target_right] using h

set_option backward.isDefEq.respectTransparency false in
theorem spin_preserves (a : Fin 7) : Preserves (GaussCoframeSpin.full a) := by
  have hp (i j : LowEnergy.Quantum.Index) :
      ((if isSix i then (1 : ℂ) else 0)-(if isSix j then (1 : ℂ) else 0))*GaussCoframeSpin.primal a i j = 0 := by
    have h := matrix_grade (diracMatrixMatterAction (GaussCoframeSpin.sourceSpin a)) 0
      (by
        simp only [Nat.cast_zero, zero_smul, add_zero]
        exact LowEnergy.MixedSymbol.degreeSix_spin _) i j
    rw [GaussCoframeSpin.spinLift_source] at h
    change ((if isSix i then (1 : ℂ) else 0)-(if isSix j then (1 : ℂ) else 0))*
      GaussCoframeSpin.spinLift (GaussCoframeSpin.sourceSpin a) i j = 0
    simpa only [Nat.cast_zero, sub_zero] using h
  intro i j
  cases i with
  | inl i => cases j with
    | inl j =>
        have he : GaussCoframeSpin.full a (Sum.inl i) (Sum.inl j) = GaussCoframeSpin.primal a i j := rfl
        rw [he]
        simpa only [charge, mem_target_left] using hp i j
    | inr j => simp [GaussCoframeSpin.full]
  | inr i => cases j with
    | inl j => simp [GaussCoframeSpin.full]
    | inr j =>
      have h := congrArg star (hp i j)
      by_cases ha : a.val < 3 <;>
        simpa [charge, GaussCoframeSpin.full, ha, mem_target_right, mul_neg] using h

theorem matter_preserves (i b : Fin 3) (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    Preserves (GaussMatterCore.localMatrix i b z) :=
  preserves_smul (preserves_mul (preserves_smul (spin_preserves _) Complex.I)
    (native_preserves _)) _

theorem quantized_grade (A : Matrix Mode Mode ℂ) (preserves : Preserves A) :
    SourceFockRaising.grade target * LowEnergy.Fermion.quantize A =
      LowEnergy.Fermion.quantize A * SourceFockRaising.grade target := by
  have he : SourceFockRaising.grade target = LowEnergy.Fermion.occupationCharge charge := by
    unfold SourceFockRaising.grade
    congr 1
    funext i
    by_cases hi : i ∈ target <;> simp [charge, hi]
  rw [he]
  exact LowEnergy.Fermion.occupationCharge_quantize charge A preserves

theorem entry_label (A : Matrix Mode Mode ℂ) (preserves : Preserves A)
    (output input : Occupation) (nonzero : matrixEntry A output input ≠ 0) :
    sourceLabel output = sourceLabel input := by
  have hn : output.card = input.card := by
    by_contra h
    exact nonzero (entry_number_zero A output input h)
  have hb : fiberCoordinates (EuclideanSpace.single input 1) = occupationBasis input := by
    funext word
    by_cases h : word = input
    · subst word; simp [fiberCoordinates, occupationBasis]
    · simp [fiberCoordinates, occupationBasis, EuclideanSpace.single, h]
  have he : matrixEntry A output input = (LowEnergy.Fermion.quantize A) (occupationBasis input) output := by
    change (LowEnergy.Fermion.quantize A) (fiberCoordinates (EuclideanSpace.single input 1)) output = _
    rw [hb]
  rw [he] at nonzero
  have hg := SourceGradeTransport.coefficient_grade target (LowEnergy.Fermion.quantize A) 0
    (by simpa only [Nat.cast_zero, zero_smul, add_zero] using quantized_grade A preserves)
    input output nonzero
  apply Prod.ext
  · exact Fin.ext hn
  · apply Fin.ext
    exact hg.trans (Nat.add_zero _)

def blockWeight (c : Label → ℂ) : FockFiber →L[ℂ] FockFiber :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => WithLp.toLp 2 (fun word => c (sourceLabel word)*f word)
      map_add' := by
        intro f g
        apply PiLp.ext
        intro word
        exact mul_add _ _ _
      map_smul' := by
        intro z f
        apply PiLp.ext
        intro word
        change c (sourceLabel word)*(z*f word) = z*(c (sourceLabel word)*f word)
        ring }

theorem blockWeight_apply (c : Label → ℂ) (f : FockFiber) (word : Occupation) :
    blockWeight c f word = c (sourceLabel word)*f word := rfl

theorem blockWeight_basis (c : Label → ℂ) (input : Occupation) :
    blockWeight c (EuclideanSpace.single input 1) = c (sourceLabel input) • EuclideanSpace.single input 1 := by
  apply PiLp.ext
  intro word
  rw [blockWeight_apply]
  by_cases h : word = input
  · subst word; simp
  · simp [EuclideanSpace.single, h]

theorem blockWeight_quantized (c : Label → ℂ) (A : Matrix Mode Mode ℂ) (preserves : Preserves A) :
    Commute (blockWeight c) (quantized A) := by
  show blockWeight c * quantized A = quantized A * blockWeight c
  apply ContinuousLinearMap.ext
  intro f
  have expansion : f = ∑ word : Occupation, f word • EuclideanSpace.single word 1 := by
    apply PiLp.ext
    intro word
    simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single, Pi.single_apply]
  have hsingle (input : Occupation) :
      blockWeight c (quantized A (EuclideanSpace.single input 1)) =
        quantized A (blockWeight c (EuclideanSpace.single input 1)) := by
    rw [blockWeight_basis, map_smul]
    apply PiLp.ext
    intro output
    rw [blockWeight_apply]
    change c (sourceLabel output)*matrixEntry A output input =
      c (sourceLabel input)*matrixEntry A output input
    by_cases hz : matrixEntry A output input = 0
    · rw [hz, mul_zero, mul_zero]
    · rw [entry_label A preserves output input hz]
  change blockWeight c (quantized A f) = quantized A (blockWeight c f)
  rw [expansion, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [map_smul, map_smul, map_smul, map_smul, hsingle]

#print axioms native_preserves
#print axioms spin_preserves
#print axioms matter_preserves
#print axioms entry_label
#print axioms blockWeight_quantized
end LowEnergy.GaussFockLabel
