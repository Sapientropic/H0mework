import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceContactFullFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCoframeSpinConnection
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeKinetic GaussCoframeForm
open scoped ContDiff Matrix

/-- The three columns are the original rotation currents numbered 3,4,5. -/
def currentRows (q : Coframe) : Matrix (Fin 6) (Fin 3) ℝ :=
  !![0,0,0;0,0,q 0;0,0,0;q 1,-q 0,0;q 2,0,0;0,0,0]

def spinConnection (q : Coframe) : Matrix (Fin 6) (Fin 3) ℝ :=
  !![0,0,0;0,0,-1/(2*q 0);0,0,q 1/(2*q 0*q 2);0,1/(2*q 0),0;
    -1/(2*q 2),-q 1/(2*q 0*q 2),0;
    q 4/(2*q 2*q 5),(q 1*q 4-q 2*q 3)/(2*q 0*q 2*q 5),0]

private theorem diagonal_ne (z : physicalChart) :
    z.val.1 0 ≠ 0 ∧ z.val.1 2 ≠ 0 ∧ z.val.1 5 ≠ 0 := by
  have h := (volume_pos z).ne'
  change z.val.1 0*z.val.1 2*z.val.1 5 ≠ 0 at h
  exact ⟨(mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).1,
    (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp h).1).2,(mul_ne_zero_iff.mp h).2⟩

/-- Generated on the full physical chart, retaining all off-diagonal coframe coefficients. -/
theorem original_polynomial_connection (z : physicalChart) (i : Fin 6) (a : Fin 3) :
    (∑ j : Fin 6,polynomial z.val.1 i j*spinConnection z.val.1 j a)=2*currentRows z.val.1 i a := by
  obtain ⟨h0,h2,h5⟩ := diagonal_ne z
  fin_cases i <;> fin_cases a <;>
    simp [polynomial,spinConnection,currentRows,Fin.sum_univ_succ] <;>
    field_simp <;> ring

/-- The actual metric returns the coefficient of each original mixed half. -/
theorem original_metric_connection (z : physicalChart) (i : Fin 6) (a : Fin 3) :
    (∑ j : Fin 6,coefficient i j z.val*spinConnection z.val.1 j a)=
      inverseVolume z.val/2*currentRows z.val.1 i a := by
  simp only [coefficient,mul_assoc,←Finset.mul_sum]
  rw [original_polynomial_connection]
  unfold inverseVolume
  ring

private theorem connection_rows (z : physicalChart) (a b : Fin 3) :
    (∑ i : Fin 6,spinConnection z.val.1 i a*currentRows z.val.1 i b)=
      if a=b then -1/2 else 0 := by
  obtain ⟨h0,h2,h5⟩ := diagonal_ne z
  fin_cases a <;> fin_cases b <;>
    simp [spinConnection,currentRows,Fin.sum_univ_succ]
  all_goals field_simp
  all_goals ring

/-- The square completion has the fixed signed rotational price; no positive metric is assumed. -/
theorem original_connection_quadratic (z : physicalChart) (a b : Fin 3) :
    (∑ i : Fin 6,∑ j : Fin 6,spinConnection z.val.1 i a*coefficient i j z.val*spinConnection z.val.1 j b)=
      if a=b then -inverseVolume z.val/4 else 0 := by
  simp only [mul_assoc,←Finset.mul_sum,original_metric_connection]
  have he : (∑ i : Fin 6,spinConnection z.val.1 i a*(inverseVolume z.val/2*currentRows z.val.1 i b))=
      inverseVolume z.val/2*(∑ i : Fin 6,spinConnection z.val.1 i a*currentRows z.val.1 i b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,connection_rows]
  split_ifs <;> ring

abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
def rotation (a : Fin 3) : FiberEnd :=
  GaussQuantumMultiplier.quantized (GaussCoframeSpin.full ⟨3+a.val,by omega⟩)
def connectionFiber (i : Fin 6) (z : SourceCoordinateSlice) : FiberEnd :=
  ∑ a : Fin 3,spinConnection z.1 i a • rotation a

private theorem weighted_square {R : Type*} [Ring R] [Algebra ℝ R]
    (m : Fin 6 → Fin 6 → ℝ) (b : Fin 6 → Fin 3 → ℝ) (S : Fin 3 → R) :
    (∑ i : Fin 6,∑ j : Fin 6,m i j • ((∑ a : Fin 3,b i a • S a)*(∑ a : Fin 3,b j a • S a)))=
      ∑ a : Fin 3,∑ c : Fin 3,(∑ i : Fin 6,∑ j : Fin 6,b i a*m i j*b j c) • (S a*S c) := by
  have shuffle (f : Fin 6 → Fin 6 → Fin 3 → Fin 3 → R) :
      (∑ i,∑ j,∑ a,∑ c,f i j a c)=(∑ a,∑ c,∑ i,∑ j,f i j a c) := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun ij : Fin 6 × Fin 6 => fun ac : Fin 3 × Fin 3 => f ij.1 ij.2 ac.1 ac.2))
  simp only [Finset.sum_mul,Finset.mul_sum,smul_mul_assoc,mul_smul_comm,
    Finset.smul_sum,smul_smul]
  rw [shuffle,Finset.sum_comm]
  simp only [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The complete ordered full-CAR connection square returns the original three rotation squares at the generated signed price. -/
theorem original_connection_fiber_square (z : physicalChart) :
    (∑ i : Fin 6,∑ j : Fin 6,coefficient i j z.val • (connectionFiber i z.val*connectionFiber j z.val))=
      (-inverseVolume z.val/4) • (∑ a : Fin 3,rotation a*rotation a) := by
  change (∑ i : Fin 6,∑ j : Fin 6,coefficient i j z.val •
    ((∑ a : Fin 3,spinConnection z.val.1 i a • rotation a)*(∑ a : Fin 3,spinConnection z.val.1 j a • rotation a)))=_
  rw [weighted_square (R := FiberEnd)]
  simp_rw [original_connection_quadratic]
  simp only [ite_smul,zero_smul]
  simp [Finset.smul_sum]

end LowEnergy.SourceCoframeSpinConnection
