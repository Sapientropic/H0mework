import H0mework.Versions.AD.Physics.LowEnergy.Quantum.GaussQuantumMultiplier

/-! Seven fixed Hermitian currents from the original Clifford matrices and both branches. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.GaussCoframeSpin
open SaturationMonoid.PhysicsCore
open DiracCliffordRepresentation DiracExteriorMatterAction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussCoreDifferential GaussFockPair
open GaussQuantumMultiplier
open scoped Matrix
local instance : DecidableEq LowEnergy.Quantum.InternalIndex := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def spinLift (S : DiracMatrix) : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ :=
  fun i j => if i.2 = j.2 then S i.1 j.1 else 0

theorem coordinates_spin (S : DiracMatrix) (f : DiracExteriorMatterCarrier)
    (i : LowEnergy.Quantum.Index) :
    LowEnergy.Quantum.coordinates (diracMatrixMatterAction S f) i =
      ∑ j : Fin 4, S i.1 j * LowEnergy.Quantum.coordinates f ⟨j,i.2⟩ := by
  change LowEnergy.Quantum.internalBasis.equivFun (∑ j : Fin 4, S i.1 j • f j) i.2 = _
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

theorem spinLift_source (S : DiracMatrix) :
    LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction S) = spinLift S := by
  ext i j
  let A : Matrix LowEnergy.Quantum.Index LowEnergy.Quantum.Index ℂ :=
    LowEnergy.Quantum.operatorMatrix (diracMatrixMatterAction S)
  change A i j = spinLift S i j
  have h := congrFun (LowEnergy.Quantum.matrix_action (diracMatrixMatterAction S)
    (LowEnergy.Quantum.coordinates.symm (Pi.single j 1))) i
  rw [coordinates_spin, LowEnergy.Quantum.coordinates.apply_symm_apply] at h
  change (∑ k, A i k * (Pi.single j (1 : ℂ) : LowEnergy.Quantum.Index → ℂ) k) =
    ∑ k : Fin 4, S i.1 k * (Pi.single j (1 : ℂ) : LowEnergy.Quantum.Index → ℂ) ⟨k,i.2⟩ at h
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h
  rcases i with ⟨r,x⟩
  rcases j with ⟨c,y⟩
  by_cases hxy : x = y
  · subst y
    simp only [Sigma.mk.inj_iff, heq_iff_eq, and_true, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at h
    simpa only [spinLift, ite_true] using h
  · simp only [Sigma.mk.inj_iff, heq_iff_eq, hxy, and_false, ite_false, Finset.sum_const_zero] at h
    simpa only [spinLift, hxy, ite_false] using h

theorem spinLift_hermitian (S : DiracMatrix) (hermitian : S.conjTranspose = S) :
    (spinLift S).conjTranspose = spinLift S := by
  ext i j
  change star (if j.2 = i.2 then S j.1 i.1 else 0) = if i.2 = j.2 then S i.1 j.1 else 0
  by_cases hij : i.2 = j.2
  · simp only [hij, ite_true]
    exact congrFun (congrFun hermitian i.1) j.1
  · simp [hij, Ne.symm hij]

def sourceSpin (a : Fin 7) : DiracMatrix :=
  ![(1/2 : ℂ) • (diracGammaZero * diracGammaOne),
    (1/2 : ℂ) • (diracGammaZero * diracGammaTwo),
    (1/2 : ℂ) • (diracGammaZero * diracGammaThree),
    (Complex.I/2) • (diracGammaTwo * diracGammaThree),
    (Complex.I/2) • (diracGammaThree * diracGammaOne),
    (Complex.I/2) • (diracGammaOne * diracGammaTwo),
    (-1/2 : ℂ) • diracGammaFive] a

theorem sourceSpin_hermitian (a : Fin 7) : (sourceSpin a).conjTranspose = sourceSpin a := by
  fin_cases a
  · change ((1/2 : ℂ) • (diracGammaZero * diracGammaOne)).conjTranspose = (1/2 : ℂ) • (diracGammaZero * diracGammaOne)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  · change ((1/2 : ℂ) • (diracGammaZero * diracGammaTwo)).conjTranspose = (1/2 : ℂ) • (diracGammaZero * diracGammaTwo)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  · change ((1/2 : ℂ) • (diracGammaZero * diracGammaThree)).conjTranspose = (1/2 : ℂ) • (diracGammaZero * diracGammaThree)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]
  · change ((Complex.I/2) • (diracGammaTwo * diracGammaThree)).conjTranspose = (Complex.I/2) • (diracGammaTwo * diracGammaThree)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod] <;> ring
  · change ((Complex.I/2) • (diracGammaThree * diracGammaOne)).conjTranspose = (Complex.I/2) • (diracGammaThree * diracGammaOne)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod] <;> ring
  · change ((Complex.I/2) • (diracGammaOne * diracGammaTwo)).conjTranspose = (Complex.I/2) • (diracGammaOne * diracGammaTwo)
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod] <;> ring
  · change ((-1/2 : ℂ) • diracGammaFive).conjTranspose = (-1/2 : ℂ) • diracGammaFive
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.smul_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [diracGammaZero, diracGammaOne, diracGammaTwo, diracGammaThree,
        diracGammaFive, Fin.sum_univ_four, Fin.coe_ofNat_eq_mod, Matrix.cons_val, Nat.reduceMod]

def primal (a : Fin 7) := spinLift (sourceSpin a)
def full (a : Fin 7) : Matrix Mode Mode ℂ :=
  Matrix.fromBlocks (primal a) 0 0
    (if a.val < 3 then (primal a).map (starRingEnd ℂ) else -(primal a).map (starRingEnd ℂ))

theorem full_hermitian (a : Fin 7) : (full a).conjTranspose = full a := by
  have hp := spinLift_hermitian (sourceSpin a) (sourceSpin_hermitian a)
  ext i j
  cases i with
  | inl i => cases j with
    | inl j => exact congrFun (congrFun hp i) j
    | inr j => simp [full]
  | inr i => cases j with
    | inl j => simp [full]
    | inr j =>
      have h := congrArg star (congrFun (congrFun hp i) j)
      by_cases ha : a.val < 3 <;> simpa [full, primal, ha, Matrix.conjTranspose_apply] using h

def current (a : Fin 7) : QuantumTest →ₗ[ℂ] QuantumTest :=
  action (fun _ => full a) (fun _ => contDiffAt_const)

theorem current_pair (a : Fin 7) (f g : QuantumTest) :
    sourcePair f (current a g) = sourcePair (current a f) g :=
  action_pair _ _ (fun _ => full_hermitian a) f g

#print axioms spinLift_source
#print axioms full_hermitian
#print axioms current_pair
end LowEnergy.GaussCoframeSpin
