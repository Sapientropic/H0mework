import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceCoframeSpinNormalOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceCoframeSpinContraction
open SaturationMonoid.PhysicsCore DiracCliffordRepresentation
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeSpin GaussCoframeForm SourceCoframeCovariantSquare SourceCoframeSpinNormalOrder GaussQuantumMultiplier
open scoped Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := LinearOrder.toDecidableEq
local instance : DecidableEq SaturationMonoid.PhysicsCore.LowEnergy.Quantum.InternalIndex := Classical.decEq _
local instance : DecidableEq SaturationMonoid.PhysicsCore.LowEnergy.Quantum.Index := Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

/-- All seven original Dirac spin matrices have the same exact one-particle square. -/
theorem original_dirac_spin_square (a : Fin 7) : sourceSpin a*sourceSpin a=(1/4 : ℂ) • (1 : DiracMatrix) := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [sourceSpin,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
      Matrix.mul_apply,Fin.sum_univ_four,Matrix.cons_val,Matrix.one_apply,Matrix.smul_apply,Matrix.diagonal_apply] <;> ring_nf <;> norm_num [Complex.I_sq,pow_succ]

private theorem lift_product (A B : DiracMatrix) : spinLift A*spinLift B=spinLift (A*B) := by
  ext i j
  simp only [Matrix.mul_apply,spinLift,Fintype.sum_sigma]
  have hi (k : DiracSpinorIndex) :
      (∑ x : SaturationMonoid.PhysicsCore.LowEnergy.Quantum.InternalIndex,
        (if i.2=x then A i.1 k else 0)*(if x=j.2 then B k j.1 else 0))=
      if i.2=j.2 then A i.1 k*B k j.1 else 0 := by
    rw [Finset.sum_eq_single i.2]
    · simp
    · intro x _ hxi
      simp [Ne.symm hxi]
    · simp
  simp_rw [hi]
  split_ifs <;> simp

private theorem lift_quarter : spinLift ((1/4 : ℂ) • (1 : DiracMatrix))=
    (1/4 : ℂ) • (1 : Matrix SaturationMonoid.PhysicsCore.LowEnergy.Quantum.Index _ ℂ) := by
  ext i j
  rcases i with ⟨r,x⟩
  rcases j with ⟨s,y⟩
  by_cases hrs : r=s <;> by_cases hxy : x=y <;>
    simp [spinLift,Matrix.smul_apply,hrs,hxy]

/-- Both original 252-mode blocks, including the independent-dual signs, retain the exact quarter square. -/
theorem original_full_spin_square (a : Fin 7) : full a*full a=(1/4 : ℂ) • (1 : Matrix Mode Mode ℂ) := by
  have hp : primal a*primal a=(1/4 : ℂ) • (1 : Matrix SaturationMonoid.PhysicsCore.LowEnergy.Quantum.Index _ ℂ) := by
    rw [primal,lift_product,original_dirac_spin_square,lift_quarter]
  have hd : (primal a).map (starRingEnd ℂ)*(primal a).map (starRingEnd ℂ)=
      (1/4 : ℂ) • (1 : Matrix SaturationMonoid.PhysicsCore.LowEnergy.Quantum.Index _ ℂ) := by
    rw [←Matrix.map_mul,hp]
    ext i j
    by_cases h : i=j <;> simp [Matrix.map_apply,Matrix.smul_apply,h]
    norm_num [starRingEnd_apply,Complex.star_def]
  unfold full
  split_ifs <;>
    simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
      neg_mul_neg,hp,hd]
  all_goals
    ext i j
    cases i <;> cases j <;> simp [Matrix.fromBlocks,Matrix.smul_apply,Matrix.one_apply]

private theorem quantized_smul (c : ℂ) (A : Matrix Mode Mode ℂ) : quantized (c • A)=c • quantized A := by
  apply ContinuousLinearMap.ext
  intro psi
  exact LinearMap.congr_fun (quantizedFiber_smul c A) psi

private theorem quantized_one : quantized (1 : Matrix Mode Mode ℂ)=fiberNumber := by
  apply ContinuousLinearMap.ext
  intro psi
  apply PiLp.ext
  intro word
  rw [fiberNumber_apply]
  change SaturationMonoid.PhysicsCore.LowEnergy.Fermion.quantize (Matrix.diagonal (fun _ : Mode => (1 : ℂ)))
    (fiberCoordinates psi) word=(word.card : ℂ)*(psi word)
  have h := SaturationMonoid.PhysicsCore.LowEnergy.Fermion.occupationCharge_original_quantize (fun _ : Mode => (1 : ℂ))
  exact (congrFun (LinearMap.congr_fun h (fiberCoordinates psi)) word).trans
    (SourceFockRaising.total_apply (fiberCoordinates psi) word)

/-- Only the one-body contraction reduces to Number; the original quartic kernel remains. -/
theorem original_one_body_number : oneBody=(-33/16 : ℂ) • fiberNumber := by
  unfold oneBody
  simp_rw [original_full_spin_square,quantized_smul,quantized_one,smul_smul]
  norm_num [residualWeight,Fin.sum_univ_succ]
  module

/-- The full original coframe action consumes the contracted one-body coefficient together with its true multi-particle kernel. -/
theorem original_coframe_contracted (f : QuantumTest) (z : SourceCoordinateSlice) :
    coframeAction f z=SourceCoframeCovariantAction.covariantKinetic f z+
      (inverseVolume z : ℂ) • (((-33/16 : ℂ) • fiberNumber+quartic) (f z))+
        multiply volumePotential volumePotential_smooth f z := by
  simpa only [original_one_body_number] using original_coframe_normal_action f z

end LowEnergy.SourceCoframeSpinContraction
