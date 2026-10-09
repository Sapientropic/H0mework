import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpinClifford

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeSpinReduction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open StageNineLorentzConnectionVariation PreparationVacuumGravityLegendreSource
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumCoframeLegendreSource
open SourceQuantumGaugeSliceCoordinates GaussHistoryHilbert PreparationVacuumMixedFieldReturn
open PreparationVacuumSourceFieldFamily SourceQuantumConfigurationHilbert
open scoped Topology BigOperators Matrix

-- These are the fixed source Clifford coordinates, including the identity slot.
def sourceSpinBasis (a : Fin 8) : DiracMatrix:=
  Fin.cases 1 (fun b=>GaussCoframeSpin.sourceSpin b) a

def sourceSpinCoordinates (A : DiracMatrix) (a : Fin 8) : ℂ:=
  Fin.cases (Matrix.trace A/4) (fun b=>Matrix.trace (GaussCoframeSpin.sourceSpin b*A)) a

def sourceSpinProjection : DiracMatrix→ₗ[ℂ] DiracMatrix where
  toFun A:=∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a
  map_add' A B:=by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    have coefficient : sourceSpinCoordinates (A+B) a=sourceSpinCoordinates A a+sourceSpinCoordinates B a:=by
      cases a using Fin.cases with
      | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_add,add_div]
      | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_add,Matrix.trace_add]
    rw [coefficient,add_smul]
  map_smul' c A:=by
    simp only [Finset.smul_sum,smul_smul,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    cases a using Fin.cases with
    | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_smul,smul_eq_mul];ring
    | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul]

private theorem sourceSpinProjection_entry_0_0 (A : DiracMatrix) :
    sourceSpinProjection A 0 0=A 0 0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 0 0=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_0_1 (A : DiracMatrix) :
    sourceSpinProjection A 0 1=A 0 1:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 0 1=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_0_2 (A : DiracMatrix) :
    sourceSpinProjection A 0 2=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 0 2=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_0_3 (A : DiracMatrix) :
    sourceSpinProjection A 0 3=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 0 3=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_1_0 (A : DiracMatrix) :
    sourceSpinProjection A 1 0=A 1 0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 1 0=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_1_1 (A : DiracMatrix) :
    sourceSpinProjection A 1 1=A 1 1:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 1 1=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_1_2 (A : DiracMatrix) :
    sourceSpinProjection A 1 2=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 1 2=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_1_3 (A : DiracMatrix) :
    sourceSpinProjection A 1 3=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 1 3=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_2_0 (A : DiracMatrix) :
    sourceSpinProjection A 2 0=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 2 0=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_2_1 (A : DiracMatrix) :
    sourceSpinProjection A 2 1=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 2 1=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_2_2 (A : DiracMatrix) :
    sourceSpinProjection A 2 2=A 2 2:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 2 2=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_2_3 (A : DiracMatrix) :
    sourceSpinProjection A 2 3=A 2 3:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 2 3=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_3_0 (A : DiracMatrix) :
    sourceSpinProjection A 3 0=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 3 0=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_3_1 (A : DiracMatrix) :
    sourceSpinProjection A 3 1=0:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 3 1=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_3_2 (A : DiracMatrix) :
    sourceSpinProjection A 3 2=A 3 2:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 3 2=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry_3_3 (A : DiracMatrix) :
    sourceSpinProjection A 3 3=A 3 3:=by
  change (∑a : Fin 8,sourceSpinCoordinates A a • sourceSpinBasis a) 3 3=_
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,Fin.sum_univ_succ,
    sourceSpinCoordinates,sourceSpinBasis,Fin.cases_zero,Fin.cases_succ,Fin.sum_univ_zero]
  simp [sourceSpinCoordinates,sourceSpinBasis,GaussCoframeSpin.sourceSpin,
    diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
    Matrix.trace,Matrix.mul_apply,Matrix.vecMul,dotProduct,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.one_apply,Matrix.diagonal,Fin.sum_univ_eight,Fin.sum_univ_seven,Fin.sum_univ_four,
    Fin.coe_ofNat_eq_mod,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Nat.reduceMod] <;>
    ring_nf <;> norm_num [Complex.I_sq,Complex.I_pow_four] <;> ring

private theorem sourceSpinProjection_entry (A : DiracMatrix) (i j : Fin 4) :
    sourceSpinProjection A i j=(if (i.val<2↔j.val<2) then A i j else 0):=by
  fin_cases i <;> fin_cases j

  · simpa using sourceSpinProjection_entry_0_0 A

  · simpa using sourceSpinProjection_entry_0_1 A

  · simpa using sourceSpinProjection_entry_0_2 A

  · simpa using sourceSpinProjection_entry_0_3 A

  · simpa using sourceSpinProjection_entry_1_0 A

  · simpa using sourceSpinProjection_entry_1_1 A

  · simpa using sourceSpinProjection_entry_1_2 A

  · simpa using sourceSpinProjection_entry_1_3 A

  · simpa using sourceSpinProjection_entry_2_0 A

  · simpa using sourceSpinProjection_entry_2_1 A

  · simpa using sourceSpinProjection_entry_2_2 A

  · simpa using sourceSpinProjection_entry_2_3 A

  · simpa using sourceSpinProjection_entry_3_0 A

  · simpa using sourceSpinProjection_entry_3_1 A

  · simpa using sourceSpinProjection_entry_3_2 A

  · simpa using sourceSpinProjection_entry_3_3 A

private theorem sourceSpinProjection_fixed (A : DiracMatrix)
    (commute : diracGammaFive*A=A*diracGammaFive) : sourceSpinProjection A=A:=by
  ext i j
  rw [sourceSpinProjection_entry]
  have entry:=congrFun (congrFun commute i) j
  fin_cases i <;> fin_cases j <;>
    simp [diracGammaFive,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_four] at entry ⊢
  all_goals first | linear_combination (1/2:ℂ)*entry | linear_combination (-1/2:ℂ)*entry

private theorem sourceInverseGamma_anticommutator (e : LorentzianCoframe) (mu : Fin 4) :
    diracGammaFive*inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu=
      -(inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu*diracGammaFive):=by
  have anti (b : Fin 4) : diracGammaFive*diracGamma b= -(diracGamma b*diracGammaFive):=
    eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes b)
  simp only [inverseCoframeDiracGamma,Finset.mul_sum,Finset.sum_mul,
    Matrix.mul_smul,Matrix.smul_mul,anti,smul_neg,Finset.sum_neg_distrib]

private theorem sourceSpinGamma_commutator (e : LorentzianCoframe) (i : LorentzIndex) :
    diracGammaFive*(diracGammaZero*sourceSpinGamma e i)=
      (diracGammaZero*sourceSpinGamma e i)*diracGammaFive:=by
  have antiZero : diracGammaFive*diracGammaZero= -(diracGammaZero*diracGammaFive):=
    eq_neg_of_add_eq_zero_left (diracGammaFive_anticommutes 0)
  simp only [sourceSpinGamma,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro mu _
  let G:=inverseCoframeDiracGamma {coframe:=e,derivative:=0} mu
  let S:=diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (sourceConnectionBasis i)) mu
  change diracGammaFive*(diracGammaZero*(G*S))=(diracGammaZero*(G*S))*diracGammaFive
  have anti : diracGammaFive*G= -(G*diracGammaFive):=sourceInverseGamma_anticommutator e mu
  have spin : S*diracGammaFive=diracGammaFive*S:=diracSpinConnectionLift_commutes_gammaFive _ _
  rw [←mul_assoc diracGammaFive diracGammaZero (G*S),antiZero,neg_mul,
    mul_assoc diracGammaZero diracGammaFive (G*S),←mul_assoc diracGammaFive G S,
    anti,neg_mul,mul_neg,neg_neg,mul_assoc G diracGammaFive S,←spin]
  simp only [mul_assoc]

theorem sourceSpinProjection_generated (e : LorentzianCoframe) (i : LorentzIndex) :
    sourceSpinProjection (diracGammaZero*sourceSpinGamma e i)=diracGammaZero*sourceSpinGamma e i:=
  sourceSpinProjection_fixed _ (sourceSpinGamma_commutator e i)

theorem sourceGaussSpinProjection_generated (z : SourceCoordinateSlice) (i : LorentzIndex) :
    sourceSpinProjection (sourceGaussSpinClifford z i)=sourceGaussSpinClifford z i:=by
  rw [sourceGaussSpinClifford,map_smul,sourceSpinProjection_generated]

def sourceGaussSpinCoordinates (z : SourceCoordinateSlice) (i : LorentzIndex) (a : Fin 8) : ℂ:=
  sourceSpinCoordinates (sourceGaussSpinClifford z i) a

theorem sourceGaussSpinBasis_generated (z : SourceCoordinateSlice) (i : LorentzIndex) :
    sourceGaussSpinClifford z i=∑a : Fin 8,sourceGaussSpinCoordinates z i a • sourceSpinBasis a:=
  (sourceGaussSpinProjection_generated z i).symm

def sourceFullSpinBasis (a : Fin 8) : Matrix Quantum.Index Quantum.Index ℂ:=
  GaussCoframeSpin.spinLift (sourceSpinBasis a)

theorem sourceGaussFullSpinBasis_generated (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    sourceSpinMatrix (f,z.val) (sourceState z.val) i=
      ∑a : Fin 8,sourceGaussSpinCoordinates z.val i a • sourceFullSpinBasis a:=by
  rw [sourceGaussSpinClifford_original,sourceGaussSpinBasis_generated]
  ext r s
  by_cases same : r.2=s.2
  · simp only [sourceFullSpinBasis,GaussCoframeSpin.spinLift,same,ite_true,Matrix.sum_apply,
      Matrix.smul_apply,smul_eq_mul]
  · simp only [sourceFullSpinBasis,GaussCoframeSpin.spinLift,same,ite_false,Matrix.sum_apply,
      Matrix.smul_apply,smul_eq_mul,mul_zero,Finset.sum_const_zero]

end LowEnergy.PreparationVacuumCoframeSpinReduction
