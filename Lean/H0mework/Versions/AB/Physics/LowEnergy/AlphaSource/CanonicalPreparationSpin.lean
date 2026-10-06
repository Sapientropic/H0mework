import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationAction
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalGradedCharge
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCorrection

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.CanonicalPreparationSpin
open SaturationMonoid.PhysicsCore
open DiracCliffordRepresentation DiracExteriorMatterAction
open SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open GaussCoreHilbert GaussDensityCore GaussHistoryHilbert GaussQuantumMultiplier
open CanonicalPreparationCore CanonicalPreparationCreation CanonicalPreparationMomentum
open CanonicalPreparationCorrection
open GaussComposite.SourceGraph CanonicalGradedCharge
open scoped ContDiff Distributions Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _
local instance : DecidableEq Mode := Classical.decEq _
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

@[simp] private theorem vec7_five {α : Type*} (a b c d e f g : α) :
    (![a,b,c,d,e,f,g] : Fin 7 → α) 5=f := rfl
@[simp] private theorem vec7_six {α : Type*} (a b c d e f g : α) :
    (![a,b,c,d,e,f,g] : Fin 7 → α) 6=g := rfl

private theorem anti_square (A B : DiracMatrix) (anti : A*B+B*A=0) :
    (A*B)*(A*B)=-(A*A)*(B*B) := by
  have swap : B*A=-(A*B) := by
    apply eq_neg_of_add_eq_zero_left
    simpa only [add_comm] using anti
  calc
    _ = A*((B*A)*B) := by simp only [mul_assoc]
    _ = _ := by rw [swap]; noncomm_ring

theorem sourceSpin_square (a : Fin 7) :
    GaussCoframeSpin.sourceSpin a*GaussCoframeSpin.sourceSpin a=(1/4 : ℂ) • (1 : DiracMatrix) := by
  fin_cases a
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaOne))*((1/2 : ℂ) •
      (diracGammaZero*diracGammaOne))=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ diracGammaZeroOne_anticommute]
    norm_num
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaTwo))*((1/2 : ℂ) •
      (diracGammaZero*diracGammaTwo))=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ diracGammaZeroTwo_anticommute]
    norm_num
  · change ((1/2 : ℂ) • (diracGammaZero*diracGammaThree))*((1/2 : ℂ) •
      (diracGammaZero*diracGammaThree))=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ diracGammaZeroThree_anticommute]
    norm_num
  · change ((Complex.I/2) • (diracGammaTwo*diracGammaThree))*((Complex.I/2) •
      (diracGammaTwo*diracGammaThree))=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ diracGammaTwoThree_anticommute]
    norm_num [div_mul_div_comm]
  · change ((Complex.I/2) • (diracGammaThree*diracGammaOne))*((Complex.I/2) •
      (diracGammaThree*diracGammaOne))=_
    have anti := diracGammaOneThree_anticommute
    rw [add_comm] at anti
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ anti]
    norm_num [div_mul_div_comm]
  · change ((Complex.I/2) • (diracGammaOne*diracGammaTwo))*((Complex.I/2) •
      (diracGammaOne*diracGammaTwo))=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,anti_square _ _ diracGammaOneTwo_anticommute]
    norm_num [div_mul_div_comm]
  · change ((-1/2 : ℂ) • diracGammaFive)*((-1/2 : ℂ) • diracGammaFive)=_
    rw [smul_mul_assoc,mul_smul_comm,smul_smul,diracGammaFive_sq]
    norm_num

theorem primal_square (a : Fin 7) :
    GaussCoframeSpin.primal a*GaussCoframeSpin.primal a=(1/4 : ℂ) • 1 := by
  unfold GaussCoframeSpin.primal
  rw [←GaussCoframeSpin.spinLift_source,←LowEnergy.Quantum.matrix_composition,
    ←SU7ExteriorBreakingYukawa.diracMatrixMatterAction_mul,sourceSpin_square]
  have identity : diracMatrixMatterAction ((1/4 : ℂ) • (1 : DiracMatrix))=
      (1/4 : ℂ) • (1 : Module.End ℂ DiracExteriorMatterCarrier) := by
    apply LinearMap.ext
    intro f
    funext i
    simp [diracMatrixMatterAction,Matrix.smul_apply,Matrix.one_apply]
  rw [identity,map_smul,map_one]

theorem full_square (a : Fin 7) :
    GaussCoframeSpin.full a*GaussCoframeSpin.full a=(1/4 : ℂ) • 1 := by
  have dual : (GaussCoframeSpin.primal a).map (starRingEnd ℂ)*
      (GaussCoframeSpin.primal a).map (starRingEnd ℂ)=(1/4 : ℂ) • 1 := by
    rw [←Matrix.map_mul,primal_square]
    ext i j
    by_cases h : i=j <;> simp [Matrix.map_apply,Matrix.smul_apply,h]
    exact map_ofNat (starRingEnd ℂ) 4
  unfold GaussCoframeSpin.full
  rw [Matrix.fromBlocks_multiply]
  simp only [zero_mul,mul_zero,add_zero,zero_add,primal_square]
  by_cases h : a.val<3
  · simp only [if_pos h,dual]
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]
  · simp only [if_neg h,neg_mul,mul_neg,neg_neg,dual]
    ext i j
    cases i <;> cases j <;> simp [Matrix.one_apply]

theorem seed_current_square (a : Fin 7) :
    quantized (GaussCoframeSpin.full a) (quantized (GaussCoframeSpin.full a)
      CanonicalCompletedSector.seed)=(1/4 : ℂ) • CanonicalCompletedSector.seed := by
  change quantized (GaussCoframeSpin.full a) (quantized (GaussCoframeSpin.full a)
      (oneParticleFiber CanonicalCompletedSector.seedCoordinates))=
    (1/4 : ℂ) • oneParticleFiber CanonicalCompletedSector.seedCoordinates
  rw [quantized_product_oneParticle,full_square,quantized_oneParticle,Matrix.smul_mulVec,
    Matrix.one_mulVec]
  apply fiberCoordinates.injective
  simp only [oneParticleFiber,map_smul,LinearEquiv.apply_symm_apply]
  funext word
  change (∑ i : Mode, ((1/4 : ℂ)*CanonicalCompletedSector.seedCoordinates i)*
      QuantizationCheck.Fermion.occupationBasis {i} word)=
    (1/4 : ℂ)*(∑ i : Mode, CanonicalCompletedSector.seedCoordinates i*
      QuantizationCheck.Fermion.occupationBasis {i} word)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem number_seed (f : ScalarTest) : GaussCoframeForm.number (seedSection f)=seedSection f := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [GaussCoframeForm.number_apply]
  change (word.card : ℂ)*(f z*CanonicalCompletedSector.seed word)=f z*CanonicalCompletedSector.seed word
  by_cases h : word.card=1
  · rw [h]
    simp
  · rw [seed_zero_off_one word h]
    simp

theorem numberShift_seed (f : ScalarTest) :
    GaussCoframeForm.numberShift (seedSection f)=
      GaussNativeForm.multiply GaussCoframeForm.numberCoefficient
        GaussCoframeForm.numberCoefficient_smooth (seedSection f) := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  simp only [GaussCoframeForm.numberShift,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.comp_apply]
  change (1/2 : ℂ)*
    (GaussCoframeForm.number (GaussNativeForm.multiply GaussCoframeForm.numberCoefficient
        GaussCoframeForm.numberCoefficient_smooth (seedSection f)) z word+
      (GaussCoframeForm.numberCoefficient z : ℂ)*GaussCoframeForm.number (seedSection f) z word)=_
  rw [GaussCoframeForm.number_apply,number_seed]
  change (1/2 : ℂ)*((word.card : ℂ)*((GaussCoframeForm.numberCoefficient z : ℂ)*
    (f z*CanonicalCompletedSector.seed word))+
    (GaussCoframeForm.numberCoefficient z : ℂ)*(f z*CanonicalCompletedSector.seed word))=_
  by_cases h : word.card=1
  · rw [h]
    simp only [Nat.cast_one]
    change (1/2 : ℂ)*(1*((GaussCoframeForm.numberCoefficient z : ℂ)*(f z*CanonicalCompletedSector.seed word))+
      (GaussCoframeForm.numberCoefficient z : ℂ)*(f z*CanonicalCompletedSector.seed word))=
        (GaussCoframeForm.numberCoefficient z : ℂ)*(f z*CanonicalCompletedSector.seed word)
    ring
  · change _=(GaussCoframeForm.numberCoefficient z : ℂ)*(f z*CanonicalCompletedSector.seed word)
    rw [seed_zero_off_one word h]
    simp

theorem spinSquare_seed (a : Fin 7) (f : ScalarTest) :
    GaussCoframeForm.spinSquare a (seedSection f)=
      ((GaussCoframeForm.spinWeight a : ℂ)/4) •
        GaussNativeForm.multiply GaussCoframeForm.inverseVolume
          GaussCoframeForm.inverseVolume_smooth (seedSection f) := by
  apply DFunLike.ext
  intro z
  change (GaussCoframeForm.spinWeight a : ℂ) •
      quantized (GaussCoframeSpin.full a)
        ((GaussCoframeForm.inverseVolume z : ℂ) •
          quantized (GaussCoframeSpin.full a) (f z • CanonicalCompletedSector.seed))=
    ((GaussCoframeForm.spinWeight a : ℂ)/4) •
      ((GaussCoframeForm.inverseVolume z : ℂ) • (f z • CanonicalCompletedSector.seed))
  rw [map_smul,map_smul,map_smul,seed_current_square]
  simp only [smul_smul]
  module

theorem spinWeight_total : (∑ a : Fin 7, GaussCoframeForm.spinWeight a/4)=-(9/8 : ℝ) := by
  norm_num [Fin.sum_univ_seven,GaussCoframeForm.spinWeight]

theorem spinSquares_seed (f : ScalarTest) :
    (∑ a : Fin 7, GaussCoframeForm.spinSquare a (seedSection f))=
      (-(9/8) : ℂ) • GaussNativeForm.multiply GaussCoframeForm.inverseVolume
        GaussCoframeForm.inverseVolume_smooth (seedSection f) := by
  have total : (∑ a : Fin 7, (GaussCoframeForm.spinWeight a : ℂ)/4)=-(9/8 : ℂ) := by
    have lifted := congrArg (fun r : ℝ => (r : ℂ)) spinWeight_total
    simpa only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using lifted
  simp only [spinSquare_seed,←Finset.sum_smul,total]

private theorem vacuum_zero (word : Occupation) (nonempty : word≠∅) : vacuumFiber word=0 := by
  rw [vacuumFiber_single]
  simp [EuclideanSpace.single,nonempty]

theorem numberShift_vacuum (f : ScalarTest) : GaussCoframeForm.numberShift (vacuumSection f)=0 := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  simp only [GaussCoframeForm.numberShift,LinearMap.smul_apply,LinearMap.add_apply,
    LinearMap.comp_apply]
  change (1/2 : ℂ)*
    (GaussCoframeForm.number (GaussNativeForm.multiply GaussCoframeForm.numberCoefficient
        GaussCoframeForm.numberCoefficient_smooth (vacuumSection f)) z word+
      (GaussCoframeForm.numberCoefficient z : ℂ)*GaussCoframeForm.number (vacuumSection f) z word)=0
  rw [GaussCoframeForm.number_apply,GaussCoframeForm.number_apply]
  change (1/2 : ℂ)*((word.card : ℂ)*((GaussCoframeForm.numberCoefficient z : ℂ)*(f z*vacuumFiber word))+
    (GaussCoframeForm.numberCoefficient z : ℂ)*((word.card : ℂ)*(f z*vacuumFiber word)))=0
  by_cases h : word=∅
  · subst word
    simp
  · rw [vacuum_zero word h]
    simp

private def realCore (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) : ScalarTest →ₗ[ℂ] ScalarTest :=
  GaussDensityCore.multiply (fun z => (c z : ℂ))
    (fun z => Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (smooth z))

private theorem real_created (c : SourceCoordinateSlice → ℝ)
    (smooth : ∀ z : physicalChart, ContDiffAt ℝ ∞ c z.val) (f : ScalarTest) :
    GaussNativeForm.multiply c smooth (createdCore f)=createdCore (realCore c smooth f) := by
  apply DFunLike.ext
  intro z
  change (c z : ℂ) • ((numberRaise z*f z) • CanonicalCompletedSector.seed)=
    (numberRaise z*((c z : ℂ)*f z)) • CanonicalCompletedSector.seed
  simp only [smul_smul]
  congr 1
  ring

def coframePotential (z : SourceCoordinateSlice) : ℝ :=
  GaussCoframeForm.volumePotential z-(15/16 : ℝ)*GaussCoframeForm.inverseVolume z

theorem coframePotential_smooth (z : physicalChart) :
    ContDiffAt ℝ ∞ coframePotential z.val :=
  (GaussCoframeForm.volumePotential_smooth z).sub
    (contDiffAt_const.mul (GaussCoframeForm.inverseVolume_smooth z))

def potentialCore : ScalarTest →ₗ[ℂ] ScalarTest := realCore coframePotential coframePotential_smooth

private theorem zero_order_core (f : ScalarTest) :
    correctionPotential f+
      (-(9/8) : ℂ) • realCore GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth f+
      realCore GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth f+
      realCore GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth f=
      potentialCore f := by
  apply DFunLike.ext
  intro z
  change (((21/16 : ℝ)*GaussCoframeForm.inverseVolume z : ℝ) : ℂ)*f z+
    (-(9/8) : ℂ)*((GaussCoframeForm.inverseVolume z : ℂ)*f z)+
    (GaussCoframeForm.numberCoefficient z : ℂ)*f z+
    (GaussCoframeForm.volumePotential z : ℂ)*f z=(coframePotential z : ℂ)*f z
  unfold GaussCoframeForm.numberCoefficient coframePotential
  push_cast
  ring

theorem coframeAction_created (f : ScalarTest) :
    GaussCoframeForm.coframeAction (createdCore f)=
      createdCore (coframeKinetic 0 f+potentialCore f)+GaussCoframeForm.currentAction (createdCore f) := by
  have spin := spinSquares_seed (numberRaiseCore f)
  have number := numberShift_seed (numberRaiseCore f)
  change (∑ a : Fin 7, GaussCoframeForm.spinSquare a (createdCore f))=
    (-(9/8) : ℂ) • GaussNativeForm.multiply GaussCoframeForm.inverseVolume
      GaussCoframeForm.inverseVolume_smooth (createdCore f) at spin
  change GaussCoframeForm.numberShift (createdCore f)=
    GaussNativeForm.multiply GaussCoframeForm.numberCoefficient
      GaussCoframeForm.numberCoefficient_smooth (createdCore f) at number
  simp only [GaussCoframeForm.coframeAction,LinearMap.add_apply,LinearMap.sum_apply]
  rw [kinetic_creation_potential,spin,number,real_created,real_created,real_created]
  have zeroOrder := congrArg createdCore (zero_order_core f)
  simp only [createdCore,map_add,map_smul] at zeroOrder ⊢
  rw [←zeroOrder]
  abel

theorem fullAction_created (f : ScalarTest) :
    GaussFullHamiltonian.fullAction (createdCore f)=
      createdCore (coframeKinetic 0 f+potentialCore f)+GaussCoframeForm.currentAction (createdCore f)+
      GaussNativeForm.nativeAction (createdCore f)+GaussMatterCore.matterAction (createdCore f)+
      GaussYukawaOperator.originalAction (createdCore f) := by
  simp only [GaussFullHamiltonian.fullAction,GaussDiagonalHistory.diagonalAction,LinearMap.add_apply]
  rw [coframeAction_created]
  abel

end LowEnergy.CanonicalPreparationSpin
