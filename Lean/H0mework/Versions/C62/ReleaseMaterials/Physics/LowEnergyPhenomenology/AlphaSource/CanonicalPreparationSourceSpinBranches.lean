import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSpinBasis

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumCoframeSpinReduction
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open DiracCliffordRepresentation DiracExteriorMatterAction PointwiseDiracSpinConnectionLift
open Stage9C.Material.SpinPair StageNineLorentzConnectionVariation
open PreparationVacuumGravityLegendreSource PreparationVacuumCoframeLegendreSource
open PreparationVacuumCoframeQuantumCurrent PreparationVacuumSourceFieldFamily
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open PreparationVacuumMixedFieldReturn GaussHistoryHilbert GaussQuantumMultiplier
open scoped Topology BigOperators Matrix
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _

private def sourceCoordinateMap (a : Fin 8) : DiracMatrix→ₗ[ℂ] ℂ where
  toFun A:=sourceSpinCoordinates A a
  map_add' A B:=by
    cases a using Fin.cases with
    | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_add,add_div]
    | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_add,Matrix.trace_add]
  map_smul' c A:=by
    cases a using Fin.cases with
    | zero=>simp only [sourceSpinCoordinates,Fin.cases_zero,Matrix.trace_smul,smul_eq_mul,RingHom.id_apply];ring
    | succ a=>simp only [sourceSpinCoordinates,Fin.cases_succ,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,RingHom.id_apply]

def sourceSpinWord (b : Fin 4) (p : Fin 6) : DiracMatrix:=
  (-Complex.I) • (diracGammaZero*(diracGamma b*
    (diracGamma (lorentzBivectorFirst p)*diracGamma (lorentzBivectorSecond p))))

def sourceSpinWordWeight (z : SourceCoordinateSlice) (i : LorentzIndex)
    (mu b : Fin 4) (p : Fin 6) : ℝ:=
  lapse*(sourceGaussCoframe z)⁻¹ mu b*
    loweredLorentzConnectionCoefficient (lorentzSkewConnectionOfBivectorOneForm (sourceConnectionBasis i)) mu p/2

theorem sourceSpinWords_generated (z : SourceCoordinateSlice) (i : LorentzIndex) :
    sourceGaussSpinClifford z i=∑mu : Fin 4,∑p : Fin 6,∑b : Fin 4,
      (sourceSpinWordWeight z i mu b p:ℂ) • sourceSpinWord b p:=by
  simp only [sourceGaussSpinClifford,sourceSpinGamma,inverseCoframeDiracGamma,diracSpinConnectionLift,
    Finset.sum_mul,Finset.mul_sum,Matrix.smul_mul,Matrix.mul_smul,Finset.smul_sum,smul_smul,
    sourceSpinWordWeight,sourceSpinWord,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro mu _
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

private theorem sourceSpinWord_phase (b : Fin 4) (p : Fin 6) (a : Fin 8) :
    (if a.val<4 then (sourceSpinCoordinates (sourceSpinWord b p) a).re
      else (sourceSpinCoordinates (sourceSpinWord b p) a).im)=0:=by
  cases a using Fin.cases with
  | zero=>
    simp only [sourceSpinCoordinates,Fin.cases_zero,Fin.val_zero]
    fin_cases b <;> fin_cases p <;>
      norm_num [sourceSpinWord,lorentzBivectorFirst,lorentzBivectorSecond,diracGamma,diracGammaZero,
        diracGammaOne,diracGammaTwo,diracGammaThree,Matrix.trace,Matrix.mul_apply,Matrix.smul_apply,
        Fin.sum_univ_four,Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Fin.coe_ofNat_eq_mod,Nat.reduceMod]
  | succ a=>
    simp only [sourceSpinCoordinates,Fin.cases_succ,Fin.val_succ]
    fin_cases b <;> fin_cases p <;> fin_cases a <;>
      norm_num [sourceSpinWord,GaussCoframeSpin.sourceSpin,lorentzBivectorFirst,lorentzBivectorSecond,
        diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,diracGammaFive,
        Matrix.trace,Matrix.mul_apply,Matrix.smul_apply,Matrix.diagonal,Fin.sum_univ_four,
        Matrix.cons_val,Matrix.cons_val_two,Matrix.cons_val_three,Fin.coe_ofNat_eq_mod,Nat.reduceMod]

theorem sourceGaussSpinCoordinates_phase (z : SourceCoordinateSlice) (i : LorentzIndex) (a : Fin 8) :
    (if a.val<4 then (sourceGaussSpinCoordinates z i a).re
      else (sourceGaussSpinCoordinates z i a).im)=0:=by
  change (if a.val<4 then (sourceCoordinateMap a (sourceGaussSpinClifford z i)).re
    else (sourceCoordinateMap a (sourceGaussSpinClifford z i)).im)=0
  rw [sourceSpinWords_generated]
  simp only [map_sum,map_smul,smul_eq_mul,RingHom.id_apply]
  by_cases phase : a.val<4
  · simp only [phase,ite_true,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,sub_zero]
    have zero (b : Fin 4) (p : Fin 6) : (sourceSpinCoordinates (sourceSpinWord b p) a).re=0:=by
      simpa only [phase,ite_true] using sourceSpinWord_phase b p a
    simp only [sourceCoordinateMap,LinearMap.coe_mk,AddHom.coe_mk,zero,mul_zero,Finset.sum_const_zero]
  · simp only [phase,ite_false,Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero]
    have zero (b : Fin 4) (p : Fin 6) : (sourceSpinCoordinates (sourceSpinWord b p) a).im=0:=by
      simpa only [phase,ite_false] using sourceSpinWord_phase b p a
    simp only [sourceCoordinateMap,LinearMap.coe_mk,AddHom.coe_mk,zero,mul_zero,Finset.sum_const_zero]

def sourceGaussRealSpinCoefficient (z : SourceCoordinateSlice) (i : LorentzIndex) (a : Fin 8) : ℝ:=
  if a.val<4 then (sourceGaussSpinCoordinates z i a).im else (sourceGaussSpinCoordinates z i a).re

def sourceSpinPhase (a : Fin 8) : ℂ:=if a.val<4 then Complex.I else 1

theorem sourceGaussSpinCoordinates_real (z : SourceCoordinateSlice) (i : LorentzIndex) (a : Fin 8) :
    sourceGaussSpinCoordinates z i a=sourceSpinPhase a*(sourceGaussRealSpinCoefficient z i a:ℂ):=by
  have zero:=sourceGaussSpinCoordinates_phase z i a
  by_cases phase : a.val<4
  · simp only [sourceSpinPhase,sourceGaussRealSpinCoefficient,phase,ite_true] at zero ⊢
    apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero,zero_add]
    · exact zero
  · simp only [sourceSpinPhase,sourceGaussRealSpinCoefficient,phase,ite_false,one_mul] at zero ⊢
    apply Complex.ext
    · rfl
    · exact zero

-- Imaginary identity emits total Number; the remaining slots are the original seven currents.
def sourceSpinEmittedBasis (a : Fin 8) : Matrix Mode Mode ℂ:=
  Fin.cases (Complex.I • (1:Matrix Mode Mode ℂ))
    (fun b=>sourceSpinPhase b.succ • GaussCoframeSpin.full b) a

theorem sourceSpinEmittedBasis_original (a : Fin 8) :
    sourceSpinEmittedBasis a=SourceRealScalarFock.branches
      (sourceSpinPhase a • sourceFullSpinBasis a):=by
  cases a using Fin.cases with
  | zero=>
    have one : sourceFullSpinBasis 0=(1:Matrix Quantum.Index Quantum.Index ℂ):=by
      rw [sourceFullSpinBasis,sourceSpinBasis,Fin.cases_zero,←GaussCoframeSpin.spinLift_source]
      have mother : diracMatrixMatterAction (1:DiracMatrix)=(1:YangMills.FullPairing.Mother):=by
        apply LinearMap.ext
        intro v
        funext a
        simp [diracMatrixMatterAction,Matrix.one_apply]
      rw [mother,map_one]
    simp only [sourceSpinEmittedBasis,Fin.cases_zero,sourceSpinPhase,Fin.val_zero,
      show (0:ℕ)<4 by decide,ite_true,one]
    ext r s
    cases r <;> cases s <;> simp [SourceRealScalarFock.branches,Matrix.smul_apply,Matrix.one_apply]
    all_goals split_ifs <;> norm_num
  | succ b=>
    have index : b.succ.val<4↔b.val<3:=by simp only [Fin.val_succ];omega
    by_cases boost : b.val<3
    · have cut : b.succ.val<4:=index.mpr boost
      simp only [sourceSpinEmittedBasis,Fin.cases_succ,sourceSpinPhase,cut,ite_true,
        sourceFullSpinBasis,sourceSpinBasis,GaussCoframeSpin.full,boost,GaussCoframeSpin.primal]
      ext r s
      cases r <;> cases s <;>
        simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply]
    · have cut : ¬b.succ.val<4:=fun h=>boost (index.mp h)
      simp only [sourceSpinEmittedBasis,Fin.cases_succ,sourceSpinPhase,cut,ite_false,one_smul,
        sourceFullSpinBasis,sourceSpinBasis,GaussCoframeSpin.full,boost,GaussCoframeSpin.primal]
      rfl

private def sourceBranchesLinear : Matrix Quantum.Index Quantum.Index ℂ→ₗ[ℝ] Matrix Mode Mode ℂ where
  toFun:=SourceRealScalarFock.branches
  map_add' A B:=by
    ext r s
    cases r <;> cases s <;> simp [SourceRealScalarFock.branches,Matrix.map_apply,add_comm]
  map_smul' r A:=by
    ext i j
    cases i <;> cases j <;>
      simp [SourceRealScalarFock.branches,Matrix.map_apply,Matrix.smul_apply,Complex.real_smul,
        RingHom.id_apply]

theorem sourceFullSpinEmitted_generated (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    sourceSpinFullMatrix (f,z.val) (sourceState z.val) i=
      ∑a : Fin 8,sourceGaussRealSpinCoefficient z.val i a • sourceSpinEmittedBasis a:=by
  change sourceBranchesLinear (sourceSpinMatrix (f,z.val) (sourceState z.val) i)=_
  rw [sourceGaussFullSpinBasis_generated]
  have realSource : (∑a : Fin 8,sourceGaussSpinCoordinates z.val i a • sourceFullSpinBasis a)=
      ∑a : Fin 8,sourceGaussRealSpinCoefficient z.val i a •
        (sourceSpinPhase a • sourceFullSpinBasis a):=by
    apply Finset.sum_congr rfl
    intro a _
    rw [sourceGaussSpinCoordinates_real]
    simp only [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]
    congr 1
    rw [mul_comm]
    rfl
  rw [realSource,map_sum]
  simp only [map_smul,RingHom.id_apply,sourceBranchesLinear,LinearMap.coe_mk,AddHom.coe_mk,
    ←sourceSpinEmittedBasis_original]

theorem sourceSpinFiber_emitted (f : Field289) (z : physicalChart) (i : LorentzIndex) :
    sourceSpinFiber (f,z.val) (sourceState z.val) i=
      ∑a : Fin 8,(sourceGaussRealSpinCoefficient z.val i a:ℂ) • quantized (sourceSpinEmittedBasis a):=by
  rw [sourceSpinFiber,sourceFullSpinEmitted_generated]
  change quantizer (∑a : Fin 8,sourceGaussRealSpinCoefficient z.val i a • sourceSpinEmittedBasis a)=_
  simp only [map_sum,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul]
  rfl

private theorem sourceQuantizedIdentity : quantized (1:Matrix Mode Mode ℂ)=fiberNumber:=by
  apply ContinuousLinearMap.ext
  intro v
  apply PiLp.ext
  intro word
  rw [fiberNumber_apply]
  change Fermion.quantize (Matrix.diagonal (fun _ : Mode=>(1:ℂ))) (fiberCoordinates v) word=
    (word.card:ℂ)*v word
  have original:=Fermion.occupationCharge_original_quantize (fun _ : Mode=>(1:ℂ))
  convert! (congrFun (LinearMap.congr_fun original (fiberCoordinates v)) word).trans
    (SourceFockRaising.total_apply (fiberCoordinates v) word) using 1
  have decisions : (inferInstance:DecidableEq Mode)=
      @LinearOrder.toDecidableEq Mode SourceRealScalarFock.branchOrder:=Subsingleton.elim _ _
  exact congrArg (fun d : DecidableEq Mode=>
    (Fermion.quantize (@Matrix.diagonal Mode ℂ d _ (fun _ : Mode=>(1:ℂ))))
      (fiberCoordinates v) word) decisions

theorem sourceSpinIdentity_number : quantized (sourceSpinEmittedBasis 0)=Complex.I • fiberNumber:=by
  change quantizer (Complex.I • (1:Matrix Mode Mode ℂ))=Complex.I • fiberNumber
  rw [map_smul]
  exact congrArg (fun A=>Complex.I • A) sourceQuantizedIdentity

end LowEnergy.PreparationVacuumCoframeSpinReduction
