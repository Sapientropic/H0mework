import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationWeylZeroReplay
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCanonicalMoyal
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff PreparationActualFactor
open PreparationVacuumLowerLeaves
open scoped BigOperators

abbrev Phase := FlatConfiguration × PhysicalMomentum
abbrev Symbol := Phase → ℝ
abbrev Slot := Fin 100 × Bool
abbrev Word (r : ℕ) := Fin r → Slot

def qDirection (i : Fin 100) : Phase := (Pi.single i 1,0)
def pDirection (i : Fin 100) : Phase := (0,WithLp.toLp 2 (Pi.single i 1))

def slotDirection (s : Slot) : Phase := if s.2 then pDirection s.1 else qDirection s.1
def slotSign (s : Slot) : ℝ := if s.2 then -1 else 1
def slotSwap : Slot ≃ Slot where
  toFun s := (s.1,!s.2)
  invFun s := (s.1,!s.2)
  left_inv s := by cases s with | mk i b => cases b <;> rfl
  right_inv s := by cases s with | mk i b => cases b <;> rfl

def wordSwap (r : ℕ) : Word r ≃ Word r := Equiv.piCongrRight (fun _ => slotSwap)
def wordSign {r : ℕ} (w : Word r) : ℝ := ∏ a : Fin r, slotSign (w a)
def jet (r : ℕ) (f : Symbol) (w : Word r) (zp : Phase) : ℝ :=
  iteratedFDeriv ℝ r f zp (fun a => slotDirection (w a))

-- This is the full ordered expansion of the original 200 signed slots.
-- The r! divides repeated ordered canonical contractions exactly once.
def contraction (r : ℕ) (f g : Symbol) (zp : Phase) : ℝ :=
  ∑ w : Word r, wordSign w*jet r f w zp*jet r g (wordSwap r w) zp

def coefficient (r : ℕ) (f g : Symbol) (zp : Phase) : ℂ :=
  (Complex.I/2)^r/(r.factorial : ℂ)*(contraction r f g zp : ℂ)

def jordan (r : ℕ) (f g : Symbol) (zp : Phase) : ℂ :=
  (coefficient r f g zp+coefficient r g f zp)/2

theorem slot_count : Fintype.card Slot=200 := by simp [Slot]

theorem original_native_q_direction (i : Fin 100) :
    nativePhase (qDirection i)=(rawDirection i,0) := by
  apply Prod.ext
  · rfl
  · apply ContinuousLinearMap.ext
    intro z
    simp [nativePhase,qDirection,nativeCovector_apply]

theorem original_native_p_direction (i : Fin 100) :
    nativePhase (pDirection i)=(0,rawCovector i) := by
  simp [nativePhase,pDirection,rawCovector]

theorem wordSwap_involution (r : ℕ) (w : Word r) : wordSwap r (wordSwap r w)=w := by
  funext a
  change slotSwap (slotSwap (w a))=w a
  exact slotSwap.left_inv (w a)

theorem wordSign_swap (r : ℕ) (w : Word r) :
    wordSign (wordSwap r w)=(-1 : ℝ)^r*wordSign w := by
  have term (a : Fin r) : slotSign (wordSwap r w a)=(-1 : ℝ)*slotSign (w a) := by
    cases h : (w a).2 <;> simp [wordSwap,slotSwap,slotSign,h]
  simp only [wordSign,term,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem contraction_swap (r : ℕ) (f g : Symbol) (zp : Phase) :
    contraction r g f zp=(-1 : ℝ)^r*contraction r f g zp := by
  unfold contraction
  rw [←(wordSwap r).sum_comp]
  simp only [wordSwap_involution,wordSign_swap,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem coefficient_swap (r : ℕ) (f g : Symbol) (zp : Phase) :
    coefficient r g f zp=(-1 : ℂ)^r*coefficient r f g zp := by
  rw [coefficient,contraction_swap]
  push_cast
  unfold coefficient
  ring

theorem contraction_zero (f g : Symbol) (zp : Phase) : contraction 0 f g zp=f zp*g zp := by
  simp [contraction,wordSign,jet]

theorem coefficient_zero (f g : Symbol) (zp : Phase) :
    coefficient 0 f g zp=(f zp : ℂ)*(g zp : ℂ) := by
  simp [coefficient,contraction_zero]

theorem coefficient_conjugate (r : ℕ) (f g : Symbol) (zp : Phase) :
    star (coefficient r f g zp)=(-1 : ℂ)^r*coefficient r f g zp := by
  unfold coefficient
  simp only [Complex.star_def,map_mul,map_div₀,map_pow,map_natCast,Complex.conj_I,
    Complex.conj_ofReal,map_ofNat]
  rw [neg_div,neg_pow]
  ring

theorem coefficient_adjoint_swap (r : ℕ) (f g : Symbol) (zp : Phase) :
    star (coefficient r f g zp)=coefficient r g f zp := by
  rw [coefficient_conjugate]
  exact (coefficient_swap r f g zp).symm

theorem jordan_odd (r : ℕ) (f g : Symbol) (zp : Phase) :
    jordan (2*r+1) f g zp=0 := by
  rw [jordan,coefficient_swap]
  have parity : (-1 : ℂ)^(2*r+1)=-1 := by
    rw [pow_add,pow_mul]
    norm_num
  rw [parity]
  ring

theorem coefficient_self_odd (r : ℕ) (f : Symbol) (zp : Phase) :
    coefficient (2*r+1) f f zp=0 := by
  have zero:=jordan_odd r f f zp
  unfold jordan at zero
  linear_combination zero

def qD (i : Fin 100) (f : Symbol) (zp : Phase) : ℝ := fderiv ℝ f zp (qDirection i)
def pD (i : Fin 100) (f : Symbol) (zp : Phase) : ℝ := fderiv ℝ f zp (pDirection i)

def hessian (f : Symbol) (zp : Phase) (v w : Phase) : ℝ :=
  fderiv ℝ (fderiv ℝ f) zp v w

theorem contraction_one (f g : Symbol) (zp : Phase) :
    contraction 1 f g zp=∑ i : Fin 100,(qD i f zp*pD i g zp-pD i f zp*qD i g zp) := by
  unfold contraction
  rw [←(Equiv.funUnique (Fin 1) Slot).symm.sum_comp]
  simp only [jet,iteratedFDeriv_one_apply,wordSign,Fin.prod_univ_one]
  rw [Fintype.sum_prod_type]
  simp [slotDirection,slotSign,wordSwap,slotSwap,qD,pD,Finset.sum_add_distrib]
  ring

theorem coefficient_one (f g : Symbol) (zp : Phase) :
    coefficient 1 f g zp=Complex.I/2*
      ((∑ i : Fin 100,(qD i f zp*pD i g zp-pD i f zp*qD i g zp) : ℝ) : ℂ) := by
  simp [coefficient,contraction_one]

theorem contraction_two (f g : Symbol) (zp : Phase) :
    contraction 2 f g zp=∑ i : Fin 100,∑ k : Fin 100,
      (hessian f zp (qDirection i) (qDirection k)*hessian g zp (pDirection i) (pDirection k)-
      hessian f zp (qDirection i) (pDirection k)*hessian g zp (pDirection i) (qDirection k)-
      hessian f zp (pDirection i) (qDirection k)*hessian g zp (qDirection i) (pDirection k)+
      hessian f zp (pDirection i) (pDirection k)*hessian g zp (qDirection i) (qDirection k)) := by
  unfold contraction
  rw [←(finTwoArrowEquiv Slot).symm.sum_comp,Fintype.sum_prod_type]
  simp only [wordSign,Fin.prod_univ_two,jet,iteratedFDeriv_two_apply]
  simp only [Fintype.sum_prod_type]
  simp [finTwoArrowEquiv,wordSwap,slotSwap,slotDirection,slotSign,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,hessian]
  ring

theorem coefficient_two (f g : Symbol) (zp : Phase) :
    coefficient 2 f g zp=(-1/8 : ℂ)*(contraction 2 f g zp : ℂ) := by
  unfold coefficient
  norm_num [div_pow,Complex.I_sq]

theorem coefficient_zero_left (r : ℕ) (g : Symbol) (zp : Phase) :
    coefficient r (fun _ => 0) g zp=0 := by
  simp [coefficient,contraction,jet,iteratedFDeriv_fun_zero]

theorem coefficient_zero_right (r : ℕ) (f : Symbol) (zp : Phase) :
    coefficient r f (fun _ => 0) zp=0 := by
  rw [coefficient_swap,coefficient_zero_left,mul_zero]

end LowEnergy.PreparationVacuumCanonicalMoyal
