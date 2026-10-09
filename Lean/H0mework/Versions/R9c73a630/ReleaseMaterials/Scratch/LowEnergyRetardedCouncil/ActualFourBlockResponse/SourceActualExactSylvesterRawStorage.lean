import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualSylvesterCore

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualExactSylvesterRawStorage
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceScalarPairedTransport SourceMixedNativeReturn SourceRetardedGraph SourceCutoffDilationWard
open Lean Meta Elab Term
open ActualTwoResolventCascade ActualSylvesterCore
open scoped Matrix InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

elab "paid_raw_source_Q_energy%" : term => do
  mkConstWithFreshMVarLevels (Name.str (Name.str (Name.str
    (Name.num `_private.H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockResponse.SourceActualTwoResolventCascade 0) "LowEnergy")
    "ActualTwoResolventCascade") "sourceQAction_energy")

private theorem source_mu_pos : 0 < sourceMu := lt_of_lt_of_le (by norm_num) source_mu_large

/-- The original all-channel smoothing, at the unaltered source damping. -/
def exactL (advanced sharp : Bool) (F : Index) (m ell : ℕ) : End :=
  sourceLCore advanced sharp F sourceMu m ell

/-- The raw form deliberately keeps only the paid source Q in its lower corner. -/
def rawStorage (advanced sharp : Bool) (F : Index) (m ell : ℕ) : Matrix (Fin 2) (Fin 2) End :=
  !![1,exactL advanced sharp F m ell;
     exactL advanced (!sharp) F m ell,(2 : ℂ) • sourceQAction sharp m ell]

def lyapunov (advanced : Bool) (F : Index) (Q : End) : End :=
  (2*(sourceMu : ℂ)) • Q-(Complex.I*(causalSign advanced : ℂ)) •
    (compressionCore F*Q-Q*compressionCore F)

/-- One complete residual, with the actual CF and same-cause paired branches. -/
def rawResidual (advanced sharp : Bool) (F : Index) (m ell : ℕ) : End :=
  lyapunov advanced F ((2 : ℂ) • sourceQAction sharp m ell)-
    literalIncrementAction (!sharp) m ell*exactL advanced sharp F m ell-
    exactL advanced (!sharp) F m ell*literalIncrementAction sharp m ell

private theorem raw_blocks {R : Type*} [Ring R] (A B D J L K Q : R) :
    -(!![B,0;J,B])*!![1,L;K,Q]-!![1,L;K,Q]*!![A,D;0,A]=
      !![-B-A,-B*L-D-L*A;-J-B*K-K*A,-J*L-B*Q-K*D-Q*A] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> noncomm_ring

private theorem damping (C L : End) (s : ℂ) :
    -((-(sourceMu : ℂ) • (1 : End)+s • C)*L)-
      L*(-(sourceMu : ℂ) • (1 : End)-s • C)=
      (2*(sourceMu : ℂ)) • L-s • (C*L-L*C) := by
  simp only [add_mul,mul_sub,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_sub]
  module

private theorem actual_exact_sylvester (advanced sharp : Bool) (F : Index) (m ell : ℕ) :
    lyapunov advanced F (exactL advanced sharp F m ell)=literalIncrementAction sharp m ell := by
  apply LinearMap.ext
  intro f
  have h := actual_source_core_sylvester advanced sharp F sourceMu source_mu_pos m ell f
  cases advanced <;>
    simpa only [lyapunov,exactL,causalSign,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,
      Bool.false_eq_true,ite_false,ite_true,Complex.ofReal_neg,Complex.ofReal_one] using h

private theorem damping_source (advanced : Bool) (F : Index) (Q : End) :
    -sourceADual advanced F*Q-Q*sourceA advanced F=lyapunov advanced F Q := by
  rw [neg_mul]
  exact damping (compressionCore F) Q (Complex.I*(causalSign advanced : ℂ))

attribute [local irreducible] exactL sourceQAction compressionCore literalIncrementAction

/-- Exact source block cancellation. No positivity of the raw storage or residual is assumed. -/
theorem actual_exact_source_raw_storage_blocks (advanced sharp : Bool) (m ell : ℕ) (F : Index) :
    -(sourceCascadeDual advanced sharp m ell F)*rawStorage advanced sharp F m ell-
      rawStorage advanced sharp F m ell*sourceCascade advanced sharp m ell F=
      !![(2*(sourceMu : ℂ)) • (1 : End),0;0,rawResidual advanced sharp F m ell] := by
  unfold sourceCascadeDual sourceCascade rawStorage
  rw [raw_blocks]
  apply ActualCascadeBlockAlgebra.four_congr
  · unfold sourceADual sourceA
    module
  · calc
      _=(-sourceADual advanced F*exactL advanced sharp F m ell-
          exactL advanced sharp F m ell*sourceA advanced F)-literalIncrementAction sharp m ell := by simp only [neg_mul]; abel
      _=lyapunov advanced F (exactL advanced sharp F m ell)-literalIncrementAction sharp m ell := by
        rw [damping_source]
      _=0 := by rw [actual_exact_sylvester,sub_self]
  · calc
      _=(-sourceADual advanced F*exactL advanced (!sharp) F m ell-
          exactL advanced (!sharp) F m ell*sourceA advanced F)-literalIncrementAction (!sharp) m ell := by simp only [neg_mul]; abel
      _=lyapunov advanced F (exactL advanced (!sharp) F m ell)-literalIncrementAction (!sharp) m ell := by
        rw [damping_source]
      _=0 := by rw [actual_exact_sylvester,sub_self]
  · unfold rawResidual
    rw [←damping_source]
    simp only [neg_mul]
    abel

/-- The full own defect is retained when the residual's CF current is read at H0. -/
theorem actual_raw_lyapunov_defect (advanced : Bool) (F : Index) (Q : End) :
    lyapunov advanced F Q=(2*(sourceMu : ℂ)) • Q-
      (Complex.I*(causalSign advanced : ℂ)) • (diagonalAction*Q-Q*diagonalAction)+
      (Complex.I*(causalSign advanced : ℂ)) • (defectAction F*Q-Q*defectAction F) := by
  have hc : compressionCore F=diagonalAction-defectAction F := by unfold defectAction; abel
  rw [lyapunov,hc]
  simp only [sub_mul,mul_sub,smul_sub]
  module

/-- At the actual (0,g) initial state the raw storage reads only twice the paid source Q. -/
theorem actual_raw_initial_value (advanced sharp : Bool) (F : Index) (m ell : ℕ) (g : QuantumTest) :
    (sourcePair g ((rawStorage advanced sharp F m ell 1 1) g)).re=2*sourceQ sharp m ell g := by
  change (sourcePair g (((2 : ℂ) • sourceQAction sharp m ell) g)).re=_
  rw [LinearMap.smul_apply]
  have he : sourcePair g ((2 : ℂ) • sourceQAction sharp m ell g)=
      (2 : ℂ)*sourcePair g (sourceQAction sharp m ell g) := by
    simp only [sourcePair,map_smul,inner_smul_right]
  rw [he]
  simp only [Complex.mul_re,Complex.re_ofNat,Complex.im_ofNat,zero_mul,sub_zero]
  rw [(paid_raw_source_Q_energy%)]

/-- Fixed-source initial payment precedes all compressions and both causes. -/
theorem actual_raw_initial_tail (sharp : Bool) (g : QuantumTest) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ F : Index, ∀ advanced : Bool,
        (sourcePair g ((rawStorage advanced sharp F m ell 1 1) g)).re ≤ ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_initial_storage_tail sharp g (ε/2) (by positivity)
  refine ⟨N,fun m hm ell hell F advanced => ?_⟩
  rw [actual_raw_initial_value]
  have h := hN m hm ell hell
  unfold initialStorage at h
  nlinarith only [h,sq_nonneg ‖embed (ActualTwoResolventCascade.sourceL sharp m ell g)‖]

end LowEnergy.ActualExactSylvesterRawStorage
