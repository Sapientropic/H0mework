import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineCancellationTable

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumEngineCancellation
open PreparationVacuumEngineSource PreparationVacuumEngineIdentities PreparationVacuumEngineResponse
open PreparationVacuumCanonicalMoyal
open scoped BigOperators

private abbrev originalJ := engine_const% "js"
private abbrev originalAffine := program_const% "affine"
private abbrev originalT := program_const% "applyT"
private abbrev originalSource := table_const% "sourceSeries"
private abbrev originalTrace := table_const% "traceSeries"
private abbrev originalCrossFirst := table_const% "crossFirst"
private abbrev originalCrossSecond := table_const% "crossSecond"
private abbrev originalCrossSlot := table_const% "crossSlot"

def sourceAffineResponse (k : ℕ) (equation : Option (Fin 4)) : Symbol :=
  match equation with
  | none => ∑ a : Fin 4,MvPolynomial.coeff 0
      (sourceNewestPolynomial k a*(originalSource (Fin.castAdd 9 a)).getD 0 0)
  | some _ => 0

private theorem J_response (k : ℕ) (a : Fin 4) (X : List AngularPolynomial) :
    MvPolynomial.coeff 0 ((originalJ (k+1) (sourceEngine (k+1)) a X).getD (k+1) 0)-
      MvPolynomial.coeff 0 ((originalJ (k+1) (sourceEngine k) a X).getD (k+1) 0)=
      MvPolynomial.coeff 0 (sourceNewestPolynomial k a*X.getD 0 0) := by
  have delta := sourceJordan_newest k a X X (fun _ _ => rfl)
  change (originalJ (k+1) (sourceEngine (k+1)) a X).getD (k+1) 0-
    (originalJ (k+1) (sourceEngine k) a X).getD (k+1) 0=
    sourceClockCoefficient k a 0*(X.getD (k+1) 0-X.getD (k+1) 0)+sourceNewestPolynomial k a*X.getD 0 0 at delta
  simp only [sub_self,mul_zero,zero_add] at delta
  simpa only [MvPolynomial.coeff_sub] using congrArg (MvPolynomial.coeff 0) delta

theorem sourceAffine_newest (k : ℕ) (equation : Option (Fin 4)) :
    originalAffine (k+1) (sourceEngine (k+1)) equation (Fin.last (k+1))-
      originalAffine (k+1) (sourceEngine k) equation (Fin.last (k+1))=
      sourceAffineResponse k equation := by
  cases equation with
  | none =>
    program_unfold "affine"
    unfold sourceAffineResponse
    rw [←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ => J_response k a _)
  | some a =>
    program_unfold "affine"
    exact sub_self _

def sourceEquationResponse (k : ℕ) (equation : Option (Fin 4)) : Symbol :=
  sourceAffineResponse k equation+
    (fun zp => (1/2 : ℝ)*sourceTableResponse k 0 0 equation originalTrace zp)-
    (∑ i : Fin 3,fun zp => (1/2 : ℝ)*
      sourceTableResponse k (Fin.succ i) (Fin.succ i) equation
        (originalSource ⟨4+i.val,by omega⟩) zp)-
    (∑ i : Fin 3,sourceTableResponse k (Fin.succ (originalCrossFirst i)) (Fin.succ (originalCrossSecond i)) equation
      (originalSource (originalCrossSlot i)))-
    (∑ i : Fin 3,sourceTableResponse k 0 (Fin.succ i) equation
      (originalSource ⟨10+i.val,by omega⟩))

private theorem T_next (k : ℕ) (a b : Fin 4) (equation : Option (Fin 4))
    (X : List AngularPolynomial) (zp : PreparationVacuumCanonicalMoyal.Phase) :
    originalT (k+1) (sourceEngine (k+1)) a b equation X (Fin.last (k+1)) zp=
      originalT (k+1) (sourceEngine k) a b equation X (Fin.last (k+1)) zp+
        sourceTableResponse k a b equation X zp := by
  have response := congrFun (sourceTable_newest k a b equation X) zp
  change originalT (k+1) (sourceEngine (k+1)) a b equation X (Fin.last (k+1)) zp-
    originalT (k+1) (sourceEngine k) a b equation X (Fin.last (k+1)) zp=_ at response
  linarith

private theorem affine_next (k : ℕ) (equation : Option (Fin 4)) (zp : PreparationVacuumCanonicalMoyal.Phase) :
    originalAffine (k+1) (sourceEngine (k+1)) equation (Fin.last (k+1)) zp=
      originalAffine (k+1) (sourceEngine k) equation (Fin.last (k+1)) zp+sourceAffineResponse k equation zp := by
  have response := congrFun (sourceAffine_newest k equation) zp
  change originalAffine (k+1) (sourceEngine (k+1)) equation (Fin.last (k+1)) zp-
    originalAffine (k+1) (sourceEngine k) equation (Fin.last (k+1)) zp=_ at response
  linarith

theorem sourceEquation_newest (k : ℕ) (equation : Option (Fin 4)) :
    forceOrEnergy (k+1) (sourceEngine (k+1)) equation (Fin.last (k+1))-
      forceOrEnergy (k+1) (sourceEngine k) equation (Fin.last (k+1))=
      sourceEquationResponse k equation := by
  funext zp
  unfold forceOrEnergy sourceEquationResponse
  simp only [Pi.sub_apply,Pi.add_apply,Finset.sum_apply]
  change originalAffine (k+1) (sourceEngine (k+1)) equation (Fin.last (k+1)) zp+
    (1/2 : ℝ)*originalT (k+1) (sourceEngine (k+1)) 0 0 equation originalTrace (Fin.last (k+1)) zp-
    (∑ i : Fin 3,(1/2 : ℝ)*originalT (k+1) (sourceEngine (k+1)) (Fin.succ i) (Fin.succ i) equation
      (originalSource ⟨4+i.val,by omega⟩) (Fin.last (k+1)) zp)-
    (∑ i : Fin 3,originalT (k+1) (sourceEngine (k+1)) (Fin.succ (originalCrossFirst i)) (Fin.succ (originalCrossSecond i)) equation
      (originalSource (originalCrossSlot i)) (Fin.last (k+1)) zp)-
    (∑ i : Fin 3,originalT (k+1) (sourceEngine (k+1)) 0 (Fin.succ i) equation
      (originalSource ⟨10+i.val,by omega⟩) (Fin.last (k+1)) zp)-_= _
  simp only [T_next,affine_next,mul_add,Finset.sum_add_distrib]
  ring

end LowEnergy.PreparationVacuumEngineCancellation
