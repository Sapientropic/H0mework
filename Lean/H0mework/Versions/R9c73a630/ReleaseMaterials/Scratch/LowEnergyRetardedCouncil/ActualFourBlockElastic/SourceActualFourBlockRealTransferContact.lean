import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferContactRead
import Mathlib.Analysis.Meromorphic.Order
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActualFourBlockElastic.SourceActualFourBlockRealTransferTransfer

set_option autoImplicit false
noncomputable section
namespace LowEnergy.ActualFourBlockRealTransfer
open MixedSpectatorContactExchange MixedSpectatorPairedSourceFrame

theorem actual_contact_polynomial_analytic (z : ℂ) (i : Fin 117) :
    AnalyticAt ℂ (fun x => contactPolynomial (worldTransfer x 0) i) z := by
  simp_rw [actual_axial_transfer]
  fin_cases i <;>
    simp only [contactPolynomial,Matrix.cons_val_zero',Matrix.cons_val_succ'] <;>
    norm_num [axialTransfer] <;> fun_prop

theorem actual_contact_coefficient_analytic (z : ℂ) (a b : Fin 97) :
    AnalyticAt ℂ (fun x => contactCoefficient (worldTransfer x 0) a b) z := by
  have h : (fun x => contactCoefficient (worldTransfer x 0) a b) =
      (fun x => contactRead (worldTransfer x 0) a b) := by
    funext x
    exact actual_contact_read _ a b
  rw [h]
  unfold contactRead
  cases hs : contactIndex a b with
  | none => simpa only [hs] using (analyticAt_const (v := (0 : ℂ)) (x := z))
  | some i => simpa only [hs] using actual_contact_polynomial_analytic z i

end LowEnergy.ActualFourBlockRealTransfer
