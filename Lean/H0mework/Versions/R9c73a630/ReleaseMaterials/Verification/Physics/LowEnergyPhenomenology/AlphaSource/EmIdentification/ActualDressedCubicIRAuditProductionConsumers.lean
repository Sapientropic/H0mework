import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRFactor
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCubicIRReturn

import Lean.Elab.Command
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCubicIRAudit
elab "checked_actual_ir_source_price_nonnegContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg).type
theorem checked_actual_ir_source_price_nonneg : checked_actual_ir_source_price_nonnegContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_ir_source_price_nonneg

elab "checked_actual_regular_matrix_real_priceContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price).type
theorem checked_actual_regular_matrix_real_price : checked_actual_regular_matrix_real_priceContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_real_price

elab "checked_actual_regular_matrix_order_lowerContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower).type
theorem checked_actual_regular_matrix_order_lower : checked_actual_regular_matrix_order_lowerContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_order_lower

elab "checked_actual_regular_matrix_factorContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor).type
theorem checked_actual_regular_matrix_factor : checked_actual_regular_matrix_factorContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_regular_matrix_factor

elab "checked_actual_fourth_ir_regularizationContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization).type
theorem checked_actual_fourth_ir_regularization : checked_actual_fourth_ir_regularizationContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_regularization

elab "checked_actual_fourth_ir_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return).type
theorem checked_actual_fourth_ir_return : checked_actual_fourth_ir_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_return

elab "checked_actual_fourth_ir_real_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return).type
theorem checked_actual_fourth_ir_real_return : checked_actual_fourth_ir_real_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_fourth_ir_real_return

elab "checked_actual_sixth_ir_zero_returnContract" : term => do
  pure (← Lean.getConstInfo ``LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return).type
theorem checked_actual_sixth_ir_zero_return : checked_actual_sixth_ir_zero_returnContract := @LowEnergy.GaussComposite.ActualDressedCubicIRReturn.actual_sixth_ir_zero_return

open CanonicalGradedSpatialSource
open ActualDressedFullCoulomb ActualDressedSourcePreparation ActualDressedSylvester ActualDressedStaticPole
open Set Filter
open scoped Topology Matrix.Norms.Elementwise

theorem actual_event_nonempty : Nonempty DressedEvent := by
  exact ⟨{
    epsilon := 1
    precision := by norm_num
    momentum := 0
    frame := Classical.choice inferInstance
    cut := 0
    energy := Complex.I
    nonreal := by simp
  }⟩

theorem actual_unit_nonzero (event : DressedEvent) : sourceDressedUnit event.epsilon event.precision≠0 := by
  intro zero
  have source:=source_dressed_unit_norm event.epsilon event.precision
  rw [zero,norm_zero] at source
  exact zero_ne_one source

theorem same_original_fourth_factor (event : DressedEvent) :
    ∃G : ℂ→Matrix (Fin 289) (Fin 289) ℂ,AnalyticAt ℂ G 0 ∧
      ∀ᶠz : ℂ in 𝓝 0,dressedStaticPoleRegular event z=z^(2*dressedStaticPoleOrder event-4) • G z :=
  ActualDressedCubicIRReturn.actual_regular_matrix_factor event

theorem same_full_actual_fourth_return (event : DressedEvent) :
    ∃L : Matrix (Fin 289) (Fin 289) ℂ,
      Tendsto (fun s : ℝ=>(s:ℂ)^4 • dressedStaticPolarization event 0 (s:ℂ))
        (nhdsWithin 0 (Ioi (0:ℝ))) (𝓝 L) :=
  ActualDressedCubicIRReturn.actual_fourth_ir_real_return event

theorem same_original_sixth_zero_return (event : DressedEvent) :
    Tendsto (fun z : ℂ=>z^6 • dressedStaticPolarization event 0 z)
      (nhdsWithin 0 {z : ℂ|0<z.re}) (𝓝 0) :=
  ActualDressedCubicIRReturn.actual_sixth_ir_zero_return event
end LowEnergy.GaussComposite.ActualDressedCubicIRAudit

