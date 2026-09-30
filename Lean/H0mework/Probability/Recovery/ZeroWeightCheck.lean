import H0mework.Probability.Recovery.Error

/-! Source values at zero weight cannot enter the recovery error or the generated conditional support. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceWeightedRecovery.Controls

open scoped Classical

noncomputable section

theorem zero_weight_error (present hidden decoded : ℂ) :
    error (PMF.pure (0 : Fin 2)) (fun _ : Fin 2 => ())
      (fun point => if point = 0 then present else hidden) (fun _ => decoded) = ‖present - decoded‖ ^ 2 := by
  simp [error, Fin.sum_univ_succ, PMF.pure_apply]

theorem zero_weight_support :
    (SourceConditionalHistory.conditional (PMF.pure (0 : Fin 2)) (fun _ : Fin 2 => ()) ()
      ((PMF.mem_support_map_iff _ _ _).mpr ⟨0, by simp, rfl⟩)).support = {0} := by
  rw [SourceConditionalHistory.conditional_support]
  simp

end
end SourceWeightedRecovery.Controls
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
