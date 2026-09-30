import H0mework.Versions.Y.Arithmetic.RiemannUnitShell.Algebra

/-! The original negative right resolvent is a bounded linear operator, with its actual orbit norm bound. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
noncomputable section

def burnolDirectRightResolventCLM (coordinate : BurnolCompletedMellinCoordinate) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  let z := coordinate.value / 2
  have rq : 1 / 4 < z.re := by
    dsimp only [z]; rw [Complex.div_re]; norm_num; linarith [coordinate.rightHalf]
  LinearMap.mkContinuous
    { toFun := burnolDirectRightResolvent z
      map_add' := fun a b => by
        have same := burnolDirectRightResolvent_sub z rq a (-b)
        have neg : burnolDirectRightResolvent z (-b) = -burnolDirectRightResolvent z b := by
          simpa only [neg_one_smul] using burnolDirectRightResolvent_smul z (-1) b
        simpa only [sub_neg_eq_add, neg] using same
      map_smul' := fun c v => burnolDirectRightResolvent_smul z c v }
    (∫ h : ℝ in Ioi 0, ‖positiveMellinQuarterRightResolventWeight z h‖)
    (by
      intro value
      change ‖burnolDirectRightResolvent z value‖ ≤ _
      unfold burnolDirectRightResolvent
      rw [norm_neg]
      calc
        _ ≤ ∫ h : ℝ in Ioi 0, ‖burnolDirectRightResolventIntegrand z value h‖ :=
          norm_integral_le_integral_norm _
        _ = _ := by
          simp only [burnolDirectRightResolventIntegrand, norm_smul,
            (burnolMultiplicativeDilation _).norm_map]
          rw [integral_mul_const])

end
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
