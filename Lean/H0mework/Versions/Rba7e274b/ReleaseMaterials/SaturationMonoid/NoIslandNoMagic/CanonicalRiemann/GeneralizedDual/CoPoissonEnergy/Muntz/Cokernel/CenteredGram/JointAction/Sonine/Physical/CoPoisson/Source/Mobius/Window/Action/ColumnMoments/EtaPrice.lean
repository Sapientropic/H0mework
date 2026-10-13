import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.EtaAction
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.FinitePrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace

def generatedEtaPrice (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  finiteResponsePrice coordinate h+inner ℂ (Paid.pairedColumn coordinate h) (etaRemainingSource coordinate)

-- The complete eta defect scalar now consumes the actual mu-cut endpoint producer.
theorem original_eta_complete_price (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
    inner ℂ (Paid.pairedColumn coordinate h) (S.D (FiniteMobiusResolventFlux.S.regularSource coordinate))=
      generatedEtaPrice coordinate h := by
  rw [original_eta_defect_action,inner_add_right,original_response_complete_price coordinate h nonnegative bounded]
  rfl

-- The original Rplus source is retained as an actual input action; no fixed-window law is promoted to all tau.
theorem original_eta_Rplus_action (coordinate : BurnolCompletedMellinCoordinate) (parameter : ℂ) (right : 1/4<parameter.re) :
    S.Rplus parameter (S.D (FiniteMobiusResolventFlux.S.regularSource coordinate))=
      S.Rplus parameter (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))+
        S.Rplus parameter (etaRemainingSource coordinate) := by
  rw [original_eta_defect_action]
  have source := S.Rplus_sub parameter right (FiniteMobiusResolventFlux.M (wholeContactResponse coordinate))
    (-etaRemainingSource coordinate)
  rw [show FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)- -etaRemainingSource coordinate=
    FiniteMobiusResolventFlux.M (wholeContactResponse coordinate)+etaRemainingSource coordinate by module] at source
  have negative := S.Rplus_smul parameter (-1) right (etaRemainingSource coordinate)
  simp only [neg_one_smul] at negative
  rw [negative] at source
  simpa only [sub_neg_eq_add] using source

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
