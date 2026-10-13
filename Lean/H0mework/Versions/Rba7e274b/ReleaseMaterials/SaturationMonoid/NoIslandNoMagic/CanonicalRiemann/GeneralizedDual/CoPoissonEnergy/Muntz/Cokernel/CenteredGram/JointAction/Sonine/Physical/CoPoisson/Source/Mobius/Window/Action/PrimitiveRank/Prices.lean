import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.InversePower
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Read
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory
open scoped InnerProductSpace

-- The original reverse reaction now has three fixed source prices and no nested R or forward tail price.
def reversePrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  -(2*Source.exteriorMoment coordinate value)*(4:ℂ)^(coordinate.value-star coordinate.value)*
    inner ℂ (pairedColumn coordinate h) (Paid.interiorBase (conjugateCoordinate coordinate))+
  (Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))*inner ℂ (pairedColumn coordinate h) (Paid.box 4)+
  (((star coordinate.value-coordinate.value)/2)*(Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))-
    Source.sigma*Paid.actualMean value)*
    inner ℂ (pairedColumn coordinate h) (Paid.Rplus (star coordinate.value/2) (Paid.box 4))

 theorem inverse_reverse_source_price (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) (star coordinate.value/2)
      (Source.reverseRankSource coordinate value))=reversePrice coordinate value h := by
  have right : 1/4<(star coordinate.value/2).re := by
    rw [Complex.div_re]
    norm_num [Complex.star_def]
    linarith [coordinate.rightHalf]
  rw [inverse_reverse_rank_read coordinate value _ right]
  have source := inverse_interior_source coordinate (conjugateCoordinate coordinate)
  change inverseAction (coordinate.value/2) (star coordinate.value/2) (Paid.interiorBase coordinate)=
    -(4:ℂ)^(coordinate.value-star coordinate.value) • Paid.interiorBase (conjugateCoordinate coordinate) at source
  rw [source,inner_smul_right]
  unfold reversePrice
  ring

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
