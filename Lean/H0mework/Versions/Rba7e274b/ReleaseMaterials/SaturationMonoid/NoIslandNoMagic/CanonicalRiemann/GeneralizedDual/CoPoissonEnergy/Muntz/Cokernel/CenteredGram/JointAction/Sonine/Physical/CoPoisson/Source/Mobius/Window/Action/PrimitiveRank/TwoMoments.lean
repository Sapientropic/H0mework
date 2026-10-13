import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Box
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Prices
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory
open scoped InnerProductSpace

def reverseMassCoefficient (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value)+
  ((((star coordinate.value-coordinate.value)/2)*(Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))-
    Source.sigma*Paid.actualMean value)*2/(1-star coordinate.value))

def reversePowerCoefficient (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  -(2*Source.exteriorMoment coordinate value)*(4:ℂ)^(coordinate.value-star coordinate.value)+
  ((((star coordinate.value-coordinate.value)/2)*(Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))-
    Source.sigma*Paid.actualMean value)*2*(4:ℂ)^(1-star coordinate.value)/(1-star coordinate.value))

def twoMomentPrice (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) : ℂ :=
  reverseMassCoefficient coordinate value*inner ℂ (pairedColumn coordinate h) (Paid.box 4)+
  reversePowerCoefficient coordinate value*inner ℂ (pairedColumn coordinate h) (Paid.interiorBase (conjugateCoordinate coordinate))

 theorem reverse_source_two_moments (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) (star coordinate.value/2)
      (Source.reverseRankSource coordinate value))=twoMomentPrice coordinate value h := by
  rw [inverse_reverse_source_price]
  have source := box_Rplus_source (conjugateCoordinate coordinate)
  change Paid.Rplus (star coordinate.value/2) (Paid.box 4)=boxSource (conjugateCoordinate coordinate) at source
  unfold reversePrice twoMomentPrice reverseMassCoefficient reversePowerCoefficient
  rw [source]
  unfold boxSource
  simp only [conjugateCoordinate,inner_add_right,inner_smul_right]
  ring

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
