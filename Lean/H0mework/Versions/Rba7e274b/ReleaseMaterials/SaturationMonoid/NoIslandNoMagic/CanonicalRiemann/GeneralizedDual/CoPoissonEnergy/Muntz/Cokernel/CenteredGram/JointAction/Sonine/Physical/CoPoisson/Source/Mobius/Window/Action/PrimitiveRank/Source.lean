import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.RankedForcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace
namespace Paid
export FiniteMobiusResolventFlux (Rplus Rplus_identity Rplus_sub Rplus_smul actualMean box interiorBase exteriorBase
  sourceA rankedForcing rankedSourceDefect reverseRankSource interior_base_read)
end Paid

def inverseAction (z w : ℂ) (value : BurnolL2) : BurnolL2 := -value-(w-z) • Paid.Rplus w value

-- The source resolvent identity removes the second R layer without dividing by the source scalar.
theorem inverse_resolvent_source (z w : ℂ) (rightZ : 1/4<z.re) (rightW : 1/4<w.re) (value : BurnolL2) :
    inverseAction z w (Paid.Rplus z value)=-Paid.Rplus w value := by
  have source := Paid.Rplus_identity w z rightW rightZ value
  unfold inverseAction
  rw [← source]
  module

theorem inverse_source_smul (z w c : ℂ) (rightW : 1/4<w.re) (value : BurnolL2) :
    inverseAction z w (c • value)=c • inverseAction z w value := by
  unfold inverseAction
  rw [Paid.Rplus_smul w c rightW]
  module

 theorem inverse_source_sub (z w : ℂ) (rightW : 1/4<w.re) (left right : BurnolL2) :
    inverseAction z w (left-right)=inverseAction z w left-inverseAction z w right := by
  unfold inverseAction
  rw [Paid.Rplus_sub w rightW,smul_sub]
  module

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
