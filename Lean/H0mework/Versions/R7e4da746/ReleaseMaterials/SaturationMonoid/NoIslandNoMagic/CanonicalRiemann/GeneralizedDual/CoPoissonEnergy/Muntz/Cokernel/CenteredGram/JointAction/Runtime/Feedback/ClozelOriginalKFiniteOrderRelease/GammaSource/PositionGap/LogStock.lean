import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.LogPairClosureSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock

open BurnolPhysicalState
open OriginalGamma.Source.FiniteLogCounting
open scoped lp

open private logGraph log_graph_closed from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.LogPairClosureSource
open private log_pair_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback

abbrev LogSlots := WithLp 2 (BurnolL2 × BurnolL2)
abbrev AmbientStock := WithLp 2 (BurnolL2 × LogSlots)

private def raw : AmbientStock →L[ℂ] BurnolL2 :=
  WithLp.fstL 2 ℂ BurnolL2 LogSlots

private def position : AmbientStock →L[ℂ] BurnolL2 :=
  (WithLp.fstL 2 ℂ BurnolL2 BurnolL2).comp (WithLp.sndL 2 ℂ BurnolL2 LogSlots)

private def frequency : AmbientStock →L[ℂ] BurnolL2 :=
  (WithLp.sndL 2 ℂ BurnolL2 BurnolL2).comp (WithLp.sndL 2 ℂ BurnolL2 LogSlots)

private def positionPair : AmbientStock →L[ℂ] (BurnolL2 × BurnolL2) :=
  raw.prod position

private def inversePair : AmbientStock →L[ℂ] (BurnolL2 × BurnolL2) :=
  (fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp raw).prod frequency

/-- The same raw occurrence lies in the position gap and carries both original closed log graphs. -/
def carrier : Submodule ℂ AmbientStock :=
  PositionField.comap raw.toLinearMap ⊓
    (logGraph.comap positionPair.toLinearMap ⊓ logGraph.comap inversePair.toLinearMap)

theorem carrier_closed : IsClosed (carrier : Set AmbientStock) :=
  (positionSpace.isClosed.preimage raw.continuous).inter
    ((log_graph_closed.preimage positionPair.continuous).inter
      (log_graph_closed.preimage inversePair.continuous))

abbrev Whole := ↥carrier

instance : CompleteSpace Whole := carrier_closed.isComplete.completeSpace_coe

def field : Whole →L[ℂ] BurnolL2 := raw.comp carrier.subtypeL
def positionLog : Whole →L[ℂ] BurnolL2 := position.comp carrier.subtypeL
def inverseLog : Whole →L[ℂ] BurnolL2 := frequency.comp carrier.subtypeL

theorem field_mem (x : Whole) : field x ∈ PositionField := x.property.1

theorem log_pairs (x : Whole) :
    LogPair (field x) (positionLog x) ∧ LogPair (fourierL2.symm (field x)) (inverseLog x) :=
  x.property.2

def ofLogs (x : PositionField) (p f : BurnolL2)
    (hp : LogPair (x : BurnolL2) p) (hf : LogPair (fourierL2.symm (x : BurnolL2)) f) : Whole :=
  ⟨WithLp.toLp 2 ((x : BurnolL2), WithLp.toLp 2 (p, f)), x.property, hp, hf⟩

theorem field_injective : Function.Injective field := by
  intro x y same
  have yPosition := (log_pairs y).1
  have yInverse := (log_pairs y).2
  rw [← same] at yPosition yInverse
  have p := log_pair_unique _ _ _ (log_pairs x).1 yPosition
  have f := log_pair_unique _ _ _ (log_pairs x).2 yInverse
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext same ((WithLp.equiv 2 _).injective (Prod.ext p f))

def coordinates (c : BurnolCompletedMellinCoordinate) : Whole →L[ℂ] ℓ²(Nat, ℂ) :=
  (basis c).repr.toContinuousLinearEquiv.toContinuousLinearMap.comp (field.codRestrict PositionField field_mem)

theorem coordinates_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (coordinates c) := by
  intro x y same
  apply field_injective
  exact congrArg Subtype.val ((basis c).repr.injective same)

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.LogStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
