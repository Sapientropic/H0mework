import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LogStockAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock

open BurnolPhysicalState MeasureTheory
open OriginalGamma.Source.JointLogConductor OriginalGamma.Source.RelativeConductorGapReadback
open scoped InnerProductSpace

open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

abbrev Base := LogStock.Whole
abbrev SecondSlots := WithLp 2 (BurnolL2 × BurnolL2)
abbrev Ambient := WithLp 2 (Base × SecondSlots)

private def baseRead : Ambient →L[ℂ] Base := WithLp.fstL 2 ℂ Base SecondSlots

private def physicalRead : Ambient →L[ℂ] BurnolL2 :=
  (WithLp.fstL 2 ℂ BurnolL2 BurnolL2).comp (WithLp.sndL 2 ℂ Base SecondSlots)

private def outsideRead : Ambient →L[ℂ] BurnolL2 :=
  (WithLp.sndL 2 ℂ BurnolL2 BurnolL2).comp (WithLp.sndL 2 ℂ Base SecondSlots)

def firstPhysical : Base →L[ℂ] BurnolL2 := LogStock.gamma.comp LogStock.physical
def firstOutside : Base →L[ℂ] BurnolL2 := LogStock.gamma - firstPhysical

private def testDifference (first second : Ambient →L[ℂ] BurnolL2)
    (test : SchwartzMap ℝ ℂ) : Ambient →L[ℂ] ℂ :=
  (innerSL ℂ (wholeConductorTest test)).comp first -
    (innerSL ℂ (test.toLp 2 volume)).comp second

private def testedPair (first second : Ambient →L[ℂ] BurnolL2) : Submodule ℂ Ambient :=
  ⨅ test : SchwartzMap ℝ ℂ, LinearMap.ker (testDifference first second test).toLinearMap

private theorem tested_pair_iff (first second : Ambient →L[ℂ] BurnolL2) (x : Ambient) :
    x ∈ testedPair first second ↔ GammaPair (first x) (second x) := by
  rw [testedPair, Submodule.mem_iInf, GammaPair]
  refine forall_congr' fun test => ?_
  change inner ℂ (wholeConductorTest test) (first x) - inner ℂ (test.toLp 2 volume) (second x) = 0 ↔ _
  exact sub_eq_zero

private theorem tested_pair_closed (first second : Ambient →L[ℂ] BurnolL2) :
    IsClosed (testedPair first second : Set Ambient) := by
  rw [testedPair, Submodule.coe_iInf]
  exact isClosed_iInter fun test => (testDifference first second test).isClosed_ker

/-- Both second fields belong to the conductor graphs of the original two first slots. -/
def carrier : Submodule ℂ Ambient :=
  testedPair (firstPhysical.comp baseRead) physicalRead ⊓
    testedPair (firstOutside.comp baseRead) outsideRead

theorem carrier_closed : IsClosed (carrier : Set Ambient) :=
  (tested_pair_closed _ _).inter (tested_pair_closed _ _)

abbrev Whole := ↥carrier
instance : CompleteSpace Whole := carrier_closed.isComplete.completeSpace_coe

def base : Whole →L[ℂ] Base := baseRead.comp carrier.subtypeL
def physicalSecond : Whole →L[ℂ] BurnolL2 := physicalRead.comp carrier.subtypeL
def outsideSecond : Whole →L[ℂ] BurnolL2 := outsideRead.comp carrier.subtypeL

theorem second_pairs (x : Whole) :
    GammaPair (firstPhysical (base x)) (physicalSecond x) ∧
      GammaPair (firstOutside (base x)) (outsideSecond x) :=
  ⟨(tested_pair_iff _ _ _).mp x.property.1, (tested_pair_iff _ _ _).mp x.property.2⟩

def ofFields (x : Base) (p o : BurnolL2)
    (physical : GammaPair (firstPhysical x) p) (outside : GammaPair (firstOutside x) o) : Whole :=
  ⟨WithLp.toLp 2 (x, WithLp.toLp 2 (p,o)),
    (tested_pair_iff _ _ _).mpr physical, (tested_pair_iff _ _ _).mpr outside⟩

theorem base_injective : Function.Injective base := by
  intro x y same
  have right := second_pairs y
  rw [← same] at right
  have first := conductor_unique _ _ _ (second_pairs x).1 right.1
  have second := conductor_unique _ _ _ (second_pairs x).2 right.2
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  exact Prod.ext same ((WithLp.equiv 2 _).injective (Prod.ext first second))

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
