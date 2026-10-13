import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ColumnMoments.Moments
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalColumnMomentSource
open Complex MeasureTheory
open scoped InnerProductSpace
namespace S
export FiniteMobiusResolventFlux (D defectFlux actual_defect_R_action source_resolvent_inverse Rplus Rplus_sub Rplus_smul)
export OriginalPrimitiveRankBalance (inverseAction inverse_source_add inverse_source_sub inverse_source_smul inverse_resolvent_source)
end S
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

-- The actual source action removes both nested R responses before any physical read is taken.
theorem contact_source_action (z w : ℂ) (rightZ : 1/4<z.re) (rightW : 1/4<w.re)
    (contact regular : BurnolL2) :
    S.inverseAction z w (S.D (contact-(w-z) • burnolDirectRightResolvent z contact+
      (1/2:ℂ) • burnolDirectRightResolvent z regular))=
      -S.D contact-(1/2:ℂ) • S.Rplus w (S.D regular)+
        S.inverseAction z w (-(w-z) • S.defectFlux z contact+(1/2:ℂ) • S.defectFlux z regular) := by
  have source : S.D (contact-(w-z) • burnolDirectRightResolvent z contact+
      (1/2:ℂ) • burnolDirectRightResolvent z regular)=
    (S.D contact-(w-z) • S.Rplus z (S.D contact))+(1/2:ℂ) • S.Rplus z (S.D regular)+
      (-(w-z) • S.defectFlux z contact+(1/2:ℂ) • S.defectFlux z regular) := by
    simp only [map_add,map_sub,map_smul,S.actual_defect_R_action z rightZ]
    module
  rw [source,S.inverse_source_add _ _ rightW,S.inverse_source_add _ _ rightW,
    S.inverse_source_smul _ _ _ rightW,S.inverse_resolvent_source _ _ rightZ rightW]
  have cancellation : S.inverseAction z w (S.D contact-(w-z) • S.Rplus z (S.D contact))=-S.D contact := by
    have generated := S.source_resolvent_inverse z w rightZ rightW (S.D contact)
    have negative : S.D contact-(w-z) • S.Rplus z (S.D contact)=-((w-z) • S.Rplus z (S.D contact)-S.D contact) := by module
    rw [negative,show -((w-z) • S.Rplus z (S.D contact)-S.D contact)=(-1:ℂ) • ((w-z) • S.Rplus z (S.D contact)-S.D contact) by module,
      S.inverse_source_smul _ _ _ rightW]
    change (-1:ℂ) • (-( (w-z) • S.Rplus z (S.D contact)-S.D contact)-
      (w-z) • S.Rplus w ((w-z) • S.Rplus z (S.D contact)-S.D contact))=_
    rw [generated]
    module
  rw [cancellation]
  module

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

def contactFluxSource : BurnolL2 :=
  -(FiniteMobiusResolventFlux.sourceA observation) • S.defectFlux (observation.coordinate/2)
    (FiniteMobiusResolventFlux.S.contactCorrection (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))+
  (1/2:ℂ) • S.defectFlux (observation.coordinate/2)
    (FiniteMobiusResolventFlux.S.regularSource (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))

def generatedContactRead (h : ℝ) : ℂ :=
  -inner ℂ (Paid.pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
    (S.D (FiniteMobiusResolventFlux.S.contactCorrection (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half)))-
  (1/2:ℂ)*inner ℂ (Paid.pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
    (S.Rplus (star observation.coordinate/2)
      (S.D (FiniteMobiusResolventFlux.S.regularSource (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))))+
  inner ℂ (Paid.pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
    (S.inverseAction (observation.coordinate/2) (star observation.coordinate/2) (contactFluxSource observation nontrivial half))

theorem original_primitive_contact_action (h : ℝ) :
    OriginalPrimitiveRankBalance.primitiveRead observation nontrivial half h=generatedContactRead observation nontrivial half h := by
  have rightZ := FiniteMobiusResolventFlux.Paid.parameter_rightQuarter observation half
  have rightW : 1/4<(star observation.coordinate/2).re := by
    rw [Complex.div_re]
    norm_num [Complex.star_def]
    linarith [half.down]
  have source := contact_source_action (observation.coordinate/2) (star observation.coordinate/2) rightZ rightW
    (FiniteMobiusResolventFlux.S.contactCorrection (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))
    (FiniteMobiusResolventFlux.S.regularSource (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))
  have scalar : star observation.coordinate/2-observation.coordinate/2=FiniteMobiusResolventFlux.sourceA observation := by
    unfold FiniteMobiusResolventFlux.sourceA
    ring
  rw [scalar] at source
  unfold OriginalPrimitiveRankBalance.primitiveRead FiniteMobiusResolventFlux.primitiveSource
  simp only [FiniteMobiusResolventFlux.Paid.original_R_direct]
  rw [source]
  simp only [inner_add_right,inner_sub_right,inner_neg_right,inner_smul_right]
  rfl

end OriginalColumnMomentSource
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
