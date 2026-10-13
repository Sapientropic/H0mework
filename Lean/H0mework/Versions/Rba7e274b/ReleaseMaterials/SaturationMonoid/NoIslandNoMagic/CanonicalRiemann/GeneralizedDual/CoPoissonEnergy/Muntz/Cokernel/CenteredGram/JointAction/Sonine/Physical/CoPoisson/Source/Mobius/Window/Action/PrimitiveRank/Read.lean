import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.PrimitiveRank.Contraction
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalPrimitiveRankBalance
open Complex MeasureTheory
open scoped InnerProductSpace
namespace Source
export FiniteMobiusResolventFlux (D primitiveSource rankedDefectFlux rankedForcing rankedSourceDefect sourceA sigma
  reverseRankSource exteriorMoment innerTailMoment Rplus_sub Rplus_smul)
end Source
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual

 theorem inverse_source_add (z w : ℂ) (rightW : 1/4<w.re) (left right : BurnolL2) :
    inverseAction z w (left+right)=inverseAction z w left+inverseAction z w right := by
  have add : Paid.Rplus w (left+right)=Paid.Rplus w left+Paid.Rplus w right := by
    have source := Paid.Rplus_sub w rightW left (-right)
    rw [show left - -right=left+right by module] at source
    have negative := Paid.Rplus_smul w (-1) rightW right
    simp only [neg_one_smul] at negative
    rw [negative] at source
    simpa only [sub_neg_eq_add] using source
  unfold inverseAction
  rw [add,smul_add]
  module

-- Source contraction eliminates the complete forward tail coefficient from the physical column read.
theorem inverse_rank_flux_read (coordinate : BurnolCompletedMellinCoordinate) (value : FiniteMobiusResolventFlux.Ambient)
    (w : ℂ) (rightW : 1/4<w.re) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) w (Source.rankedDefectFlux coordinate value))=
    inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) w
      (Source.reverseRankSource coordinate (fourierL2 (value : BurnolL2)))) := by
  unfold Source.rankedDefectFlux
  rw [inverse_source_add _ _ rightW,inverse_source_smul _ _ _ rightW,inner_add_right,inner_smul_right,
    paired_inverse_tate_tail_zero coordinate _ w rightW,mul_zero,add_zero]

-- The paid identity collapses the reverse mean response to a single original Rplus-star response.
theorem inverse_reverse_rank_read (coordinate : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (w : ℂ) (rightW : 1/4<w.re) (h : ℝ) :
    inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) w (Source.reverseRankSource coordinate value))=
      (2*Source.exteriorMoment coordinate value)*
        inner ℂ (pairedColumn coordinate h) (inverseAction (coordinate.value/2) w (Paid.interiorBase coordinate))+
      (Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))*inner ℂ (pairedColumn coordinate h) (Paid.box 4)+
      ((w-coordinate.value/2)*(Source.sigma*Paid.actualMean (Paid.Rplus (coordinate.value/2) value))-
        Source.sigma*Paid.actualMean value)*inner ℂ (pairedColumn coordinate h) (Paid.Rplus w (Paid.box 4)) := by
  have rightZ : 1/4<(coordinate.value/2).re := by rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
  unfold Source.reverseRankSource
  rw [inverse_source_add _ _ rightW,inverse_source_sub _ _ rightW,
    inverse_source_smul _ _ _ rightW,inverse_source_smul _ _ _ rightW,inverse_source_smul _ _ _ rightW,
    inverse_resolvent_source _ _ rightZ rightW]
  simp only [inner_add_right,inner_sub_right,inner_smul_right,inner_neg_right]
  unfold inverseAction
  simp only [inner_sub_right,inner_neg_right,inner_smul_right]
  ring

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : CenteredGram.IntegralGraphJointAction.OriginalKCombCalculation.Half observation)

 theorem original_rank_defect_read (h : ℝ) :
    inner ℂ (pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
      (Source.rankedSourceDefect observation nontrivial half)=
    inner ℂ (pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
      (inverseAction (observation.coordinate/2) (star observation.coordinate/2) (Source.D (Source.primitiveSource observation nontrivial half)))-
    Source.sourceA observation*inner ℂ (pairedColumn (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half) h)
      (inverseAction (observation.coordinate/2) (star observation.coordinate/2)
        (Source.reverseRankSource (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half)
          (fourierL2 (FiniteMobiusResolventFlux.Prior.originalK observation nontrivial half)))) := by
  have rightW : 1/4<(star observation.coordinate/2).re := by
    rw [Complex.div_re]
    norm_num [Complex.star_def]
    linarith [half.down]
  have scalar : star observation.coordinate/2-observation.coordinate/2=Source.sourceA observation := by unfold Source.sourceA;ring
  have inverseRead : Source.rankedSourceDefect observation nontrivial half=
      inverseAction (observation.coordinate/2) (star observation.coordinate/2) (Source.rankedForcing observation nontrivial half) := by
    unfold Source.rankedSourceDefect inverseAction
    rw [scalar]
  rw [inverseRead]
  unfold Source.rankedForcing
  rw [inverse_source_sub _ _ rightW,inverse_source_smul _ _ _ rightW,inner_sub_right,inner_smul_right]
  have source := inverse_rank_flux_read (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half)
    (burnolCompletedMellinRieszVector (FiniteMobiusResolventFlux.Prior.coordinate observation nontrivial half))
    (star observation.coordinate/2) rightW h
  rw [FiniteMobiusResolventFlux.Prior.coordinate_value] at source
  rw [source]
  rfl

end OriginalPrimitiveRankBalance
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
