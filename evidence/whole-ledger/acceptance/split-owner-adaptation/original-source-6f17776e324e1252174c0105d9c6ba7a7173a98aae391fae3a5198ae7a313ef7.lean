import Lean
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCompactAdjointRSource.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
open Complex MeasureTheory Set Filter SourceGeneratedHilbertCokernel
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
namespace Paid
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.FiniteMobiusResolventFlux (actualMean Rplus RplusIntegrand Rplus_integrable)
export _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalJointFluxSource (actual_mean_source_integral actual_mean_dilation_source source_weight_mean_phase)
end Paid
local notation "q" => (1/4:ℝ)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)



elab "actualConstantEulerSource" : term => do
 let head := ("_private.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.RieszEulerDomain".splitOn ".").foldl Lean.Name.str Lean.Name.anonymous
 let full := ("SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalRieszFinitePairing.CoPoisson.Ward.RieszEulerDomain.constant_euler".splitOn ".").foldl Lean.Name.str (Lean.Name.num head 0)
 return Lean.mkConst full

namespace ConstantSource
export OriginalKConstantContactSourceAction.ConstantSource (seed)
end ConstantSource

def actualWholeSeedRField (coordinate : BurnolCompletedMellinCoordinate) : BurnolL2 :=
 (-2/(coordinate.value-1):ℂ) •
 (OriginalRieszFiniteSource.edgePrimitive (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)+ConstantSource.seed)

/-- The two original source Euler laws actually cancel the same contact, generating the entire R seed field. -/
theorem actual_whole_seed_R_euler (coordinate : BurnolCompletedMellinCoordinate) :
 OriginalRieszSource.GapEuler.euler (actualWholeSeedRField coordinate : TemperedDistribution ℝ ℂ)=
 (-(coordinate.value-1/2) • actualWholeSeedRField coordinate-(2:ℂ) • ConstantSource.seed : BurnolL2) := by
 have edge:=OriginalRieszFiniteSource.edgePrimitive_euler
   (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate)
 have constant:=actualConstantEulerSource
 have qualified : coordinate.value-1≠0 := by
  intro zero
  have real:=congrArg Complex.re zero
  norm_num at real
  linarith [coordinate.belowOne]
 change OriginalRieszSource.GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 (actualWholeSeedRField coordinate))=
   Lp.toTemperedDistributionCLM ℂ volume 2 _
 unfold actualWholeSeedRField
 simp only [map_smul,map_add,map_sub,Lp.toTemperedDistributionCLM_apply]
 have coefficient : star (OriginalKQuarterTailPhysicalSource.actualStarSource coordinate).value=coordinate.value :=star_star _
 rw [coefficient] at edge
 rw [eq_sub_of_add_eq edge,constant]
 have scalar : (-2/(coordinate.value-1):ℂ)*(coordinate.value-1)= -2 := by
  field_simp [qualified]
 have generated:=congrArg (fun factor : ℂ=>factor • (ConstantSource.seed : TemperedDistribution ℝ ℂ)) scalar
 linear_combination (norm:=module) generated

/-- The generated whole field enters the existing strong-source resolvent consumer. -/
theorem actual_original_R_seed_whole_field (coordinate : BurnolCompletedMellinCoordinate) :
 burnolDirectRightResolvent (coordinate.value/2) ConstantSource.seed=actualWholeSeedRField coordinate := by
 have native:=OriginalRieszFinitePairing.CoPoisson.Ward.DilationWard.strong_derivative _ _
   (actual_whole_seed_R_euler coordinate)
 have source : HasDerivAt (fun shift : ℝ=>burnolMultiplicativeDilation shift (actualWholeSeedRField coordinate))
   (-(coordinate.value-1/2) • actualWholeSeedRField coordinate-(2:ℂ) • ConstantSource.seed)
   ((fun time : ℝ=>-time/2) 0) := by simpa only [neg_zero,zero_div] using native
 have scalar : HasDerivAt (fun time : ℝ=>-time/2) (-1/2:ℝ) 0 := by
  simpa only [Pi.neg_apply,neg_div,id_eq] using ((hasDerivAt_id (0:ℝ)).neg.div_const 2)
 have generated:=source.scomp (0:ℝ) scalar
 have right : 1/4<(coordinate.value/2).re := by
  rw [Complex.div_re];norm_num;linarith [coordinate.rightHalf]
 apply (burnolDirectRightResolvent_of_strongEquation (coordinate.value/2) right
   ConstantSource.seed (actualWholeSeedRField coordinate) ?_).symm
 convert! generated using 1
 rw [←algebraMap_smul ℂ (-1/2:ℝ)]
 push_cast
 module

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKConstantSeedWholeRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
