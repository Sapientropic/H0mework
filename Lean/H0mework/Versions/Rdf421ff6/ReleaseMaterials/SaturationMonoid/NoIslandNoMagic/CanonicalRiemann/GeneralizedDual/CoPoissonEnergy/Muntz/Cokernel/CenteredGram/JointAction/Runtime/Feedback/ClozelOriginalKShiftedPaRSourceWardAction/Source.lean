import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRSourceEnergy.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace Energy
export OriginalKDecodedPaRSourceEnergy (sourceR source_R_vector_action source_R_energy)
end Energy
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)
abbrev sourceA := OriginalKDecodedPaRFourFaceSourceAction.sourceA observation nontrivial half depth ordinal h H N

def shiftedR (shift : ℝ) : BurnolL2 := burnolMultiplicativeDilation (-shift/2) (Energy.sourceR observation nontrivial half depth ordinal h H N)
def shiftedA (shift : ℝ) : BurnolL2 := burnolMultiplicativeDilation (-shift/2) (sourceA observation nontrivial half depth ordinal h H N)
def shiftedVelocity (shift : ℝ) : BurnolL2 := (observation.coordinate/2-1/4) • shiftedR observation nontrivial half depth ordinal h H N shift+
 shiftedA observation nontrivial half depth ordinal h H N shift

/-- The source group transports the actual vector Ward velocity before any projected or numerical read. -/
theorem source_Ward_at_shift (shift : ℝ) :
 HasDerivAt (fun t : ℝ => shiftedR observation nontrivial half depth ordinal h H N t)
  (shiftedVelocity observation nontrivial half depth ordinal h H N shift) shift := by
 let D := (burnolMultiplicativeDilation (-shift/2)).toLinearIsometry.toContinuousLinearMap
 have initial := Energy.source_R_vector_action observation nontrivial half depth ordinal h H N
 have pushed := (D.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 initial
 have move : HasDerivAt (fun t : ℝ => t-shift) 1 shift := (hasDerivAt_id shift).sub_const shift
 have generated := pushed.scomp_of_eq shift move (by simp)
 have same : (fun t : ℝ => D (burnolMultiplicativeDilation (-(t-shift)/2)
  (Energy.sourceR observation nontrivial half depth ordinal h H N)))=
  (fun t : ℝ => shiftedR observation nontrivial half depth ordinal h H N t) := by
  funext t
  change burnolMultiplicativeDilation (-shift/2) (burnolMultiplicativeDilation (-(t-shift)/2) _)=_
  rw [burnolMultiplicativeDilation_add]
  have parameter : -shift/2+ -(t-shift)/2= -t/2 := by ring
  rw [parameter]
  rfl
 have velocity : D ((observation.coordinate/2-1/4) • Energy.sourceR observation nontrivial half depth ordinal h H N+
  sourceA observation nontrivial half depth ordinal h H N)=shiftedVelocity observation nontrivial half depth ordinal h H N shift := by
  rw [map_add,map_smul]
  rfl
 change HasDerivAt (fun t : ℝ => D (burnolMultiplicativeDilation (-(t-shift)/2)
  (Energy.sourceR observation nontrivial half depth ordinal h H N)))
  (1 • D ((observation.coordinate/2-1/4) • Energy.sourceR observation nontrivial half depth ordinal h H N+
   sourceA observation nontrivial half depth ordinal h H N)) shift at generated
 rw [one_smul,same,velocity] at generated
 exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKShiftedPaRSourceWardAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
