import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDecodedPaRFourFaceSourceAction.Physical
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBoundarySourceAction.Integral
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

/-- All four cotests are qualified by their own literal source action. -/
def ownPhysicalFaces : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) :=
 let stock := ownFourFaceSource observation nontrivial half depth ordinal h H N
 let paid := own_four_faces_physical observation nontrivial half depth ordinal h H N
 ((⟨stock.1.1,paid.1⟩,⟨stock.1.2,paid.2.1⟩),(⟨stock.2.1,paid.2.2.1⟩,⟨stock.2.2,paid.2.2.2⟩))

def boundaryFourRead (stock : (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier) × (BurnolPaAmbientCarrier × BurnolPaAmbientCarrier)) (shift : ℝ) :=
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 ((OriginalKBoundarySourceAction.actualBoundaryIntegralRead c stock.1.1 shift,
   OriginalKBoundarySourceAction.actualBoundaryIntegralRead c stock.1.2 shift),
  (OriginalKBoundarySourceAction.actualBoundaryIntegralRead c stock.2.1 shift,
   OriginalKBoundarySourceAction.actualBoundaryIntegralRead c stock.2.2 shift))

/-- Original B is read through its generated vector integral with both moving contact/mean windows. -/
theorem own_four_cotest_full_B_price (shift : ℝ) :
 let stock := ownPhysicalFaces observation nontrivial half depth ordinal h H N
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 ((inner ℂ stock.1.1 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift),
   inner ℂ stock.1.2 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift)),
  (inner ℂ stock.2.1 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift),
   inner ℂ stock.2.2 (burnolZeroPairedFixedAnnulusBoundary c observation.mathlibZero shift))) =
 boundaryFourRead observation nontrivial half stock shift := by
 let c := OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let stock := ownPhysicalFaces observation nontrivial half depth ordinal h H N
 have first := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.1 shift
 have second := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.1.2 shift
 have third := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.1 shift
 have fourth := OriginalKBoundarySourceAction.actual_boundary_integral_read c (show riemannZeta c.value=0 from observation.mathlibZero) stock.2.2 shift
 exact congrArg₂ (fun x y => (x,y)) (congrArg₂ (fun x y => (x,y)) first second) (congrArg₂ (fun x y => (x,y)) third fourth)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDecodedPaRFourFaceSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
