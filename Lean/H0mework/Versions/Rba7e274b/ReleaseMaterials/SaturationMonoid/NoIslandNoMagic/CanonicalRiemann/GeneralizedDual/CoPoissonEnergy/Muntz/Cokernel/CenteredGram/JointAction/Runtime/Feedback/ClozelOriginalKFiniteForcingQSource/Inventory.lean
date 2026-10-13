import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteForcingQSource.Face
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance inventoryAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "OP" => burnolCompactCoPoissonClosedRange.toSubmodule.orthogonal.starProjection
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def actualFinitePaStock (h : ℝ) : BurnolPaAmbientCarrier :=
 OriginalKCombCofinalPaAction.E (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)+
 OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
 OriginalKCombCofinalPaAction.E (Paid.originalForcingPair observation nontrivial half h)

def actualFiniteOutsideStock (h : ℝ) : BurnolL2 :=
 Paid.originalOutside (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)+
 OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
 Paid.originalOutside (Paid.originalForcingPair observation nontrivial half h)

private theorem full_stock (material : BurnolL2) :
 material=(Q material : BurnolL2)+(OriginalKCombCofinalPaAction.E material : BurnolL2)+Paid.originalOutside material := by
 have physical:=(evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.starProjection_add_starProjection_orthogonal material
 have inside:=congrArg (fun face : BurnolPaAmbientCarrier=>(face : BurnolL2))
   (burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal (P material))
 change (P material : BurnolL2)+Paid.originalOutside material=material at physical
 change (OriginalKCombCofinalPaAction.E material : BurnolL2)+(Q material : BurnolL2)=(P material : BurnolL2) at inside
 calc
  material=(P material : BurnolL2)+Paid.originalOutside material := physical.symm
  _ = (OriginalKCombCofinalPaAction.E material : BurnolL2)+(Q material : BurnolL2)+Paid.originalOutside material := by rw [inside]
  _ = _ := by abel

/-- The actual original finite forcing source is restored before R acts; both omitted inventories remain. -/
theorem actual_full_finite_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKFullSourceRResponse.completeSource observation nontrivial half h=
 -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • Paid.originalForcingPair observation nontrivial half h+
 (actualFinitePaStock observation nontrivial half h : BurnolL2)+actualFiniteOutsideStock observation nontrivial half h := by
 have physical:=congrArg (fun face : BurnolPaAmbientCarrier=>(face : BurnolL2))
   (actual_complete_finite_forcing_face observation nontrivial half h nonnegative bounded)
 simp only [Submodule.coe_smul] at physical
 have complete:=full_stock (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)
 have forcing:=full_stock (Paid.originalForcingPair observation nontrivial half h)
 unfold actualFinitePaStock actualFiniteOutsideStock
 simp only [Submodule.coe_add,Submodule.coe_smul]
 rw [physical] at complete
 linear_combination (norm:=module) complete+OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h • forcing

/-- Original R consumes the complete real source inventory, after the actual common physical face was generated. -/
theorem actual_R_finite_source (h : ℝ) (nonnegative : 0≤h) (bounded : h≤Real.log 2) :
 OriginalKFullSourceRResponse.Op.R observation nontrivial half
   (OriginalKFullSourceRResponse.completeSource observation nontrivial half h)=
 -OriginalCommonInverseForcing.SourceJoint.upperSeedFactor h •
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (Paid.originalForcingPair observation nontrivial half h)+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFinitePaStock observation nontrivial half h : BurnolL2)+
 OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFiniteOutsideStock observation nontrivial half h) := by
 have source:=congrArg (fun material : BurnolL2=>OriginalKFullSourceRResponse.Op.R observation nontrivial half material)
   (actual_full_finite_source observation nontrivial half h nonnegative bounded)
 simpa only [map_add,map_smul] using source

private theorem actual_finite_Pa_qualification (h : ℝ) :
 actualFinitePaStock observation nontrivial half h ∈ burnolCompactCoPoissonClosedRange := by
 have complete:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_apply_mem
   (P (OriginalKFullSourceRResponse.completeSource observation nontrivial half h))
 have forcing:=burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_apply_mem
   (P (Paid.originalForcingPair observation nontrivial half h))
 exact burnolCompactCoPoissonClosedRange.toSubmodule.add_mem complete
   (burnolCompactCoPoissonClosedRange.toSubmodule.smul_mem _ forcing)

/-- The stock's own Pa qualification produces both true original K/FK unit-tail prices. -/
theorem actual_R_finite_Pa_prices (h : ℝ) :
 (inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFinitePaStock observation nontrivial half h : BurnolL2))=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (actualFinitePaStock observation nontrivial half h)*
 inner ℂ (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2)
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) ∧
 (inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (OriginalKFullSourceRResponse.Op.R observation nontrivial half (actualFinitePaStock observation nontrivial half h : BurnolL2))=
 burnolPaResolventSourceCoefficient (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)
   (actualFinitePaStock observation nontrivial half h)*
 inner ℂ (fourierL2 (burnolCompletedMellinRieszVector (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) : BurnolL2))
   (burnolUnitTailResponse (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half) 4)) := by
 let coordinate:=OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
 let k : BurnolPaOrthogonalCarrier:=⟨burnolCompletedMellinRieszVector coordinate,
   riemannZeta_zero_burnolCompletedMellinRieszVector_mem_Pa_orthogonal coordinate observation.mathlibZero⟩
 have left:=burnolPaResolvent_source_pairing coordinate (actualFinitePaStock observation nontrivial half h)
   (actual_finite_Pa_qualification observation nontrivial half h) k
 have right:=burnolPaResolvent_source_pairing coordinate (actualFinitePaStock observation nontrivial half h)
   (actual_finite_Pa_qualification observation nontrivial half h) (burnolCompactCoPoissonActionSquare.orthogonalAction k)
 change inner ℂ (fourierL2 (burnolCompletedMellinRieszVector coordinate : BurnolL2))
   (burnolDirectRightResolvent (coordinate.value/2) (actualFinitePaStock observation nontrivial half h : BurnolL2))=_ at right
 rw [OriginalKCombCofinalRAction.original_R_direct]
 rw [OriginalKCombCofinalTwoDirection.coordinate_value] at left right
 exact ⟨left,right⟩


end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteForcingQSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
