import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFullSourceRResponse.Projection
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
open Complex MeasureTheory SourceGeneratedHilbertCokernel
open scoped InnerProductSpace
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
local instance forcingAmbientComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local instance forcingPaComplete : CompleteSpace BurnolPaOrthogonalCarrier := by
  apply IsComplete.completeSpace_coe
  exact burnolPaOrthogonalClosedFace.isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

def sourceResidual (h : ℝ) : BurnolPaOrthogonalCarrier :=
  residual burnolCompactCoPoissonLanding (P (completeSource observation nontrivial half h))

theorem source_residual_read (h : ℝ) :
    (sourceResidual observation nontrivial half h : BurnolPaAmbientCarrier)=
      Paid.Q (completeSource observation nontrivial half h) := rfl

/-- Both forcing channels are restrictions of the same actual raw source.
Only the paid Fourier action on its literal Pa residual is used. -/
theorem source_fourier_restriction (h : ℝ) :
    Paid.Q (fourierL2 (completeSource observation nontrivial half h))=
      (burnolCompactCoPoissonActionSquare.orthogonalAction (sourceResidual observation nontrivial half h) : BurnolPaAmbientCarrier) := by
  have physical : F (P (completeSource observation nontrivial half h))=
      P (fourierL2 (completeSource observation nontrivial half h)) := by
    apply Subtype.ext
    exact fourierL2_evenBurnolPhysicalProjection _ _
  have generated:=burnolCompactCoPoissonActionSquare.orthogonalAction_residual
    (P (completeSource observation nontrivial half h))
  change burnolCompactCoPoissonActionSquare.orthogonalAction (sourceResidual observation nontrivial half h)=
    residual burnolCompactCoPoissonLanding (F (P (completeSource observation nontrivial half h))) at generated
  rw [physical] at generated
  exact (congrArg (fun value : BurnolPaOrthogonalCarrier=>(value : BurnolPaAmbientCarrier)) generated).symm

theorem actual_complete_residual_forcing (h : ℝ) :
    HasDerivAt (fun t : ℝ=>Paid.Q (burnolMultiplicativeDilation (-t/2) (pairedResponse observation nontrivial half h)))
      ((observation.coordinate/2-1/4) • Paid.Q (siblingResponse observation nontrivial half h)+
        (1/2:ℂ) • ((sourceResidual observation nontrivial half h : BurnolPaAmbientCarrier)-
          (burnolCompactCoPoissonActionSquare.orthogonalAction (sourceResidual observation nontrivial half h) : BurnolPaAmbientCarrier))) 0 ∧
    HasDerivAt (fun t : ℝ=>Paid.Q (burnolMultiplicativeDilation (-t/2) (siblingResponse observation nontrivial half h)))
      ((observation.coordinate/2-1/4) • Paid.Q (pairedResponse observation nontrivial half h)+
        (1/2:ℂ) • ((sourceResidual observation nontrivial half h : BurnolPaAmbientCarrier)+
          (burnolCompactCoPoissonActionSquare.orthogonalAction (sourceResidual observation nontrivial half h) : BurnolPaAmbientCarrier))) 0 := by
  have generated:=actual_source_Q_forcing observation nontrivial half h
  rw [source_fourier_restriction,←source_residual_read] at generated
  exact generated

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRResponse
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

