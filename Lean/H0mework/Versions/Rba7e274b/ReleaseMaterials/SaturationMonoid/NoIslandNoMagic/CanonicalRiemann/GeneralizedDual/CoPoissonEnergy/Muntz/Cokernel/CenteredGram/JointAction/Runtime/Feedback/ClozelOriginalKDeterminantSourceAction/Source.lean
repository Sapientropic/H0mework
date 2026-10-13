import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCountingSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
open Complex MeasureTheory Filter FourierTransform
open scoped InnerProductSpace Topology
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState OriginalPaPhysicalGreen
local instance characterActionComplete : CompleteSpace BurnolPaAmbientCarrier :=by
 apply IsComplete.completeSpace_coe
 exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "K" => burnolCompletedMellinRieszVector
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "H" => OriginalKCommonGapKernelSource.actualCommonField
local notation "velocity" => OriginalKCommonGapKernelSource.actualCommonVelocity


variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half:OriginalKCombCalculation.Half observation)
local notation "c" => (OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half)

/-- This reads the original evaluator-generated nonzero physical state at the same observation. -/
theorem actual_original_source_kernel_ne_zero:(K c:BurnolL2)≠0 :=by
 have generated:=(OriginalRieszSource.Kernel.zero_owned_response observation nontrivial half.down).1
 intro zero
 apply generated
 apply Subtype.ext
 apply Subtype.ext
 exact zero

/-- The actual self Green form pays both contact factors without assuming either target factor. -/
theorem actual_original_source_contact_factors:
 OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c≠0 ∧
 OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c≠0 :=by
 have source:=OriginalRieszSourceGreen.original_kernel_gram c c
 have rate:=OriginalRieszSourceGreen.source_cross_parameter_ne_zero c c
 have kernel:=actual_original_source_kernel_ne_zero observation nontrivial half
 constructor
 · intro zero
   have same:OriginalRieszSource.Kernel.A c=OriginalRieszSource.Kernel.beta c:=sub_eq_zero.mp zero
   rw [same,sub_self,mul_zero] at source
   have paid:inner ℂ (K c:BurnolL2) (K c:BurnolL2)=0:=(mul_eq_zero.mp source).resolve_left rate
   exact kernel (inner_self_eq_zero.mp paid)
 · intro zero
   have same:OriginalRieszSource.Kernel.A c=-OriginalRieszSource.Kernel.beta c:=eq_neg_of_add_eq_zero_left zero
   rw [same] at source
   simp only [star_neg,neg_mul_neg,sub_self,mul_zero] at source
   have paid:inner ℂ (K c:BurnolL2) (K c:BurnolL2)=0:=(mul_eq_zero.mp source).resolve_left rate
   exact kernel (inner_self_eq_zero.mp paid)

/-- The original determinant is a source unit, generated after the full same-source self Green law. -/
theorem actual_original_common_determinant_ne_zero:
 OriginalKCommonGapKernelSource.actualCommonDeterminant c≠0 :=by
 have source:=actual_original_source_contact_factors observation nontrivial half
 have literal:OriginalKCommonGapKernelSource.actualCommonDeterminant c=
  (OriginalRieszSource.Kernel.A c-OriginalRieszSource.Kernel.beta c)*
  (OriginalRieszSource.Kernel.A c+OriginalRieszSource.Kernel.beta c):=by
  unfold OriginalKCommonGapKernelSource.actualCommonDeterminant
  ring
 rw [literal]
 exact mul_ne_zero source.1 source.2

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKCharacterActionSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
