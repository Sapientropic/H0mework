import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.ContactReceipt

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFiniteSource OriginalKSourceResolventReconstruction
open OriginalRieszFinitePairing.CoPoisson.Ward
open scoped InnerProductSpace

/-- Keeping only the translated endpoint loses the complete exponential base field. -/
theorem contact_endpoint_delete_base (coordinate : BurnolCompletedMellinCoordinate) (shift : ℝ) :
    nativeIntegral (sourceRate coordinate) (fourierL2 ConstantDual.seed) shift -
        burnolMultiplicativeDilation shift (fourierL2 (contactPrimitive coordinate)) =
      -Complex.exp (-sourceRate coordinate * (shift : ℂ)) • fourierL2 (contactPrimitive coordinate) := by
  rw [contact_primitive_endpoint,contactEndpointSource]
  module

theorem contact_endpoint_zero_keeps_source (coordinate : BurnolCompletedMellinCoordinate) :
    contactEndpointSource coordinate 0 = 0 ∧ type_of% (contactPrimitive_fourier_euler coordinate) := by
  refine ⟨?_,contactPrimitive_fourier_euler coordinate⟩
  simp only [contactEndpointSource,burnolMultiplicativeDilation_zero,Complex.ofReal_zero,mul_zero,
    Complex.exp_zero,one_smul,sub_self]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => Real.log stageZeroSonineQ
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

include depth ordinal in
/-- The old actual omission price now consumes both complete compact-power endpoint updates. -/
theorem actual_endpoint_contact_omission_price :
    (receipt).fixedResidual + inner ℂ (receipt).kernel (boundaryWithoutSecondContact c h) =
      (sourceCoefficients c 1 * sourceRate c) * inner ℂ (receipt).kernel
        (contactEndpointSource c h + contactEndpointSource c (-h)) := by
  have price := actual_delete_second_contact_price observation nontrivial half depth ordinal
  rw [contact_primitive_endpoint,contact_primitive_endpoint] at price
  exact price

/-- Both generations of actual omission/override controls accompany the same original whole-next consumer. -/
theorem actual_contact_source_gate :
    type_of% (actual_contact_source_on_original_whole_next observation nontrivial half depth ordinal) ∧
    type_of% (contact_endpoint_delete_base c h) ∧
    type_of% (actual_endpoint_contact_omission_price observation nontrivial half depth ordinal) ∧
    type_of% (contact_endpoint_zero_keeps_source c) :=
  ⟨actual_contact_source_on_original_whole_next observation nontrivial half depth ordinal,
    contact_endpoint_delete_base c h,actual_endpoint_contact_omission_price observation nontrivial half depth ordinal,
    contact_endpoint_zero_keeps_source c⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_contact_source_gate"

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKSourceFiniteUpdate
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
