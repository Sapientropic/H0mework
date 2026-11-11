import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterSource
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.PaAdjointReceipt

set_option autoImplicit false
set_option Elab.async false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
open Complex MeasureTheory Set BurnolPhysicalState
open OriginalKFullAdjointSource OriginalKDirectRCofinalMaterial
open OriginalRieszFinitePairing.CoPoisson.Ward SourceOperationScalarInventoryLift
open scoped InnerProductSpace
local notation "S" => burnolMeanZeroTruncatedFourier
local instance hReceiptGroups (grade : Nat) (target : Unit) :
    AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "H" => sourceAdjointField c
local notation "raw" => D.raw observation nontrivial half depth ordinal
local notation "rawNext" => D.raw observation nontrivial half depth (ordinal+1)
local notation "g" => sourceOutsideColumn c raw
local notation "receiptK" => (installedOriginalKReceiptAt observation nontrivial half.down).kernel
local notation "alpha" => OriginalKDirectRCofinalDivision.sourceCoefficient observation nontrivial half depth (ordinal+1)
local notation "Qunit" => (OriginalKDirectRCofinalDivision.sourceUnit observation nontrivial half : BurnolL2)
local notation "born" => D.packet observation nontrivial half depth ((ordinal+1)+1)
local notation "bornValue" => CF.collapseValue born.1 (born.2.1.1.activeEnvironment () (),0)
local notation "bornRaw" => (bornValue.1.1+bornValue.1.2)+(bornValue.2.1+bornValue.2.2)
local notation "powerPrice" => star (hQuarterAmplitude c)*inner ℂ (SingularCounting.centeredPower c) (S g)

/-- Local source equations act on the same actual invisible and born reads, without enlarging their whole receipt. -/
def consume_actual_h_quarter {Result : Sort u}
    (consumer :
      (quarterCotest H=hQuarterField c) →
      (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
        inner ℂ (qAdjointSource c) rawNext+inner ℂ (outsideCotest H) g) →
      (inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
        inner ℂ (qAdjointSource c) rawNext-inner ℂ (quarterCotest H) (S g)) → Result) : Result :=
  consumer (h_quarter_source c)
    (actual_pa_q_adjoint_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.1
    (actual_pa_q_adjoint_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.2.2

/-- The actual Volterra quarter source is consumed in the original whole, its same born, and the actual Q successor. -/
theorem actual_h_quarter_on_original_whole_next :
    type_of% (actual_pa_q_adjoint_on_original_whole_next observation nontrivial half depth ordinal) ∧
    (quarterCotest H=hQuarterField c) ∧
    (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
      inner ℂ (qAdjointSource c) rawNext-powerPrice) ∧
    (inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
      inner ℂ (qAdjointSource c) rawNext-powerPrice) ∧
    type_of% (actual_nextQ_power_source observation nontrivial half depth ordinal) := by
  refine ⟨actual_pa_q_adjoint_on_original_whole_next observation nontrivial half depth ordinal,?_⟩
  apply consume_actual_h_quarter observation nontrivial half depth ordinal
  intro vector invisible bornRead
  have completePrice : inner ℂ (outsideCotest H) g= -powerPrice := by
    rw [outside_price_from_position_source,vector,hQuarterField,inner_smul_left]
    simp only [starRingEnd_apply]
  rw [completePrice] at invisible
  rw [vector,hQuarterField,inner_smul_left] at bornRead
  refine ⟨vector,?_,?_,actual_nextQ_power_source observation nontrivial half depth ordinal⟩
  · simpa only [sub_eq_add_neg] using invisible
  · exact bornRead

-- This explicit whole receipt stays fully visible to the kernel and audits; omit only automatic premise suggestions.
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_h_quarter_on_original_whole_next"

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
