import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HProjectionSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.HQuarterReceipt

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
local instance hProjectionReceiptGroups (grade : Nat) (target : Unit) :
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

/-- Complete source realization and its actual loss act on the original mathematical reads. -/
def consume_actual_h_projection {Result : Sort u}
    (consumer :
      (hQField c=qAdjointSource c) →
      ((burnolEvenAmbientProjection H : BurnolL2)=hPhysicalField c) →
      (H-(burnolEvenAmbientProjection H : BurnolL2)=hQuarterAmplitude c • hPowerPhysicalCorrection c) →
      (‖H‖^2-‖hPhysicalField c‖^2=‖hQuarterAmplitude c‖^2*‖hPowerPhysicalCorrection c‖^2) →
      (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
        inner ℂ (qAdjointSource c) rawNext-powerPrice) →
      (inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
        inner ℂ (qAdjointSource c) rawNext-powerPrice) → Result) : Result :=
  consumer (hQField_eq_paid c) (hPhysicalField_actual c) (h_projection_loss_source c) (h_projection_loss_energy c)
    (actual_h_quarter_on_original_whole_next observation nontrivial half depth ordinal).2.2.1
    (actual_h_quarter_on_original_whole_next observation nontrivial half depth ordinal).2.2.2.1

/-- The original whole and born consume a fixed B column, the full source vectors, and their actual projection cost. -/
theorem actual_h_projection_on_original_whole_next :
    type_of% (actual_h_quarter_on_original_whole_next observation nontrivial half depth ordinal) ∧
    ((burnolEvenAmbientProjection H : BurnolL2)=hPhysicalField c) ∧
    ((PA.Q H : BurnolL2)=hQField c) ∧
    (H-(burnolEvenAmbientProjection H : BurnolL2)=hQuarterAmplitude c • hPowerPhysicalCorrection c) ∧
    (‖H‖^2-‖hPhysicalField c‖^2=‖hQuarterAmplitude c‖^2*‖hPowerPhysicalCorrection c‖^2) ∧
    (inner ℂ receiptK (P.R observation nontrivial half (PA.invisible rawNext))=
      inner ℂ (hQField c) rawNext-powerPrice) ∧
    (inner ℂ receiptK bornRaw=alpha*inner ℂ receiptK Qunit+
      inner ℂ (hQField c) rawNext-powerPrice) ∧
    type_of% (actual_nextQ_B_power_source observation nontrivial half depth ordinal) := by
  have prior := actual_h_quarter_on_original_whole_next observation nontrivial half depth ordinal
  refine ⟨prior,?_⟩
  apply consume_actual_h_projection observation nontrivial half depth ordinal
  intro qField physical loss energy invisible bornRead
  have actualQ := prior.1.2.2.1
  rw [←qField] at actualQ invisible bornRead
  exact ⟨physical,actualQ,loss,energy,invisible,bornRead,
    actual_nextQ_B_power_source observation nontrivial half depth ordinal⟩

run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_h_projection_on_original_whole_next"

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalOutsideVolterraSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
