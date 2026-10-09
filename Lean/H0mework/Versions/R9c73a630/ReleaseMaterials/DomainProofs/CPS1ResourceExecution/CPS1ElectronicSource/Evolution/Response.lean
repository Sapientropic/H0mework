import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Evolution.Native

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution.Native
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing Stage10.ChargedPreparation
open scoped InnerProductSpace
noncomputable section

def weightedPreparation (weight : ℂ) : Mother := weight • preparation

theorem weighted_prepared (weight : ℂ) (point : BasePoint) :
    operator (weightedPreparation weight) (YangMills.FullPairing.prepared point) =
      preparedSection weight point := by
  simp [operator,weightedPreparation,preparedSection]

theorem generated_charge_response (first second : ℂ) (point : BasePoint) :
    State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (responseMatrix (pairedMother (weightedPreparation first)
        (chargeMother.comp (weightedPreparation second)))) = -(star first * second) := by
  rw [source_gram,weighted_prepared]
  have action : operator (chargeMother.comp (weightedPreparation second))
      (YangMills.FullPairing.prepared point) =
      operator chargeMother (preparedSection second point) := by
    simp [operator,weightedPreparation,preparedSection]
  rw [action,native_charge]

variable {slots : Type*} [Fintype slots]
theorem generated_complete_response (weights : slots → ℂ) (point : BasePoint) :
    (∑ slot, State.vectorEvaluation (Stage10.Runtime.tick.answer point)
      (responseMatrix (pairedMother (weightedPreparation (weights slot))
        (chargeMother.comp (weightedPreparation (weights slot)))))) = -density weights := by
  simp only [generated_charge_response,density,Finset.sum_neg_distrib]

end
end CPS1ElectronicEvolution.Native
