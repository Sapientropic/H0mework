import H0mework.Versions.AB.Physics.MotherSource.ChargedPreparation.Classical
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 0
namespace CPS1ElectronicEvolution.Native
open SaturationMonoid.PhysicsCore
open ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open Stage9C.Material.SpinPair Stage9DEF Stage9DEF.Compatibility
open YangMills.FullPairing Stage10.ChargedPreparation
open scoped InnerProductSpace
noncomputable section

def preparedSection (weight : ℂ) (point : BasePoint) : Hilbert :=
  weight • operator preparation (YangMills.FullPairing.prepared point)

theorem native_pair (first second : ℂ) (point : BasePoint) :
    inner ℂ (preparedSection first point) (preparedSection second point) = star first * second := by
  simp only [preparedSection,inner_smul_left,inner_smul_right,full_prepared_inner,mul_one]
  exact mul_comm _ _

theorem native_charge (first second : ℂ) (point : BasePoint) :
    inner ℂ (preparedSection first point) (operator chargeMother (preparedSection second point)) =
      -(star first * second) := by
  simp only [preparedSection,map_smul,inner_smul_left,inner_smul_right,full_charge_pair,starRingEnd_apply]
  ring

def classicalPair (first second : ℂ) (point : BasePoint) : ℂ :=
  star first * second * actual.conjugateMatter point
    (dualPreparation (currentAction 0 Stage10.HyperchargeResponse.chargeDirection
      (preparation (actual.matter point))))

theorem native_classical_current (first second : ℂ) (point : BasePoint) :
    classicalPair first second point =
      (4 * (spinScale : ℂ)) *
        inner ℂ (preparedSection first point) (operator chargeMother (preparedSection second point)) := by
  rw [classicalPair,classical_current,native_charge]
  ring

variable {slots : Type*} [Fintype slots]
def density (weights : slots → ℂ) : ℂ := ∑ slot, star (weights slot) * weights slot

def charge (weights : slots → ℂ) (point : BasePoint) : ℂ :=
  ∑ slot, inner ℂ (preparedSection (weights slot) point)
    (operator chargeMother (preparedSection (weights slot) point))

theorem complete_charge (weights : slots → ℂ) (point : BasePoint) :
    charge weights point = -density weights := by
  simp only [charge,density,native_charge,Finset.sum_neg_distrib]

def current (weights : slots → ℂ) (point : BasePoint) : ℂ :=
  ∑ slot, classicalPair (weights slot) (weights slot) point

theorem complete_current (weights : slots → ℂ) (point : BasePoint) :
    current weights point = (4 * (spinScale : ℂ)) * charge weights point := by
  simp only [current,charge,native_classical_current,Finset.mul_sum]

end
end CPS1ElectronicEvolution.Native
