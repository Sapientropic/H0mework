import H0mework.Physics.DiracEvolution.SafeSymmetricHyperbolicAllOrderEnergyRate
import Mathlib.Data.Fintype.Sigma

/-!
# Fixed P506/L0 whole-order energy hierarchy

All spatial words through one finite order are assembled before the energy
consumer is selected.  The same source constant controls every hierarchy
order, so the later regularity induction has one carrier and one energy law.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy

open Set
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedAction
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedEnergyRate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterCommutedPrincipal
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderCommutator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyRate
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterTemporalJetReduction
open StageNineHolonomicField
open StageNineMatterCoordinateFirstOrderCommutator
open ProofFreeRicherAnholonomicSource

noncomputable section

set_option autoImplicit false

/-- All spatial words of length at most `order`, in one finite carrier. -/
def FixedMatterSpatialWordIndex (order : ℕ) :=
  Sigma fun length : Fin (order + 1) => Fin length.1 → Fin 3

instance fixedMatterSpatialWordIndexFintype (order : ℕ) :
    Fintype (FixedMatterSpatialWordIndex order) := by
  unfold FixedMatterSpatialWordIndex
  infer_instance

def FixedMatterSpatialWordIndex.toList
    {order : ℕ} (word : FixedMatterSpatialWordIndex order) : List (Fin 3) :=
  List.ofFn word.2

def fixedMatterAllOrderWordValue
    {order : ℕ}
    (word : FixedMatterSpatialWordIndex order)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedSpatialWordDerivative word.toList field
    (diracMatterSpacetimeCoordinatePoint time space)

def fixedMatterAllOrderWordForcing
    {order : ℕ}
    (word : FixedMatterSpatialWordIndex order)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  fixedMatterAllOrderVolterraForcing word.toList field
    (diracMatterSpacetimeCoordinatePoint time space)

/-- Complete pointwise energy of every spatial word through one order. -/
def fixedMatterAllOrderPointwiseEnergy
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    fixedCoordinatePointwiseEnergy time space
      (fixedMatterAllOrderWordValue word field time space)

/-- Complete squared forcing budget of every spatial word through one order. -/
def fixedMatterAllOrderPointwiseForcingBudget
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2

/-- Whole-order magnitude of the forced energy-rate identity. -/
def fixedMatterAllOrderPointwiseRateMagnitude
    (order : ℕ)
    (field : BasePoint → MatterCoordinateCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  ∑ word : FixedMatterSpatialWordIndex order,
    ‖fixedCoordinatePointwiseRate time space
          (fixedMatterAllOrderWordValue word field time space) +
        2 * fixedCoordinatePointwiseMassPairing time space
          (fixedMatterAllOrderWordForcing word field time space)
          (fixedMatterAllOrderWordValue word field time space)‖

/-- One source constant controls the complete finite hierarchy at every
order.  `order` changes only the finite carrier being summed. -/
theorem exists_fixedMatterAllOrderPointwiseHierarchyBoundOnBox
    (timeStart timeEnd : ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (timeOrder : timeStart ≤ timeEnd)
    (boxOrder : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (order : ℕ)
        (field : BasePoint → MatterCoordinateCarrier),
        ∀ time ∈ Icc timeStart timeEnd,
          ∀ space ∈ Icc a b,
            fixedMatterAllOrderPointwiseRateMagnitude
                order field time space ≤
              K * (fixedMatterAllOrderPointwiseEnergy
                  order field time space +
                fixedMatterAllOrderPointwiseForcingBudget
                  order field time space) := by
  obtain ⟨K, KNonnegative, bound⟩ :=
    exists_fixedMatterAllOrderEnergyRateBoundOnBox
      timeStart timeEnd a b timeOrder boxOrder
  refine ⟨K, KNonnegative, ?_⟩
  intro order field time timeMem space spaceMem
  unfold fixedMatterAllOrderPointwiseRateMagnitude
    fixedMatterAllOrderPointwiseEnergy
    fixedMatterAllOrderPointwiseForcingBudget
  calc
    (∑ word : FixedMatterSpatialWordIndex order,
      ‖fixedCoordinatePointwiseRate time space
            (fixedMatterAllOrderWordValue word field time space) +
          2 * fixedCoordinatePointwiseMassPairing time space
            (fixedMatterAllOrderWordForcing word field time space)
            (fixedMatterAllOrderWordValue word field time space)‖) ≤
        ∑ word : FixedMatterSpatialWordIndex order,
          K * (fixedCoordinatePointwiseEnergy time space
              (fixedMatterAllOrderWordValue word field time space) +
            ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro word _
      exact bound word.toList field time timeMem space spaceMem
    _ = K * ((∑ word : FixedMatterSpatialWordIndex order,
          fixedCoordinatePointwiseEnergy time space
            (fixedMatterAllOrderWordValue word field time space)) +
        ∑ word : FixedMatterSpatialWordIndex order,
          ‖fixedMatterAllOrderWordForcing word field time space‖ ^ 2) := by
      rw [mul_add, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro word _
      ring

/-- On the mother-action zero fiber, the hierarchy forcing is exactly the
source coefficient commutator in every word coordinate. -/
theorem fixedMatterAllOrderWordForcing_of_actionZero
    {order : ℕ}
    (word : FixedMatterSpatialWordIndex order)
    (field : BasePoint → MatterCoordinateCarrier)
    (actionZero : ∀ point,
      matterCoordinateFirstOrderOperator
        fixedEvolutionPrincipalCoordinateCLM fixedMatterLowerCoefficient
        field point = 0)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    fixedMatterAllOrderWordForcing word field time space =
      -fixedEvolutionTemporalPrincipalInverseCoordinateCLM
        (diracMatterSpacetimeCoordinatePoint time space)
        (fixedMatterAllOrderCommutedForcing word.toList field
          (diracMatterSpacetimeCoordinatePoint time space)) := by
  exact fixedMatterAllOrderVolterraForcing_of_actionZero
    word.toList field actionZero
      (diracMatterSpacetimeCoordinatePoint time space)

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeFixedP506CauchySafeMatterSymmetricHyperbolicAllOrderEnergyHierarchy
