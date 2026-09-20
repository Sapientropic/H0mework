import H0mework.Physics.SpinPair.Spinor

/-! The complete mother/P286 action compressed to the two occupied source
color states. Spectator currents are read from this same compression. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open DiracExteriorMatterAction ProofFreeRicherAnholonomicSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineSourceActionGeneratedP506MatterCurrentP286NonzeroCurvatureSynchronizedLocalActualLift
open SU7ExteriorBreakingYukawa SU7ExteriorMatterGaugeCovariantJet SU7ExteriorMatterRestriction
open SU7ExteriorMatterRepresentation SU7MotherLieAlgebra SU7MotherGaugeTheory
open GaugeProjection.ConcreteBlockDiagonal

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

private theorem sourceColorDoublet_enumeration (state position : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm (sourceColorDoubletIndex state) position =
      if position = 0 then Sum.inl (state.castLE (by decide)) else hyperPlusIndex := by
  let family : Fin 2 → SU7MotherIndex :=
    fun position => if position = 0 then Sum.inl (state.castLE (by decide)) else hyperPlusIndex
  have membership (position : Fin 2) : family position ∈ (sourceColorDoubletIndex state).1 := by
    by_cases zero : position = 0 <;> simp [family, sourceColorDoubletIndex, zero]
  have unique : family = (sourceColorDoubletIndex state).1.orderEmbOfFin
      (sourceColorDoubletIndex state).prop := by
    apply Finset.orderEmbOfFin_unique _ membership
    intro first second ordered
    fin_cases first <;> fin_cases second
    all_goals try (norm_num at ordered)
    change smBlockIndexEquivFin7 (Sum.inl (state.castLE (by decide))) <
      smBlockIndexEquivFin7 hyperPlusIndex
    fin_cases state <;> decide
  exact (congrFun unique position).symm

private theorem sourceColorDoublet_position (state position : Fin 2) :
    (exteriorPositionEquiv (sourceColorDoubletIndex state) position).1 =
      if position = 0 then Sum.inl (state.castLE (by decide)) else hyperPlusIndex :=
  sourceColorDoublet_enumeration state position

theorem sourceColorDoublet_basisActionCoefficient
    (matrix : SU7MotherLieMatrix) (row column : Fin 2) :
    (su7ExteriorBasis 2).repr
      (exteriorMotherLieAction 2 matrix (su7ExteriorBasis 2 (sourceColorDoubletIndex column)))
      (sourceColorDoubletIndex row) =
      (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        (Sum.inl (row.castLE (by decide))) (Sum.inl (column.castLE (by decide))) +
      if row = column then (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
        hyperPlusIndex hyperPlusIndex else 0 := by
  rw [exteriorMotherLieAction_basis_current]
  unfold exteriorBasisLieAction
  rw [map_sum]
  change (∑ position : Fin 2, (su7ExteriorBasis 2).repr
    ((exteriorPower.ιMulti ℂ 2)
      (exteriorBasisLieActionInput 2 matrix (sourceColorDoubletIndex column) position))
      (sourceColorDoubletIndex row)) = _
  simp_rw [exteriorBasisLieActionTerm_eq_update]
  unfold su7ExteriorBasis
  simp_rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.det_fin_two, Fin.sum_univ_two, exteriorBasisInput,
      sourceColorDoublet_position, sourceColorDoublet_enumeration,
      fundamentalMotherLieAction, Matrix.mulVecLin, su7FundamentalBasis, Fin.castLE, hyperPlusIndex]

theorem sourceColorDoublet_p286ActionCoefficient
    (data : P286LieBlockData) (row column : Fin 2) :
    sourceColorDoubletDual row
      (exteriorSpinorMotherLieAction (p286LieBlockEmbed data) (sourceColorDoubletMatter column)) =
      (data.1 : Matrix (Fin 3) (Fin 3) ℂ) (row.castLE (by decide)) (column.castLE (by decide)) +
        if row = column then data.2.2.1 else 0 := by
  change (su7ExteriorBasis 2).repr
    (exteriorMotherLieAction 2 (p286LieBlockEmbed data)
      (su7ExteriorBasis 2 (sourceColorDoubletIndex column))) (sourceColorDoubletIndex row) = _
  rw [sourceColorDoublet_basisActionCoefficient]
  rfl

theorem sourceColorDoublet_basis_wedge (state : Fin 2) :
    su7ExteriorBasis 2 (sourceColorDoubletIndex state) =
      (exteriorPower.ιMulti ℂ 2)
        ![su7FundamentalBasis (Sum.inl (state.castLE (by decide))), su7FundamentalBasis hyperPlusIndex] := by
  rw [← exteriorBasisInput_wedge_eq_basis_current]
  apply congrArg (exteriorPower.ιMulti ℂ 2)
  funext position
  fin_cases position <;> simp [exteriorBasisInput, sourceColorDoublet_position]

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
