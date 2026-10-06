import H0mework.Versions.AB.Physics.LowEnergyActive.Triplet
import H0mework.Physics.Exterior.ExteriorMotherLieRepresentation

/-! Every original P286 direction acts on the same occupied exterior triplet. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open DiracCliffordRepresentation DiracExteriorMatterAction ActiveSector
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorBreakingYukawa StageNineExteriorMotherLieRepresentation StageNineHolonomicField
open StageNineP286GaugeConnectionVariation
open Stage9C.Material.SpinPair GaugeProjection.ConcreteBlockDiagonal
open scoped Matrix BigOperators
noncomputable section
local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

private theorem triplet_enumeration (color : Fin 3) (position : Fin 2) :
    Set.powersetCard.ofFinEmbEquiv.symm (colorTripletIndex color) position =
      if position=0 then Sum.inl color else hyperPlusIndex := by
  let family : Fin 2 → SU7MotherIndex := fun position => if position=0 then Sum.inl color else hyperPlusIndex
  have membership (position : Fin 2) : family position ∈ (colorTripletIndex color).1 := by
    by_cases zero : position=0 <;> simp [family,colorTripletIndex,zero]
  have unique : family=(colorTripletIndex color).1.orderEmbOfFin (colorTripletIndex color).prop := by
    apply Finset.orderEmbOfFin_unique _ membership
    intro first second ordered
    fin_cases first <;> fin_cases second
    all_goals try norm_num at ordered
    change smBlockIndexEquivFin7 (Sum.inl color)<smBlockIndexEquivFin7 hyperPlusIndex
    fin_cases color <;> decide
  exact (congrFun unique position).symm

theorem triplet_basis_wedge (color : Fin 3) :
    su7ExteriorBasis 2 (colorTripletIndex color) =
      (exteriorPower.ιMulti ℂ 2) ![su7FundamentalBasis (Sum.inl color),su7FundamentalBasis hyperPlusIndex] := by
  rw [← exteriorBasisInput_wedge_eq_basis_slot]
  apply congrArg (exteriorPower.ιMulti ℂ 2)
  funext position
  fin_cases position <;> simp [exteriorBasisInput,exteriorPositionEquiv,triplet_enumeration]

theorem p286_fundamental_color (data : P286LieBlockData) (color : Fin 3) :
    fundamentalMotherLieAction (p286LieBlockEmbed data) (su7FundamentalBasis (Sum.inl color)) =
      ∑ target : Fin 3, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) target color • su7FundamentalBasis (Sum.inl target) := by
  ext row
  rcases row with c | w | p | m
  all_goals simp [fundamentalMotherLieAction,su7FundamentalBasis,p286LieBlockEmbed,rawP286LieBlock,
    weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,Matrix.mulVecLin,Matrix.mulVec,dotProduct,
    Pi.single_apply,mul_ite]

theorem p286_fundamental_hyper (data : P286LieBlockData) :
    fundamentalMotherLieAction (p286LieBlockEmbed data) (su7FundamentalBasis hyperPlusIndex) =
      data.2.2.1 • su7FundamentalBasis hyperPlusIndex := by
  ext row
  rcases row with c | w | p | m
  all_goals try fin_cases p
  all_goals simp [fundamentalMotherLieAction,su7FundamentalBasis,p286LieBlockEmbed,rawP286LieBlock,
    weakHyperchargeLieBlock,hyperchargeLieBlock,scalarLieBlock,Matrix.mulVecLin,Matrix.mulVec,dotProduct,
    hyperPlusIndex,Pi.single_apply,mul_ite]

theorem p286_exterior_triplet (data : P286LieBlockData) (color : Fin 3) :
    exteriorMotherLieAction 2 (p286LieBlockEmbed data) (su7ExteriorBasis 2 (colorTripletIndex color)) =
      (∑ target : Fin 3, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) target color •
        su7ExteriorBasis 2 (colorTripletIndex target)) +
        data.2.2.1 • su7ExteriorBasis 2 (colorTripletIndex color) := by
  rw [triplet_basis_wedge,exteriorMotherLieAction_eq_slotDerivedAction,
    exteriorSlotDerivedAction_apply_ιMulti,Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [p286_fundamental_color,p286_fundamental_hyper]
  rw [(exteriorPower.ιMulti ℂ 2).map_update_sum]
  simp_rw [(exteriorPower.ιMulti ℂ 2).map_update_smul]
  have updated (target : Fin 3) :
      Function.update ![su7FundamentalBasis (Sum.inl color),su7FundamentalBasis hyperPlusIndex]
        0 (su7FundamentalBasis (Sum.inl target)) =
      ![su7FundamentalBasis (Sum.inl target),su7FundamentalBasis hyperPlusIndex] := by
    funext position
    fin_cases position <;> simp
  simp_rw [updated,← triplet_basis_wedge]
  congr 1
  congr 1
  rw [triplet_basis_wedge]
  apply congrArg (exteriorPower.ιMulti ℂ 2)
  funext position
  fin_cases position <;> simp

theorem p286_colorTripletMatter (data : P286LieBlockData) (color : Fin 3) :
    exteriorSpinorMotherLieAction (p286LieBlockEmbed data) (colorTripletMatter color) =
      (∑ target : Fin 3, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) target color • colorTripletMatter target) +
        data.2.2.1 • colorTripletMatter color := by
  simp only [exteriorSpinorMotherLieAction,colorTripletMatter,LinearMap.prodMap_apply,map_zero]
  rw [p286_exterior_triplet]
  apply Prod.ext
  · simp [Fin.sum_univ_three]
  · apply Prod.ext <;> simp [Fin.sum_univ_three]

theorem original_P286_triplet (data : P286LieBlockData)
    (coefficient : DiracSpinorIndex → Fin 3 → ℂ) :
    diracExteriorMotherLieAction (p286LieBlockEmbed data) (tripletMatter coefficient) =
      tripletMatter (fun spin target =>
        (∑ color, (data.1 : Matrix (Fin 3) (Fin 3) ℂ) target color * coefficient spin color) +
          data.2.2.1*coefficient spin target) := by
  funext spin
  change exteriorSpinorMotherLieAction (p286LieBlockEmbed data)
      (∑ color, coefficient spin color • colorTripletMatter color) = _
  simp only [map_sum,map_smul,p286_colorTripletMatter,smul_add,Finset.smul_sum,smul_smul,
    Finset.sum_add_distrib,tripletMatter,Finset.sum_smul,add_smul]
  rw [Finset.sum_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro target _
    apply Finset.sum_congr rfl
    intro color _
    rw [mul_comm]
  · apply Finset.sum_congr rfl
    intro target _
    rw [mul_comm]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
