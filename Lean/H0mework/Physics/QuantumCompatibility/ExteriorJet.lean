import H0mework.Physics.QuantumCompatibility.ConnectionJet
import Mathlib.Analysis.Calculus.FDeriv.ContinuousMultilinearMap

/-! Exterior-matter coordinates read the derivative of the same full source
transport. The derivative is the existing mother Lie slot action. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility

open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open SU7MotherLieAlgebra SU7ExteriorMatterRepresentation SU7ExteriorMatterRestriction
open SU7ExteriorMatterGaugeCovariantJet StageNineExteriorMotherLieRepresentation
open StageNineP286GaugeConnectionVariation
open DiracExteriorMatterLocalGaugeLink
open GaugeProjection.ConcreteBlockDiagonal
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

local instance : LinearOrder SU7MotherIndex :=
  LinearOrder.lift' smBlockIndexEquivFin7 smBlockIndexEquivFin7.injective

def exteriorCoordinateForm (degree : ℕ) (coordinate : ExteriorBasisIndex degree) :
    ContinuousMultilinearMap ℂ (fun _ : Fin degree => SU7FundamentalCarrier) ℂ where
  toMultilinearMap := ((su7ExteriorBasis degree).coord coordinate).compMultilinearMap
    (exteriorPower.ιMulti ℂ degree).toMultilinearMap
  cont := by
    change Continuous (fun vectors => (su7ExteriorBasis degree).repr
      ((exteriorPower.ιMulti ℂ degree) vectors) coordinate)
    simp only [su7ExteriorBasis, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti]
    fun_prop

private theorem fundamentalTransport_hasDerivAt (point : BasePoint) (direction : LorentzianIndex)
    (vector : SU7FundamentalCarrier) :
    HasDerivAt (fun duration : ℝ => connectionTransport point direction duration *ᵥ vector)
      (connectionGenerator point direction *ᵥ vector) 0 := by
  have derivative := connectionTransport_firstJet point direction
  apply hasDerivAt_pi.mpr
  intro row
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun column _ => (hasDerivAt_pi.mp (hasDerivAt_pi.mp derivative row) column).mul_const (vector column))

theorem exteriorTransport_wedge_hasDerivAt
    (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (vectors : Fin degree → SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree) :
    HasDerivAt (fun duration : ℝ => (su7ExteriorBasis degree).repr
      (exteriorLinkAction degree (connectionTransport point direction duration)
        ((exteriorPower.ιMulti ℂ degree) vectors)) coordinate)
      ((su7ExteriorBasis degree).repr
        (exteriorMotherLieAction degree (actualPotential point direction)
          ((exteriorPower.ιMulti ℂ degree) vectors)) coordinate) 0 := by
  let form := (exteriorCoordinateForm degree coordinate).restrictScalars ℝ
  have vectorsDerivative : HasDerivAt
      (fun duration : ℝ => fun slot => connectionTransport point direction duration *ᵥ vectors slot)
      (fun slot => connectionGenerator point direction *ᵥ vectors slot) 0 :=
    hasDerivAt_pi.mpr (fun slot => fundamentalTransport_hasDerivAt point direction (vectors slot))
  have formDerivative := form.hasFDerivAt
    (fun slot => connectionTransport point direction 0 *ᵥ vectors slot)
  have derivative := formDerivative.comp_hasDerivAt 0 vectorsDerivative
  simp only [connectionTransport_zero, Matrix.one_mulVec] at derivative
  change HasDerivAt (fun duration : ℝ => form
      (fun slot => connectionTransport point direction duration *ᵥ vectors slot))
      (form.linearDeriv vectors (fun slot => connectionGenerator point direction *ᵥ vectors slot)) 0 at derivative
  simp only [ContinuousMultilinearMap.linearDeriv_apply] at derivative
  change HasDerivAt (fun duration : ℝ => (su7ExteriorBasis degree).repr
      ((exteriorPower.ιMulti ℂ degree)
        (fun slot => connectionTransport point direction duration *ᵥ vectors slot)) coordinate)
      (∑ slot, (su7ExteriorBasis degree).repr ((exteriorPower.ιMulti ℂ degree)
        (Function.update vectors slot (connectionGenerator point direction *ᵥ vectors slot))) coordinate) 0 at derivative
  rw [exteriorMotherLieAction_eq_slotDerivedAction, exteriorSlotDerivedAction_apply_ιMulti, map_sum]
  simpa only [exteriorLinkAction, exteriorPower.map_apply_ιMulti,
    fundamentalLinkAction, Matrix.mulVecLin_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
    fundamentalMotherLieAction, Function.comp_def, connectionGenerator] using derivative

theorem exteriorTransport_hasDerivAt
    (point : BasePoint) (direction : LorentzianIndex) (degree : ℕ)
    (matter : ⋀[ℂ]^degree SU7FundamentalCarrier) (coordinate : ExteriorBasisIndex degree) :
    HasDerivAt (fun duration : ℝ => (su7ExteriorBasis degree).repr
      (exteriorLinkAction degree (connectionTransport point direction duration) matter) coordinate)
      ((su7ExteriorBasis degree).repr
        (exteriorMotherLieAction degree (actualPotential point direction) matter) coordinate) 0 := by
  have basisDerivative (input : ExteriorBasisIndex degree) :=
    exteriorTransport_wedge_hasDerivAt point direction degree (exteriorBasisInput degree input) coordinate
  simp only [exteriorBasisInput_wedge_eq_basis_slot] at basisDerivative
  rw [← (su7ExteriorBasis degree).sum_repr matter]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun input _ => (basisDerivative input).const_mul ((su7ExteriorBasis degree).repr matter input))

end
end SaturationMonoid.PhysicsCore.Stage9DEF.Compatibility
