import H0mework.Physics.SpinPair.Spinor
import H0mework.Physics.SpinPair.Phase
import H0mework.Physics.Material.CartanAssemblyQualification
import H0mework.Physics.Homogeneous.Cartan

/-! One actual from the original color source, its generated phase pair and
the joint positive amplitudes. The existing action writes every auxiliary,
the Cartan connection and the gravitational reaction on this whole field. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair

open ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineGlobalIntegratedAction StageNineHolonomicField
open StageNineDynamicBreakingVacuum StageNineCClassicalWorldAcceptance
open StageNineP286GaugeConnectionVariation StageNineLorentzConnectionVariation
open StageNineGravityBianchi SU7MotherLieAlgebra
open Stage9C.Reduction Stage9C.Dynamics.Homogeneous

noncomputable section

def gaugePotential (amplitude : ℝ) : LorentzianIndex → P286LieBlockData :=
  ![0, amplitude • sourceColorP286Generator 0,
    amplitude • sourceColorP286Generator 1, amplitude • sourceColorP286Generator 2]

def seed : StageNineHolonomicConfiguration :=
  { firstAssemblyCartanActual with
    coframe := fun _ => homogeneousCoframe lapse
    gaugeConnection := fun _ => gaugePotential gaugeScale
    scalar := fun _ => firstAssemblyCartanActual.scalar 0
    matter := fun point => spinPairMatter (upperPhase point) (lowerPhase point)
    conjugateMatter := fun point => spinPairDual (upperDualPhase point) (lowerDualPhase point) }

def actual : StageNineHolonomicConfiguration :=
  algebraicCartanReduction positiveSmoothUnifiedSource seed

theorem actual_coframe : actual.coframe = fun _ => homogeneousCoframe lapse := rfl
theorem actual_gaugeConnection :
    actual.gaugeConnection = fun _ => gaugePotential gaugeScale := rfl
theorem actual_matter : actual.matter =
    fun point => spinPairMatter (upperPhase point) (lowerPhase point) := rfl
theorem actual_conjugateMatter : actual.conjugateMatter =
    fun point => spinPairDual (upperDualPhase point) (lowerDualPhase point) := rfl

theorem actual_scalar : actual.scalar =
    fun _ => sourceGeneratedVacuumCoordinates positiveSmoothUnifiedSource := by
  funext point
  change firstAssemblyCartanActual.scalar 0 = _
  rw [firstAssemblyCartanActual_dynamicScalarSourceContact]
  exact congrFun
    StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchySafeDynamicScalarSourceContact.positive_generatedLocalVacuumCoordinates_zero_eq_constant 0

theorem seed_nondegenerate : seed.Nondegenerate :=
  fun _ => homogeneousCoframe_nondegenerate lapse lapse_pos

theorem actual_nondegenerate : actual.Nondegenerate := by
  intro point
  rw [actual_coframe]
  exact homogeneousCoframe_nondegenerate lapse lapse_pos

theorem actual_lorentzAdmissible :
    GravityConnectionLorentzAdmissible actual :=
  algebraicCartanReduction_lorentzAdmissible positiveSmoothUnifiedSource seed seed_nondegenerate

theorem actual_dynamicScalarSourceContact :
    DynamicScalarSourceContactAtOrigin positiveSmoothUnifiedSource actual :=
  firstAssemblyCartanActual_dynamicScalarSourceContact

end
end SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair
