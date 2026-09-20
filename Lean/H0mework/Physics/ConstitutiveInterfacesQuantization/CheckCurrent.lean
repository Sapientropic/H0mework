import H0mework.Physics.ConstitutiveInterfacesQuantization.CheckFermion
import H0mework.Physics.QuantumCompatibility.Hermitian

/-! Standard finite fermionic second quantization of the exact occupied source.
The independent dual is retained in `responseMatrix`, and the original field
amplitude and spin scale are restored before comparing physical currents. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.QuantizationCheck

open DiracCliffordRepresentation DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
open StageNineP286GaugeConnectionActionVariation
open StageNineConnectionSectorSourceBalance
open SU7MotherLieAlgebra Stage9C.Material.SpinPair Stage9DEF
open scoped Matrix

noncomputable section

private theorem indexCode_injective : Function.Injective
    (fun index : Source.Index => index.1.val * 2 + index.2.val) := by
  intro first second same
  dsimp only at same
  have spin : first.1 = second.1 := by
    apply Fin.ext
    omega
  have color : first.2 = second.2 := by
    apply Fin.ext
    omega
  exact Prod.ext spin color

/-- Spin-major, color-fast order fixes the occupation-basis signs. -/
abbrev sourceIndexOrder : LinearOrder Source.Index :=
  LinearOrder.lift' _ indexCode_injective

attribute [local instance] sourceIndexOrder

def preparedFock (point : BasePoint) : Fermion.Fock Source.Index :=
  Fermion.oneParticle (Source.vector point)

def fockEvaluation (point : BasePoint) (observable : State.Observable) : ℂ :=
  Fermion.pairing (preparedFock point)
    (Fermion.secondQuantize observable (preparedFock point))

theorem preparedFock_normalized (point : BasePoint) :
    Fermion.pairing (preparedFock point) (preparedFock point) = 1 := by
  rw [preparedFock, Fermion.pairing_oneParticle]
  exact Source.vector_inner_self point

/-- Every occupied matrix element is preserved, before any physical response is selected. -/
theorem fockEvaluation_eq_source (point : BasePoint) (observable : State.Observable) :
    fockEvaluation point observable = State.evaluation point observable := by
  exact Fermion.expectation_secondQuantize_oneParticle observable (Source.vector point)

theorem full_dual_response_preserved (point : BasePoint)
    (action : Module.End ℂ DiracExteriorMatterCarrier) :
    actual.conjugateMatter point (action (actual.matter point)) =
      4 * (spinScale : ℂ) * fockEvaluation point (Compatibility.responseMatrix action) := by
  rw [fockEvaluation_eq_source]
  exact Compatibility.actual_action_quantumResponse point action

theorem complex_current_preserved (point : BasePoint) (direction : LorentzianIndex)
    (data : P286LieBlockData) :
    spinPairCurrentComplex direction data (upperDualPhase point) (lowerDualPhase point)
      (upperPhase point) (lowerPhase point) =
      4 * (spinScale : ℂ) * fockEvaluation point (Compatibility.currentObservable direction data) := by
  rw [fockEvaluation_eq_source]
  exact Compatibility.current_classical_quantum point direction data

theorem physical_current_preserved (point : BasePoint) (direction : LorentzianIndex)
    (data : P286LieBlockData) :
    fockEvaluation point (Compatibility.physicalCurrent direction data) =
      (Compatibility.vectorRead point (Compatibility.currentObservable direction data)).re := by
  rw [fockEvaluation_eq_source]
  exact Compatibility.physicalCurrent_readout point direction data

def fockCurrentResponse (point : BasePoint) (variation : P286GaugeOneForm) : ℝ :=
  4 * lapse * spinScale * ∑ direction : Fin 3,
    (fockEvaluation point (Compatibility.physicalCurrent direction.succ
      (p286CoordinateEquiv.symm (variation direction.succ)))).re

/-- This is the original full P286 current coefficient, including its source normalization. -/
theorem full_p286_current_preserved (point : BasePoint) (variation : P286GaugeOneForm) :
    fockCurrentResponse point variation =
      p286MatterCurrentCoefficient
        StageNineEnrichedProofFreeSource.positiveSmoothUnifiedSource actual variation point := by
  rw [← Compatibility.currentResponse_eq_classical]
  unfold fockCurrentResponse Compatibility.currentResponse
  simp only [physical_current_preserved, Complex.ofReal_re]

theorem source_generator_prediction (point : BasePoint) (direction generator : Fin 3) :
    fockEvaluation point
      (Compatibility.physicalCurrent direction.succ (sourceColorP286Generator generator)) =
      if direction = generator then 1 / 2 else 0 := by
  rw [fockEvaluation_eq_source]
  exact Compatibility.physicalCurrent_prediction point direction generator

theorem physical_stress_preserved (point : BasePoint) (internal direction : LorentzianIndex) :
    fockEvaluation point (Compatibility.physicalKinetic internal direction) =
      (Compatibility.vectorRead point (Compatibility.kineticObservable internal direction)).re := by
  rw [fockEvaluation_eq_source]
  exact Compatibility.physicalKinetic_readout point internal direction

end
end SaturationMonoid.PhysicsCore.QuantizationCheck
