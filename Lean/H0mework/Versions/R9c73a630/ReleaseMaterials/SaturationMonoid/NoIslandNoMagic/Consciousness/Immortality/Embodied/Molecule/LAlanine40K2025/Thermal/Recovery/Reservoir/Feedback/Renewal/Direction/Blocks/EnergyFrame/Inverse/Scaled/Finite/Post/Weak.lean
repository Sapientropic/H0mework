import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post.Load

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
open Collision Load.Source Propagation.Producer
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def mappedWeakPair : Matrix.unitaryGroup (PairController × PairController) ℂ :=
  Quantum.localUnitary (mappedPCUnitary (nativeClockStep : ℝ)) (mappedPCUnitary (nativeClockStep : ℝ))*
    Exchange.exchangeUnitary (nativeClockStep : ℝ)

def weakPairPolynomial : JointMatrix PairController := Supply.sharedPCPolynomial*Supply.weakExchangePolynomial

theorem mapped_shared_PC_polynomial_error :
    ‖(Quantum.localUnitary (mappedPCUnitary (nativeClockStep : ℝ)) (mappedPCUnitary (nativeClockStep : ℝ)) : JointMatrix PairController)-
      Supply.sharedPCPolynomial‖ ≤ (113/10^15 : ℝ) :=
  (Actions.approximated_tensor_error (mappedPCUnitary (nativeClockStep : ℝ)) (mappedPCUnitary (nativeClockStep : ℝ))
    Phase.pcPolynomial Phase.pcPolynomial (56/10^15) (56/10^15) original_PC_polynomial_error original_PC_polynomial_error).trans (by norm_num)

theorem original_weak_pair_polynomial_error :
    ‖(mappedWeakPair : JointMatrix PairController)-weakPairPolynomial‖ ≤ (114/10^15 : ℝ) :=
  (Input.approximated_product_error
    (Quantum.localUnitary (mappedPCUnitary (nativeClockStep : ℝ)) (mappedPCUnitary (nativeClockStep : ℝ)))
    (Exchange.exchangeUnitary (nativeClockStep : ℝ)) Supply.sharedPCPolynomial Supply.weakExchangePolynomial
    (113/10^15) (2/10^18) mapped_shared_PC_polynomial_error Supply.weak_exchange_polynomial_error).trans (by norm_num)

def calculatedWeak : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Actions.reframeUnitary Supply.installedFullFrame (Weak.fullPulse (nativeClockStep : ℝ))

def fullWeakPolynomial : Current.FullJoint := Matrix.kronecker weakPairPolynomial Phase.environmentPolynomial

theorem original_weak_polynomial_error :
    ‖(calculatedWeak : Current.FullJoint)-fullWeakPolynomial‖ ≤ (115/10^15 : ℝ) := by
  change ‖(Actions.reframeUnitary (spectatorFrame (Quantum.localUnitary installedPCFrame installedPCFrame))
    (Load.Quantum.localUnitary (Weak.pairPulse (nativeClockStep : ℝ))
      (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))) : Current.FullJoint)-fullWeakPolynomial‖ ≤ _
  rw [Actions.reframe_spectator]
  have same : (Actions.reframeUnitary (Quantum.localUnitary installedPCFrame installedPCFrame)
      (Weak.pairPulse (nativeClockStep : ℝ)) : JointMatrix PairController)=(mappedWeakPair : JointMatrix PairController) := by
    rw [Actions.reframe_value,Weak.pair_factor]
    change Quantum.localConjugation installedPCFrame installedPCFrame
      ((Quantum.localUnitary (Native.freePCUnitary (nativeClockStep : ℝ)) (Native.freePCUnitary (nativeClockStep : ℝ))*
        Exchange.exchangeUnitary (nativeClockStep : ℝ) : Matrix.unitaryGroup (PairController × PairController) ℂ) : JointMatrix PairController)=_
    rw [mapped_pair_pulse]
    rfl
  rw [same]
  exact (Actions.approximated_tensor_error mappedWeakPair (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))
    weakPairPolynomial Phase.environmentPolynomial (114/10^15) (1/10^18)
    original_weak_pair_polynomial_error Phase.environment_polynomial_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Post
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
