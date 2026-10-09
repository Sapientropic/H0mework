import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply.Exchange
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Actions.Received

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
open Collision Propagation.Producer Load.Source Load.Producer.StrictThermal
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section

def sharedPCPolynomial : JointMatrix PairController := Matrix.kronecker Phase.pcPolynomial Phase.pcPolynomial
def nativePairPolynomial : JointMatrix PairController := sharedPCPolynomial*nativeExchangePolynomial

theorem shared_PC_polynomial_error :
    ‖(Quantum.localUnitary numericPCFree numericPCFree : JointMatrix PairController)-sharedPCPolynomial‖ ≤ (3/10^18 : ℝ) :=
  (Actions.approximated_tensor_error numericPCFree numericPCFree Phase.pcPolynomial Phase.pcPolynomial
    (1/10^18) (1/10^18) Phase.pc_polynomial_error Phase.pc_polynomial_error).trans (by norm_num)

theorem numeric_native_pair_polynomial_error :
    ‖(numericPairPulse (nativeClockStep : ℝ) : JointMatrix PairController)-nativePairPolynomial‖ ≤ (6/10^18 : ℝ) :=
  (Input.approximated_product_error (Quantum.localUnitary numericPCFree numericPCFree)
    (Exchange.exchangeUnitary (Native.sourceCoupling*(nativeClockStep : ℝ))) sharedPCPolynomial nativeExchangePolynomial
    (3/10^18) (2/10^18) shared_PC_polynomial_error native_exchange_polynomial_error).trans (by norm_num)

theorem original_native_pair_polynomial_error :
    ‖(mappedPairUnitary (nativeClockStep : ℝ) : JointMatrix PairController)-nativePairPolynomial‖ ≤ (111/10^15 : ℝ) := by
  have triangle := norm_sub_le_norm_sub_add_norm_sub (mappedPairUnitary (nativeClockStep : ℝ) : JointMatrix PairController)
    (numericPairPulse (nativeClockStep : ℝ) : JointMatrix PairController) nativePairPolynomial
  linarith [actual_pair_native_error,numeric_native_pair_polynomial_error]

def installedFullFrame : Matrix.unitaryGroup Current.FullIndex ℂ :=
  spectatorFrame (Quantum.localUnitary installedPCFrame installedPCFrame)

def calculatedSupply : Matrix.unitaryGroup Current.FullIndex ℂ :=
  Actions.reframeUnitary installedFullFrame (Current.pulse (nativeClockStep : ℝ))

def fullSupplyPolynomial : Current.FullJoint := Matrix.kronecker nativePairPolynomial Phase.environmentPolynomial

theorem original_supply_polynomial_error :
    ‖(calculatedSupply : Current.FullJoint)-fullSupplyPolynomial‖ ≤ (112/10^15 : ℝ) := by
  change ‖(Actions.reframeUnitary (spectatorFrame (Quantum.localUnitary installedPCFrame installedPCFrame))
    (Load.Quantum.localUnitary (Native.pairFlow (nativeClockStep : ℝ))
      (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ))) : Current.FullJoint)-fullSupplyPolynomial‖ ≤ _
  rw [Actions.reframe_spectator]
  have same : (Actions.reframeUnitary (Quantum.localUnitary installedPCFrame installedPCFrame)
      (Native.pairFlow (nativeClockStep : ℝ)) : JointMatrix PairController)=
      (mappedPairUnitary (nativeClockStep : ℝ) : JointMatrix PairController) := mapped_pair_value _
  rw [same]
  exact (Actions.approximated_tensor_error (mappedPairUnitary (nativeClockStep : ℝ))
    (Load.Recovery.Control.environmentUnitary (nativeClockStep : ℝ)) nativePairPolynomial Phase.environmentPolynomial
    (111/10^15) (1/10^18) original_native_pair_polynomial_error Phase.environment_polynomial_error).trans (by norm_num)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Supply
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
