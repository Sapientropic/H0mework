import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.ActualFlow

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
open Collision Propagation.Interface Powered.Source Load.Producer.StrictThermal
open scoped Matrix Matrix.Norms.L2Operator
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem tensor_unitary_error [Nonempty ι] (U V : Matrix.unitaryGroup ι ℂ) :
    ‖Matrix.kronecker (U : Matrix ι ι ℂ) (U : Matrix ι ι ℂ)-
      Matrix.kronecker (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ)‖ ≤ 2*‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖ := by
  have split : Matrix.kronecker (U : Matrix ι ι ℂ) (U : Matrix ι ι ℂ)-
      Matrix.kronecker (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ) =
      Matrix.kronecker ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) (U : Matrix ι ι ℂ)+
      Matrix.kronecker (V : Matrix ι ι ℂ) ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.kronecker,Matrix.kroneckerMap_apply]
    ring
  rw [split]
  have left := kronecker_norm_le ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)) (U : Matrix ι ι ℂ)
  have right := kronecker_norm_le (V : Matrix ι ι ℂ) ((U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ))
  rw [CStarRing.norm_coe_unitary U,mul_one] at left
  rw [CStarRing.norm_coe_unitary V,one_mul] at right
  exact (norm_add_le _ _).trans (by linarith)

def numericPCUnitary (time : ℝ) : Matrix.unitaryGroup Load.Source.PairController ℂ :=
  ⟨hamiltonianFlow (sourcePCH E) time,hamiltonianFlow_unitary _ numeric_PC_hermitian time⟩

def mappedPCUnitary (time : ℝ) : Matrix.unitaryGroup Load.Source.PairController ℂ :=
  installedPCFrame*Native.freePCUnitary time*star installedPCFrame

theorem mapped_PC_value (time : ℝ) : (mappedPCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ) =
    Quantum.conjugation installedPCFrame (Native.freePCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ) := by
  simp only [mappedPCUnitary,Submonoid.coe_mul,Unitary.coe_star,Quantum.conjugation_apply]

def numericPairPulse (time : ℝ) : Matrix.unitaryGroup (Load.Source.PairController × Load.Source.PairController) ℂ :=
  Quantum.localUnitary (numericPCUnitary time) (numericPCUnitary time)*Exchange.exchangeUnitary (Native.sourceCoupling*time)

theorem original_exchange_shared (U : Matrix.unitaryGroup ι ℂ) (angle : ℝ) :
    Quantum.localConjugation U U (Exchange.exchangeUnitary (ι := ι) angle : JointMatrix ι) = (Exchange.exchangeUnitary (ι := ι) angle : JointMatrix ι) := by
  have one : Quantum.localConjugation U U (1 : JointMatrix ι) = 1 :=
    map_one (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (Quantum.localUnitary U U))
  simp only [Exchange.exchangeUnitary,partialSwap,map_sub,map_smul,one,shared_conjugation_swap]

theorem local_conjugation_mul (U : Matrix.unitaryGroup ι ℂ) (A B : JointMatrix ι) :
    Quantum.localConjugation U U (A*B) = Quantum.localConjugation U U A*Quantum.localConjugation U U B :=
  map_mul (Unitary.conjStarAlgAut ℂ (JointMatrix ι) (Quantum.localUnitary U U)) A B

theorem local_pair_pulse (U V : Matrix.unitaryGroup ι ℂ) (angle : ℝ) :
    Quantum.localConjugation U U
      ((Quantum.localUnitary V V*Exchange.exchangeUnitary angle : Matrix.unitaryGroup (ι × ι) ℂ) : JointMatrix ι) =
      Matrix.kronecker (Quantum.conjugation U (V : Matrix ι ι ℂ)) (Quantum.conjugation U (V : Matrix ι ι ℂ))*
        (Exchange.exchangeUnitary (ι := ι) angle : JointMatrix ι) := by
  simp only [Submonoid.coe_mul,local_conjugation_mul,original_exchange_shared]
  change Quantum.localConjugation U U (Matrix.kronecker (V : Matrix ι ι ℂ) (V : Matrix ι ι ℂ))*_ = _
  rw [Quantum.localConjugation_tensor]

theorem tensor_exchange_error [Nonempty ι] (U V : Matrix.unitaryGroup ι ℂ) (angle : ℝ) :
    ‖((Quantum.localUnitary U U*Exchange.exchangeUnitary angle : Matrix.unitaryGroup (ι × ι) ℂ) : JointMatrix ι)-
      ((Quantum.localUnitary V V*Exchange.exchangeUnitary angle : Matrix.unitaryGroup (ι × ι) ℂ) : JointMatrix ι)‖ ≤
        2*‖(U : Matrix ι ι ℂ)-(V : Matrix ι ι ℂ)‖ := by
  simp only [Submonoid.coe_mul]
  rw [← sub_mul,CStarRing.norm_mul_coe_unitary]
  exact tensor_unitary_error U V

theorem mapped_pair_pulse (U V : Matrix.unitaryGroup ι ℂ) (angle : ℝ) :
    Quantum.localConjugation U U
      ((Quantum.localUnitary V V*Exchange.exchangeUnitary angle : Matrix.unitaryGroup (ι × ι) ℂ) : JointMatrix ι) =
      ((Quantum.localUnitary (U*V*star U) (U*V*star U)*Exchange.exchangeUnitary angle :
        Matrix.unitaryGroup (ι × ι) ℂ) : JointMatrix ι) := by
  rw [local_pair_pulse]
  simp only [Submonoid.coe_mul,Quantum.conjugation_apply]
  rfl

attribute [local irreducible] installedPCFrame Native.freePCUnitary

/-- The same original exchange angle and donor side remain in the coupled source approximation. -/
theorem original_pair_pulse_error (time : ℝ) :
    ‖Quantum.localConjugation installedPCFrame installedPCFrame
      (Native.pairFlow time : JointMatrix Load.Source.PairController)-
        (numericPairPulse time : JointMatrix Load.Source.PairController)‖ ≤ |time| * (252/10^12 : ℝ) := by
  rw [Native.pairFlow_factor,mapped_pair_pulse]
  have estimate := tensor_exchange_error (mappedPCUnitary time) (numericPCUnitary time) (Native.sourceCoupling*time)
  have final : 2*‖(mappedPCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ)-(numericPCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ)‖ ≤
      |time| * (252/10^12 : ℝ) := by
    rw [mapped_PC_value]
    have bound := actual_free_PC_error time
    change ‖Quantum.conjugation installedPCFrame (Native.freePCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ)-
      (numericPCUnitary time : Matrix Load.Source.PairController Load.Source.PairController ℂ)‖ ≤ _ at bound
    linarith
  exact estimate.trans final

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
