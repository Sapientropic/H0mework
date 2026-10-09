import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.Inverse.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.WeakSupply

set_option autoImplicit false
set_option maxRecDepth 4096
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
open Collision Propagation.Interface Load.Source
open scoped Matrix ComplexOrder
noncomputable section

def reservoirOrbit (p : Current.FullIndex) : Sym2 (Sym2 Basis) :=
  s(pcOrbit p.1.1, pcOrbit p.1.2)
def pointerOrbit : PointerIndex → Sym2 (Sym2 Basis) := Sum.elim reservoirOrbit reservoirOrbit

theorem pair_swap_preserves :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1, pcOrbit p.2))
      (swapOperator : JointMatrix PairController) := by
  intro ⟨i,a⟩ ⟨j,b⟩ separated
  have entry := swap_mul_apply (1 : JointMatrix PairController) i a j b
  rw [Matrix.mul_one] at entry
  rw [entry]
  have distinct : (a,i) ≠ (j,b) := by
    intro equal
    apply separated
    exact (Sym2.eq_swap : s(pcOrbit i,pcOrbit a) = s(pcOrbit a,pcOrbit i)).trans
      (congrArg (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2)) equal)
  simp [distinct]

theorem exchange_preserves (time : ℝ) :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2))
      (Exchange.exchangeUnitary (ι := PairController) time : JointMatrix PairController) := by
  change Preserves _ (partialSwap (Real.cos time) (Real.sin time))
  exact preserves_sub (preserves_smul (preserves_one _) _) (preserves_smul pair_swap_preserves _)

theorem localLift_preserves (U : Matrix.unitaryGroup (PairController × Fin 2) ℂ)
    (V : Matrix.unitaryGroup PairController ℂ)
    (left : Preserves pceOrbit (U : LoadedJoint))
    (right : Preserves pcOrbit (V : Matrix PairController PairController ℂ)) :
    Preserves reservoirOrbit (Incidence.localLift U V : Current.FullJoint) := by
  intro i j separated
  change (U : LoadedJoint) (i.1.1,i.2) (j.1.1,j.2) *
    (V : Matrix PairController PairController ℂ) i.1.2 j.1.2 = 0
  by_cases same : pcOrbit i.1.1 = pcOrbit j.1.1
  · rw [right _ _ (fun other => separated (by simp only [reservoirOrbit, same, other])), mul_zero]
  · rw [left (i.1.1,i.2) (j.1.1,j.2) same, zero_mul]

theorem bodyObservable_preserves (O : LoadedJoint) (kept : Preserves pceOrbit O) :
    Preserves reservoirOrbit (Incidence.bodyObservable O) := by
  intro i j separated
  change O (i.1.1,i.2) (j.1.1,j.2) * (1 : Matrix PairController PairController ℂ) i.1.2 j.1.2 = 0
  by_cases same : pcOrbit i.1.1 = pcOrbit j.1.1
  · rw [preserves_one pcOrbit _ _ (fun other => separated (by simp only [reservoirOrbit, same, other])), mul_zero]
  · rw [kept (i.1.1,i.2) (j.1.1,j.2) same, zero_mul]

theorem free_pair_preserves (time : ℝ) :
    Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2))
      (Quantum.localUnitary (Native.freePCUnitary time) (Native.freePCUnitary time) :
        JointMatrix PairController) :=
  preserves_relabel (preserves_tensor (source_free_pc_preserves time) (source_free_pc_preserves time))
    (fun p : Sym2 Basis × Sym2 Basis => s(p.1,p.2))

theorem original_pulse_preserves (time : ℝ) :
    Preserves reservoirOrbit (Current.pulse time : Current.FullJoint) := by
  have pair : Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2))
      (Native.pairFlow time : JointMatrix PairController) := by
    rw [Native.pairFlow_factor, MulMemClass.coe_mul]
    exact preserves_mul (free_pair_preserves time) (exchange_preserves _)
  exact preserves_tensor_left pair _

theorem original_load_preserves (time : ℝ) :
    Preserves reservoirOrbit (Current.loadPulse time : Current.FullJoint) :=
  localLift_preserves _ _ (source_load_flow_preserves time) (source_free_pc_preserves time)

theorem weak_pulse_preserves (time : ℝ) :
    Preserves reservoirOrbit (Weak.fullPulse time : Current.FullJoint) := by
  have pair : Preserves (fun p : PairController × PairController => s(pcOrbit p.1,pcOrbit p.2))
      (Weak.pairPulse time : JointMatrix PairController) := by
    rw [Weak.pair_factor, MulMemClass.coe_mul]
    exact preserves_mul (free_pair_preserves time) (exchange_preserves _)
  exact preserves_tensor_left pair _


end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.Sectors
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
