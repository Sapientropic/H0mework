import H0mework.Physics.LowEnergy.FullQuantum.ClosedLoops.Words
import H0mework.Physics.LowEnergy.FullQuantum.TriangularTrace

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Consumer
open Stage9C.Material.SpinPair DiracCliffordRepresentation SU7MotherLieAlgebra
noncomputable section

theorem actual_regular_loop_exists (k : Fin 3 → ℝ) (mu : LorentzianIndex) (data : P286LieBlockData) :
    ∃ z : ℂ, let line : GaugeLine := ⟨actual,0,k,z,mu,data⟩
      line.Regular ∧
        Triangular.diracKernel actual 0 k z*Triangular.diracResolvent actual 0 k z=1 ∧
        Triangular.diracResolvent actual 0 k z*Triangular.diracKernel actual 0 k z=1 ∧
        loopTrace (line.full*line.full)=loopTrace (line.diagonal*line.diagonal) := by
  obtain ⟨z,regular⟩ := Triangular.free_regular_energy_exists actual 0 k
  refine ⟨z,?_⟩
  let line : GaugeLine := ⟨actual,0,k,z,mu,data⟩
  have valid : line.Regular := ⟨actual_noncharacteristic 0,regular⟩
  have inverse := line.propagator valid
  exact ⟨valid,inverse.1,inverse.2,expansion_trace ((line.generated valid).mul (line.generated valid))⟩

theorem actual_whole_word_readback (lines : List GaugeLine) (k : Fin 3 → ℝ) (t : ℝ) :
    canonicalDual actual 0 k t (actual.conjugateMatter 0)
      ((lines.map GaugeLine.full).prod (primal actual 0 k t (actual.matter 0)))=
      4*(spinScale : ℂ)*Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer 0)
        (Stage9DEF.Compatibility.responseMatrix
          (insertion actual 0 k t (lines.map GaugeLine.full).prod)) :=
  original_Stage10_insertion actual 0 k t (lines.map GaugeLine.full).prod

#print axioms actual_regular_loop_exists
#print axioms actual_whole_word_readback

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.ClosedLoops.Consumer
