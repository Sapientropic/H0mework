import H0mework.Physics.LowEnergy.PacketDynamics.Continuity
import H0mework.Physics.LowEnergy.PacketDynamics.AdjointGraph

/-! Every load in the transported source graph is continuous in actual time, including the adjoint Yukawa correction. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise GaugeHistory
noncomputable section
attribute [local irreducible] freeAction yukawaOperator inversePrincipal

theorem adjointEvolve_field_continuous {energy damping : ℝ} (map : SourceMap energy damping) (input : FullMatterL2) :
    Continuous (fun time => (adjointEvolve map time).field input) :=
  adjointFlow_stronglyContinuous (map.field input)

theorem adjointEvolve_load_continuous {energy damping : ℝ} (map : SourceMap energy damping) (input : FullMatterL2) :
    Continuous (fun time => (adjointEvolve map time).load input) := by
  change Continuous (fun time => principal 0 (adjointFlow time (inversePrincipal 0 (map.load input)))+
    Complex.I • principal 0 (skewAction (adjointFlow time (map.field input))-
      adjointFlow time (skewAction (map.field input))))
  exact ((principal 0).continuous.comp (adjointFlow_stronglyContinuous _)).add
    (((principal 0).continuous.comp ((skewAction.continuous.comp (adjointFlow_stronglyContinuous _)).sub
      (adjointFlow_stronglyContinuous _))).const_smul Complex.I)

theorem cosine_family_load_continuous {energy damping : ℝ} (family : ℝ → SourceMap energy damping)
    (input : FullMatterL2) (shift : Position)
    (continuousField : Continuous (fun time => (family time).field input))
    (continuousLoad : Continuous (fun time => (family time).load input)) :
    Continuous (fun time => ((family time).cosine shift).load input) := by
  have shifted (transfer : Position) : Continuous (fun time => ((family time).shift transfer).load input) := by
    change Continuous (fun time => phaseShift transfer ((family time).load input)-
      constantLift (shiftSymbol 0 transfer) (phaseShift transfer ((family time).field input)))
    exact ((phaseShift transfer).continuous.comp continuousLoad).sub
      ((constantLift (shiftSymbol 0 transfer)).continuous.comp ((phaseShift transfer).continuous.comp continuousField))
  change Continuous (fun time => (1/2 : ℂ) •
    (((family time).shift shift).load input+((family time).shift (-shift)).load input))
  exact ((shifted shift).add (shifted (-shift))).const_smul (1/2 : ℂ)

theorem adjointHamiltonian_family_continuous {energy damping : ℝ} (family : ℝ → SourceMap energy damping)
    (input : FullMatterL2)
    (continuousField : Continuous (fun time => (family time).field input))
    (continuousLoad : Continuous (fun time => (family time).load input)) :
    Continuous (fun time => (family time).adjointHamiltonian input) := by
  change Continuous (fun time => ((energy : ℂ)+Complex.I*(damping : ℂ)) • (family time).field input-
    Complex.I • inversePrincipal 0 ((family time).load input)+
      (yukawaOperator.adjoint-yukawaOperator) ((family time).field input))
  exact ((continuousField.const_smul ((energy : ℂ)+Complex.I*(damping : ℂ))).sub
    (((inversePrincipal 0).continuous.comp continuousLoad).const_smul Complex.I)).add
      ((yukawaOperator.adjoint-yukawaOperator).continuous.comp continuousField)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
