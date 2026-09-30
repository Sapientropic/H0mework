import H0mework.Physics.LowEnergy.PacketMomentum.Operators

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketMomentum
open FullQuantum FullSpace SpatialGreen PacketNoise GaugeHistory
noncomputable section
attribute [local irreducible] freeAction yukawaOperator inversePrincipal

theorem shift_load_continuous {X : Type*} [TopologicalSpace X] {energy damping : ℝ}
    (family : X → SourceMap energy damping) (shift : X → Position) (input : FullMatterL2)
    (continuousShift : Continuous shift)
    (continuousField : Continuous (fun x => (family x).field input))
    (continuousLoad : Continuous (fun x => (family x).load input)) :
    Continuous (fun x => ((family x).shift (shift x)).load input) := by
  change Continuous (fun x => phaseShift (shift x) ((family x).load input)-
    constantLift (shiftSymbol 0 (shift x)) (phaseShift (shift x) ((family x).field input)))
  exact (phase_apply_continuous shift continuousShift _ continuousLoad).sub
    ((constantLift.continuous.comp (shiftSymbol_continuous.comp continuousShift)).clm_apply
      (phase_apply_continuous shift continuousShift _ continuousField))

theorem cosine_load_continuous {X : Type*} [TopologicalSpace X] {energy damping : ℝ}
    (family : X → SourceMap energy damping) (shift : X → Position) (input : FullMatterL2)
    (continuousShift : Continuous shift)
    (continuousField : Continuous (fun x => (family x).field input))
    (continuousLoad : Continuous (fun x => (family x).load input)) :
    Continuous (fun x => ((family x).cosine (shift x)).load input) := by
  change Continuous (fun x => (1/2 : ℂ) •
    (((family x).shift (shift x)).load input+((family x).shift (-(shift x))).load input))
  exact ((shift_load_continuous family shift input continuousShift continuousField continuousLoad).add
    (shift_load_continuous family (fun x => -(shift x)) input continuousShift.neg continuousField continuousLoad)).const_smul
      (1/2 : ℂ)

theorem adjointHamiltonian_continuous {X : Type*} [TopologicalSpace X] {energy damping : ℝ}
    (family : X → SourceMap energy damping) (input : FullMatterL2)
    (continuousField : Continuous (fun x => (family x).field input))
    (continuousLoad : Continuous (fun x => (family x).load input)) :
    Continuous (fun x => (family x).adjointHamiltonian input) := by
  change Continuous (fun x => ((energy : ℂ)+Complex.I*(damping : ℂ)) • (family x).field input-
    Complex.I • inversePrincipal 0 ((family x).load input)+
      (yukawaOperator.adjoint-yukawaOperator) ((family x).field input))
  exact ((continuousField.const_smul ((energy : ℂ)+Complex.I*(damping : ℂ))).sub
    (((inversePrincipal 0).continuous.comp continuousLoad).const_smul Complex.I)).add
      ((yukawaOperator.adjoint-yukawaOperator).continuous.comp continuousField)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketMomentum
