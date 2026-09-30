import H0mework.Physics.LowEnergy.PacketNoise.Bounded

/-! The generated current response varies continuously with genuine continuum momentum transfer. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen GaugeHistory Stage9C.Dynamics.Homogeneous
open Stage9C.Material.SpinPair
noncomputable section
attribute [local irreducible] freeAction yukawaOperator inversePrincipal

def constantLift : FiberOperators →L[ℂ] FullMatterL2 →L[ℂ] FullMatterL2 :=
  (ContinuousLinearMap.id ℂ FiberOperators).compLpL₂ 2 volume

theorem shiftSymbol_continuous : Continuous (shiftSymbol 0) := by
  unfold shiftSymbol
  apply continuous_finsetSum
  intro j _
  exact (Complex.continuous_ofReal.comp ((continuous_apply j).comp physicalMomentum_continuous)).smul
    continuous_const

theorem SourceMap.shift_load_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (input : FullMatterL2) : Continuous (fun transfer => (map.shift transfer).load input) := by
  change Continuous (fun transfer => phaseShift transfer (map.load input)-
    constantLift (shiftSymbol 0 transfer) (phaseShift transfer (map.field input)))
  exact (phaseShift_continuous (map.load input)).sub
    ((constantLift.continuous.comp shiftSymbol_continuous).clm_apply
      (phaseShift_continuous (map.field input)))

theorem SourceMap.cosine_load_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (input : FullMatterL2) : Continuous (fun transfer => (map.cosine transfer).load input) := by
  change Continuous (fun transfer => (1/2 : ℂ) •
    ((map.shift transfer).load input+(map.shift (-transfer)).load input))
  exact ((map.shift_load_continuous input).add
    ((map.shift_load_continuous input).comp continuous_neg)).const_smul (1/2 : ℂ)

theorem SourceMap.cosine_adjointHamiltonian_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (input : FullMatterL2) : Continuous (fun transfer => (map.cosine transfer).adjointHamiltonian input) := by
  change Continuous (fun transfer =>
    ((energy : ℂ)+Complex.I*(damping : ℂ)) • cosineShift transfer (map.field input)-
      Complex.I • inversePrincipal 0 ((map.cosine transfer).load input)+
        (yukawaOperator.adjoint-yukawaOperator) (cosineShift transfer (map.field input)))
  exact (((cosineShift_continuous (map.field input)).const_smul
    ((energy : ℂ)+Complex.I*(damping : ℂ))).sub
    (((inversePrincipal 0).continuous.comp (map.cosine_load_continuous input)).const_smul Complex.I)).add
      ((yukawaOperator.adjoint-yukawaOperator).continuous.comp (cosineShift_continuous (map.field input)))

theorem SourceMap.current_continuous {energy damping : ℝ} (map : SourceMap energy damping)
    (input : FullMatterL2) : Continuous (fun transfer => map.current transfer input) := by
  change Continuous (fun transfer => (((lapse^2)⁻¹ : ℝ) : ℂ) •
    (boundaryAction (cosineShift transfer (map.hamiltonian input))+
      (map.boundary.cosine transfer).adjointHamiltonian input))
  exact ((boundaryAction.continuous.comp (cosineShift_continuous (map.hamiltonian input))).add
    (map.boundary.cosine_adjointHamiltonian_continuous input)).const_smul (((lapse^2)⁻¹ : ℝ) : ℂ)

theorem currentFilter_continuous (energy damping : ℝ) (positive : 0 < damping) (input : FullMatterL2) :
    Continuous (fun transfer => currentFilter energy damping positive transfer input) := by
  change Continuous (fun transfer => ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ) •
    (greenMap energy damping positive).current transfer input)
  exact ((greenMap energy damping positive).current_continuous input).const_smul
    ((‖rawPacket energy damping positive‖⁻¹ : ℝ) : ℂ)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
