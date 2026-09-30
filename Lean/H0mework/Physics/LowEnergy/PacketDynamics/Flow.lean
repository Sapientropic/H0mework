import H0mework.Physics.LowEnergy.PacketDynamics.Symbol

set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise
noncomputable section
attribute [local irreducible] temporal temporalInverse

theorem sourceField_flow (energy damping time : ℝ) (field : FullMatterL2) :
    sourceField 0 energy damping (spatialFlow 0 time field) =ᵐ[volume]
      fun frequency => temporal (fullMatrices 0 time frequency
        (temporalInverse (sourceField 0 energy damping field frequency))) := by
  filter_upwards [spatialFlow_fourier_ae 0 time field] with frequency original
  simp only [sourceField,original]
  change (symbol 0 energy damping frequency*fullMatrices 0 time frequency) (fourier field frequency)=_
  rw [symbol_flow]
  rfl

def loadFlow (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (principal 0).comp ((spatialFlow 0 time).comp (inversePrincipal 0))

theorem loadFlow_fourier (time : ℝ) (field : FullMatterL2) :
    fourier (loadFlow time field) =ᵐ[volume]
      fun frequency => temporal (fullMatrices 0 time frequency (temporalInverse (fourier field frequency))) := by
  have inverse : fourier (inversePrincipal 0 field)=inversePrincipal 0 (fourier field) :=
    GaugeGreen.constant_fourier _ field
  change fourier (principal 0 (spatialFlow 0 time (inversePrincipal 0 field))) =ᵐ[volume] _
  rw [GaugeGreen.principal_fourier]
  filter_upwards [GaugeGreen.principal_ae 0 (fourier (spatialFlow 0 time (inversePrincipal 0 field))),
    spatialFlow_fourier_ae 0 time (inversePrincipal 0 field),
    temporalInverse.coeFn_compLpL (fourier field)] with frequency outer flow inner
  rw [outer,flow,inverse]
  rw [← temporal]
  have inverseValue : inversePrincipal 0 (fourier field) frequency=temporalInverse (fourier field frequency) := by
    simpa only [inversePrincipal,temporalInverse] using inner
  exact congrArg (fun x => temporal (fullMatrices 0 time frequency x)) inverseValue

def evolve {energy damping : ℝ} (map : SourceMap energy damping) (time : ℝ) : SourceMap energy damping where
  field := (spatialFlow 0 time).comp map.field
  load := (loadFlow time).comp map.load
  equation input := by
    filter_upwards [sourceField_flow energy damping time (map.field input),map.equation input,
      loadFlow_fourier time (map.load input)] with frequency original equation load
    exact original.trans ((congrArg (fun x => temporal (fullMatrices 0 time frequency (temporalInverse x))) equation).trans load.symm)

theorem evolve_field {energy damping : ℝ} (map : SourceMap energy damping) (time : ℝ) (input : FullMatterL2) :
    (evolve map time).field input=spatialFlow 0 time (map.field input) := rfl

theorem evolve_hamiltonian {energy damping : ℝ} (map : SourceMap energy damping)
    (positive : 0 < damping) (time : ℝ) (input : FullMatterL2) :
    sourceHamiltonian ((evolve map time).generator positive input)=
      spatialFlow 0 time (sourceHamiltonian (map.generator positive input)) := by
  rw [(evolve map time).hamiltonian_value positive,map.hamiltonian_value positive]
  change ((energy : ℂ)+Complex.I*(damping : ℂ)) • spatialFlow 0 time (map.field input)-
    Complex.I • inversePrincipal 0 (principal 0 (spatialFlow 0 time (inversePrincipal 0 (map.load input))))=
      spatialFlow 0 time (((energy : ℂ)+Complex.I*(damping : ℂ)) • map.field input-
        Complex.I • inversePrincipal 0 (map.load input))
  rw [inversePrincipal_left,map_sub,map_smul,map_smul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
