import H0mework.Physics.LowEnergy.PacketNoise.Linear

/-! Momentum transfer and the original boundary weight generate new bounded Dirac graphs from the same source graph. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
open FullQuantum FullSpace SpatialGreen
noncomputable section
attribute [local irreducible] chiral chiralContact

def SourceMap.shift {energy damping : ℝ} (map : SourceMap energy damping) (transfer : Position) :
    SourceMap energy damping where
  field := (phaseShift transfer).toContinuousLinearMap.comp map.field
  load := (phaseShift transfer).toContinuousLinearMap.comp map.load-
    ((shiftSymbol 0 transfer).compLpL 2 volume).comp
      ((phaseShift transfer).toContinuousLinearMap.comp map.field)
  equation input := by
    have value := original_dirac_shift 0 energy damping (map.domain input) transfer
    rw [map.dirac_value] at value
    have equation := dirac_fourier_ae 0 energy damping
      (domainShift 0 energy damping transfer (map.domain input))
    rw [value] at equation
    exact equation.symm

def SourceMap.boundary {energy damping : ℝ} (map : SourceMap energy damping) :
    SourceMap energy damping where
  field := boundaryAction.comp map.field
  load := ((chiralContact 0 energy damping).compLpL 2 volume).comp map.field-
    boundaryAction.comp map.load
  equation input := by
    change sourceField 0 energy damping (boundaryAction (map.field input)) =ᵐ[volume]
      fourier ((chiralContact 0 energy damping).compLpL 2 volume (map.field input)-
        boundaryAction (map.load input))
    rw [map_sub,GaugeGreen.constant_fourier,boundaryAction,GaugeGreen.constant_fourier]
    filter_upwards [sourceField_boundary 0 energy damping (map.field input),map.equation input,
      (chiralContact 0 energy damping).coeFn_compLpL (fourier (map.field input)),
      chiral.coeFn_compLpL (fourier (map.load input)),
      Lp.coeFn_sub ((chiralContact 0 energy damping).compLpL 2 volume (fourier (map.field input)))
        (chiral.compLpL 2 volume (fourier (map.load input)))]
      with frequency original equation first second difference
    rw [boundaryAction] at original
    rw [original,equation,difference]
    simp only [Pi.sub_apply,first,second]

def SourceMap.cosine {energy damping : ℝ} (map : SourceMap energy damping) (transfer : Position) :
    SourceMap energy damping :=
  ((map.shift transfer).add (map.shift (-transfer))).scale (1/2)

theorem SourceMap.cosine_field {energy damping : ℝ} (map : SourceMap energy damping)
    (transfer : Position) (input : FullMatterL2) :
    (map.cosine transfer).field input=cosineShift transfer (map.field input) := rfl

theorem SourceMap.boundary_field {energy damping : ℝ} (map : SourceMap energy damping)
    (input : FullMatterL2) :
    map.boundary.field input=boundaryAction (map.field input) := rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketNoise
