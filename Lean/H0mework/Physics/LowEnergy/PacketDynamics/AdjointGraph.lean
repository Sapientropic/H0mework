import H0mework.Physics.LowEnergy.PacketDynamics.AdjointSymbol
import H0mework.Physics.LowEnergy.PacketDynamics.Fourier

set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
open FullQuantum FullSpace SpatialGreen PacketNoise
noncomputable section

def skewAction : FullMatterL2 →L[ℂ] FullMatterL2 := skewFiber.compLpL 2 volume

def adjointLoadFlow (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (principal 0).comp ((adjointFlow time).comp (inversePrincipal 0))

def adjointCorrection (time : ℝ) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  Complex.I • (principal 0).comp
    (skewAction.comp (adjointFlow time)-(adjointFlow time).comp skewAction)

def adjointLoadMatrix (time : ℝ) (frequency : Position) : FiberOperators :=
  temporal*(adjointMatrices time frequency*temporalInverse)

def adjointCorrectionMatrix (time : ℝ) (frequency : Position) : FiberOperators :=
  Complex.I • (temporal*(skewFiber*adjointMatrices time frequency-adjointMatrices time frequency*skewFiber))

theorem adjointLoadFlow_symbol (time : ℝ) : HasSymbol (adjointLoadFlow time) (adjointLoadMatrix time) :=
  (constant_symbol temporal).comp ((adjointFlow_symbol time).comp (constant_symbol temporalInverse))

theorem adjointCorrection_symbol (time : ℝ) : HasSymbol (adjointCorrection time) (adjointCorrectionMatrix time) :=
  ((constant_symbol temporal).comp (((constant_symbol skewFiber).comp (adjointFlow_symbol time)).sub
    ((adjointFlow_symbol time).comp (constant_symbol skewFiber)))).smul Complex.I

attribute [local irreducible] temporal temporalInverse skewFiber adjointMatrices

theorem sourceField_adjointFlow (energy damping time : ℝ) (field : FullMatterL2) :
    sourceField 0 energy damping (adjointFlow time field) =ᵐ[volume]
      fun frequency => adjointLoadMatrix time frequency (sourceField 0 energy damping field frequency)+
        adjointCorrectionMatrix time frequency (fourier field frequency) := by
  filter_upwards [adjointFlow_symbol time field] with frequency flow
  simp only [sourceField,flow]
  change (symbol 0 energy damping frequency*adjointMatrices time frequency) (fourier field frequency)=_
  rw [symbol_adjoint_flow]
  rfl

def adjointEvolve {energy damping : ℝ} (map : SourceMap energy damping) (time : ℝ) : SourceMap energy damping where
  field := (adjointFlow time).comp map.field
  load := (adjointLoadFlow time).comp map.load+(adjointCorrection time).comp map.field
  equation input := by
    change sourceField 0 energy damping (adjointFlow time (map.field input)) =ᵐ[volume]
      fourier (adjointLoadFlow time (map.load input)+adjointCorrection time (map.field input))
    rw [map_add]
    filter_upwards [sourceField_adjointFlow energy damping time (map.field input),map.equation input,
      adjointLoadFlow_symbol time (map.load input),adjointCorrection_symbol time (map.field input),
      Lp.coeFn_add (fourier (adjointLoadFlow time (map.load input)))
        (fourier (adjointCorrection time (map.field input)))]
      with frequency original equation load correction sum
    rw [original,equation,sum]
    simp only [Pi.add_apply,load,correction]

theorem adjointEvolve_field {energy damping : ℝ} (map : SourceMap energy damping) (time : ℝ) (input : FullMatterL2) :
    (adjointEvolve map time).field input=adjointFlow time (map.field input) := rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketDynamics
