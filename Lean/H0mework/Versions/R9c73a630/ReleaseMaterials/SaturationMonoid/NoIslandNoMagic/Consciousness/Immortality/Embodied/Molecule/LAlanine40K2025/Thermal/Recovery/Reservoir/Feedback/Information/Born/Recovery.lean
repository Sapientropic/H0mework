import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Information.Born.Moment
import H0mework.Probability.Recovery.Error
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Probability.Source.Recovery.Moments

/-! The same joint Born output generates its optimal pointer decoder and preserves the original observable mean. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born

open _root_.SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Collision

noncomputable section

local instance : MeasurableSpace PointerIndex := ⊤
local instance : MeasurableSingletonClass PointerIndex := ⟨fun _ => trivial⟩

variable (observable : Current.FullJoint) (hermitian : observable.IsHermitian) (current : Live.State)

def task (index : PointerIndex) : ℂ := outcome observable hermitian index

def bestDecoder : Fin 2 → ℂ :=
  SourceWeightedRecovery.optimalDecoder (distribution observable hermitian current) pointer (task observable hermitian)

def loss (decoder : Fin 2 → ℂ) : ℝ :=
  SourceWeightedRecovery.error (distribution observable hermitian current) pointer (task observable hermitian) decoder

theorem loss_decomposition (decoder : Fin 2 → ℂ) :
    loss observable hermitian current decoder = loss observable hermitian current (bestDecoder observable hermitian current) +
      SourceWeightedRecovery.error (distribution observable hermitian current) pointer
        (fun index => bestDecoder observable hermitian current (pointer index)) decoder :=
  SourceWeightedRecovery.error_decomposition (distribution observable hermitian current) pointer
    (task observable hermitian) decoder

theorem loss_minimal (decoder : Fin 2 → ℂ) :
    loss observable hermitian current (bestDecoder observable hermitian current) ≤ loss observable hermitian current decoder :=
  SourceWeightedRecovery.optimal_lower_bound (distribution observable hermitian current) pointer
    (task observable hermitian) decoder

theorem bestDecoder_mean :
    (∑ atom : Fin 2, (((distribution observable hermitian current).map pointer) atom).toReal *
      (bestDecoder observable hermitian current atom).re) = energy observable (bodyRead current.joint) := by
  have source := congrArg Complex.re
    (SourceWeightedRecovery.optimal_first_moment (distribution observable hermitian current) pointer
      (task observable hermitian))
  have realSource : (∑ atom : Fin 2, (((distribution observable hermitian current).map pointer) atom).toReal *
      (bestDecoder observable hermitian current atom).re) =
        ∑ index : PointerIndex, (distribution observable hermitian current index).toReal * outcome observable hermitian index := by
    simpa only [Complex.re_sum, Complex.smul_re, smul_eq_mul, bestDecoder,
      SourceWeightedRecovery.observed, task, Complex.ofReal_re] using source
  exact realSource.trans (first_moment observable hermitian current)

end
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Born
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
