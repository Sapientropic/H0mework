import H0mework.Versions.X.NavierStokes.StressAction.StressDynamicsBilinear
import H0mework.Versions.X.NavierStokes.StressWeakInput.OriginalInput

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeStressTimeAlgebra

open NativeResolventCompactness NativeEndpointVelocityCarrier NativeCompleteStressBilinear

noncomputable section

def quadratic (value : State) : NativeCompleteStressCarrier.Space :=
  mixedCLM (wholeVelocity value) (wholeVelocity value)

theorem quadratic_continuous : Continuous quadratic :=
  (mixedCLM.continuous.comp wholeVelocityCLM.continuous).clm_apply wholeVelocityCLM.continuous

theorem quadratic_bound (value : State) : ‖quadratic value‖ ≤ ‖mixedCLM‖ * ‖value‖ ^ 2 := by
  have paid := mixedCLM.le_of_opNorm₂_le_of_le (le_refl ‖mixedCLM‖) (wholeVelocity_norm_le value) (wholeVelocity_norm_le value)
  exact paid.trans_eq (by ring)

theorem quadratic_difference (first last : State) :
    ‖quadratic last - quadratic first‖ ≤ ‖mixedCLM‖ * (‖last‖ + ‖first‖) * ‖last - first‖ := by
  have split : quadratic last - quadratic first =
      mixedCLM (wholeVelocity (last - first)) (wholeVelocity last) +
        mixedCLM (wholeVelocity first) (wholeVelocity (last - first)) := by
    have same : wholeVelocity (last - first) = wholeVelocity last - wholeVelocity first := wholeVelocityCLM.map_sub last first
    rw [same]
    simp only [map_sub, sub_apply]
    change mixedCLM (wholeVelocity last) (wholeVelocity last) - mixedCLM (wholeVelocity first) (wholeVelocity first) = _
    abel
  rw [split]
  have firstBound := mixedCLM.le_of_opNorm₂_le_of_le (le_refl ‖mixedCLM‖)
    (wholeVelocity_norm_le (last - first)) (wholeVelocity_norm_le last)
  have lastBound := mixedCLM.le_of_opNorm₂_le_of_le (le_refl ‖mixedCLM‖)
    (wholeVelocity_norm_le first) (wholeVelocity_norm_le (last - first))
  exact (norm_add_le _ _).trans ((add_le_add firstBound lastBound).trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.NativeStressTimeAlgebra
