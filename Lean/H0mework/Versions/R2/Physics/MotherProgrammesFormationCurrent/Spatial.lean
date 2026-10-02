import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.Stream
import H0mework.Versions.R2.Physics.MotherProgrammesFormation.NativeInitial

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial

open StageNineCanonicalCauchyState
open Topology Filter

noncomputable section

abbrev RationalPoint := Fin 3 → ℚ

def rationalPoint (point : RationalPoint) : StageNineSpatialPoint :=
  WithLp.toLp 2 (fun direction => (point direction : ℝ))

theorem rationalPoint_dense : IsDenseInducing rationalPoint := by
  have cast : IsDenseInducing (fun point : RationalPoint => fun i => (point i : ℝ)) :=
    ⟨Topology.IsInducing.piMap (fun _ => Rat.isEmbedding_coe_real.isInducing),
      DenseRange.piMap (fun _ : Fin 3 => Rat.denseRange_cast)⟩
  have coordinates : IsDenseInducing (fun point : Fin 3 → ℝ => WithLp.toLp 2 point) :=
    ⟨(PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.isInducing,
      (PiLp.homeomorph 2 (fun _ : Fin 3 => ℝ)).symm.surjective.denseRange⟩
  exact ⟨coordinates.isInducing.comp cast.isInducing,
    coordinates.dense.comp cast.dense coordinates.continuous⟩

/-- Total neighborhood-limit decoder on a fixed rational spatial grid. -/
def extendReal (samples : RationalPoint → ℝ) : StageNineSpatialPoint → ℝ :=
  rationalPoint_dense.extend samples

theorem extendReal_recovers (field : StageNineSpatialPoint → ℝ)
    (continuous : Continuous field) :
    extendReal (fun point => field (rationalPoint point)) = field :=
  rationalPoint_dense.extend_unique (fun _ => rfl) continuous

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial
