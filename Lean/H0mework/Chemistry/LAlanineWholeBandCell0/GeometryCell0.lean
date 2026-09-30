import H0mework.Chemistry.LAlanineWholeBandCell0.ContinuationFull
import H0mework.Chemistry.LAlanineTrueFlowGeometry.FlowSourceNoFold
import H0mework.Chemistry.LAlanineWholeBandCell0.GeometrySeedPlane
import H0mework.Chemistry.LAlanineWholeBandCell0.GeometryTransverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell0Geometry

open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator ContinuousGradient WholeBandGeometry TrueFlowGeometry
open TrueFlowDifferential WholeBandActual WholeBandCell0Continuation Matrix Set
open scoped Matrix
noncomputable section

theorem cell0_full_transverse (p : Cell0Point) (t : ℝ)
    (time : t ∈ Icc (-(1/2 : ℝ)) (1/2)) :
    (1/20 : ℝ) < seedNormal ⬝ᵥ sourceGradient (rawFlow (cellSeed 0 p.val) t) := by
  obtain ⟨d, i, _, fields⟩ := cell0_full_field_cover p t time
  exact WholeBandTransverse.actual_cell0_field_transverse d i .tube _ fields

theorem cell0_plane_strictMono (p : Cell0Point) :
    StrictMonoOn (fun t => planeCoordinate (rawFlow (cellSeed 0 p.val) t)) (Icc (-(1/2 : ℝ)) (1/2)) :=
  rawPlane_strictMono_of_actual _ (cell0_full_original p)
    (fun t ht => (by norm_num : (0 : ℝ) < 1/20).trans (cell0_full_transverse p t ht))

def cell0ParameterMap (p : Point) : Point := rawFlow (cellSeed 0 p) (p 2)

theorem cell0_parameter_meeting_classification (p q : Cell0Point) (a b : Time) :
    rawFlow (cellSeed 0 p.val) a = rawFlow (cellSeed 0 q.val) b ↔
      p.val 0 = q.val 0 ∧ p.val 1 = q.val 1 ∧ (a : ℝ) = b := by
  rw [rawFlow_meeting_classification _ _ (cell_seed_plane_zero 0 p.val) (cell_seed_plane_zero 0 q.val)
    (cell0_plane_strictMono p) (cell0_plane_strictMono q) a b,
    cell_seed_eq_iff_coordinates 0 0 p.val q.val p.property q.property]
  exact and_assoc

theorem cell0ParameterMap_injective :
    Function.Injective (fun p : Cell0Point => cell0ParameterMap p.val) := by
  intro p q meeting
  have classification := (cell0_parameter_meeting_classification p q
    ⟨p.val 2, p.property.2.2⟩ ⟨q.val 2, q.property.2.2⟩).mp meeting
  apply Subtype.ext
  funext i
  fin_cases i
  · exact classification.1
  · exact classification.2.1
  · exact classification.2.2

theorem cell0ParameterMap_injOn : InjOn cell0ParameterMap (cellDomain 0) := by
  intro p hp q hq meeting
  have same : (⟨p,hp⟩ : Cell0Point) = ⟨q,hq⟩ := cell0ParameterMap_injective meeting
  exact congrArg Subtype.val same

end
end LAlanine40K2025.BasinRefinement.WholeBandCell0Geometry
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
