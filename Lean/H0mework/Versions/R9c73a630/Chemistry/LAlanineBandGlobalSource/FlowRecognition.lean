import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandGlobalSource.FlowGlobal
import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandContinuation.Full

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.GlobalSource

open SourceGaussianModel ContinuousGradient WholeBandSource WholeBandGeometry
open WholeBandContinuation TrueFlowDifferential Set ODE
noncomputable section

/-- The already paid original cell flow is the restriction of the same global source flow. -/
theorem flow_restricts_original_cell (c : FullBandCell) (fields : ∀ d, DirectionFields c d)
    (p : Point) (inside : p ∈ cellDomain c) :
    EqOn (flow (cellSeed c p)) (rawFlow (cellSeed c p)) (Icc (-(1/2 : ℝ)) (1/2)) := by
  have original := full_original c fields p inside
  apply ODE_solution_unique_of_mem_Icc
    (v := fun _ => sourceGradient) (s := fun _ => univ)
    (fun _ _ => sourceGradient_globally_lipschitz.lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-(1/2 : ℝ)) (1/2) by constructor <;> norm_num)
    (flow_continuous _).continuousOn
    (fun t _ => flow_hasDerivAt _ t) (fun _ _ => mem_univ _)
    (HasDerivWithinAt.continuousOn original)
    (fun t ht => (original t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (fun _ _ => mem_univ _)
  exact (flow_starts _).trans (full_starts c p).symm

end
end LAlanine40K2025.BasinRefinement.GlobalSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
