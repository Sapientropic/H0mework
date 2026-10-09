import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFullCarrier.SourceMaterial

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
open _root_.LAlanineTrueFlowDifferential
open SourceGaussianModel SourceSignedEvaluator WholeBandSource WholeBandGeometry WholeBandContinuation
open WholeBandContinuationParameter TrueFlowDifferential ContinuousGradient Set
noncomputable section

theorem all_original_flows (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c) :
    IsIntegralCurveOn (rawFlow (cellSeed c p)) (fun _ => sourceGradient) (Icc (-(1/2 : ℝ)) (1/2)) :=
  full_original c (fields c) p inside

theorem all_original_initials (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c)
    (d : Direction) (i : Step) : InRectangle (initialBox c d i) (rawFlow (cellSeed c p) (elapsedStart c d i)) :=
  full_initials c (fields c) p inside d i

theorem all_original_endpoints (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c)
    (d : Direction) (i : Step) : InRectangle (endpointBox c d i) (rawFlow (cellSeed c p) (elapsedStop c d i)) :=
  full_endpoints c (fields c) p inside d i

theorem all_literal_reentries (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c)
    (d : Direction) (i : Fin 15) : InRectangle (initialBox c d i.succ) (rawFlow (cellSeed c p) (elapsedStop c d i.castSucc)) :=
  full_next_initial c (fields c) p inside d i

theorem all_actual_jacobians (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c) :
    HasFDerivWithinAt (material.maps c) (material.jacobians c p) (material.domains c) p :=
  actualMap_hasFDerivWithinAt c (fields c) (bounds c) p inside

theorem all_jacobians_nondegenerate (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c) :
    (material.jacobians c p).det ≠ 0 := trueJacobian_det_ne_zero c (fields c) (bounds c) (positive c) p inside

theorem all_actual_meetings (c d : FullBandCell) (p q : Point)
    (hp : p ∈ material.domains c) (hq : q ∈ material.domains d) :
    material.maps c p = material.maps d q ↔ p = q :=
  actual_parameter_meeting c d (fields c) (fields d) (positive c) (positive d) p q hp hq

/-- The retained whole-space source flow supplies every original band restriction. -/
theorem actual_global_flow (initial : Point) (t : ℝ) :
    HasDerivAt (material.globalFlow initial)
      (sourceGradient (material.globalFlow initial t)) t := GlobalSource.flow_hasDerivAt initial t

theorem actual_global_initial (initial : Point) : material.globalFlow initial 0 = initial :=
  GlobalSource.flow_starts initial

theorem actual_global_composition (initial : Point) (s t : ℝ) :
    material.globalFlow initial (s+t) = material.globalFlow (material.globalFlow initial s) t :=
  GlobalSource.flow_add initial s t

theorem actual_global_inverse (initial : Point) (t : ℝ) :
    material.globalFlow (material.globalFlow initial t) (-t) = initial :=
  GlobalSource.flow_inverse initial t

theorem all_global_restrictions (c : FullBandCell) (p : Point) (inside : p ∈ material.domains c) :
    EqOn (material.globalFlow (cellSeed c p)) (rawFlow (cellSeed c p)) (Icc (-(1/2 : ℝ)) (1/2)) :=
  GlobalSource.flow_restricts_original_cell c (fields c) p inside

/-- The same M3/D3 source also supplies a real critical point and an open attracting region. -/
theorem actual_critical_point : sourceGradient material.criticalPoint = 0 :=
  WholeBandAttractor.Atom007.actual_gradient_zero

theorem actual_critical_unique (x : Point)
    (inside : x ∈ Metric.closedBall WholeBandAttractor.Atom007.centre WholeBandAttractor.Atom007.radius)
    (zero : sourceGradient x = 0) : x = material.criticalPoint :=
  WholeBandAttractor.Atom007.actual_zero_unique x inside zero

theorem actual_attracting_volume : 0 < MeasureTheory.volume material.attractingRegion :=
  WholeBandAttractor.Atom007.attracting_positive_volume

theorem actual_attracting_retention (x : Point) (inside : x ∈ material.attractingRegion)
    (t : ℝ) (nonnegative : 0 ≤ t) : material.globalFlow x t ∈ material.attractingRegion :=
  WholeBandAttractor.Atom007.actual_positive_retention x inside t nonnegative

theorem actual_attracting_limit (x : Point) (inside : x ∈ material.attractingRegion) :
    Filter.Tendsto (material.globalFlow x) Filter.atTop (nhds material.criticalPoint) :=
  WholeBandAttractor.Atom007.actual_convergence x inside

end
end LAlanine40K2025.BasinRefinement.WholeBandFullCarrier.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
