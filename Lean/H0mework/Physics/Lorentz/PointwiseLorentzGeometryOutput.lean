import H0mework.Physics.Lorentz.PointwiseLorentzOmegaGluing

/-!
# Dependency-light pointwise Lorentz geometry output

This module packages the metric, Hodge, affine/spin connection, and
identity-chart omega-gluing readouts of one nondegenerate coframe jet.  It has
no generated endpoint, repair, P950, incidence, or running dependency.
-/

namespace SaturationMonoid.PhysicsCore.GeneratedEndpointQuadraticCoframeSource

noncomputable section

structure PointwiseLorentzGeometryOutput
    (J : PointwiseLorentzianCoframeJet) where
  metric : LorentzianMetric
  metric_eq : metric = J.metric
  hodge : LorentzianTwoFormHodgeOperator
  hodge_eq : hodge = lorentzianCoframeHodge
  spin : PointwiseLorentzianCoframeJet.LorentzSpinConnectionOutput J
  omegaGluing : PointwiseLorentzianCoframeJet.LorentzOmegaGluingOutput J

def producePointwiseLorentzGeometryFromJet
    (J : PointwiseLorentzianCoframeJet)
    (hcoframe : Matrix.det J.coframe ≠ 0) :
    PointwiseLorentzGeometryOutput J where
  metric := J.metric
  metric_eq := rfl
  hodge := lorentzianCoframeHodge
  hodge_eq := rfl
  spin := J.produceLorentzSpinConnection hcoframe
  omegaGluing := J.produceLorentzOmegaGluing hcoframe

end
end SaturationMonoid.PhysicsCore.GeneratedEndpointQuadraticCoframeSource
