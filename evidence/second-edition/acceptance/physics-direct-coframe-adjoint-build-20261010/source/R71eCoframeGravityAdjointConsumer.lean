import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationCoframeInverseJets
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalSourcePropagationNativeGravityScalarReturn
set_option autoImplicit false
open LowEnergy.SourcePropagationNativeActionHessian
example (p : Fin 4 → ℂ) : (nativeJacobi (-p)).transpose = nativeJacobi p :=
  nativeJacobi_formalAdjoint p
#print axioms nativeJacobi_formalAdjoint
