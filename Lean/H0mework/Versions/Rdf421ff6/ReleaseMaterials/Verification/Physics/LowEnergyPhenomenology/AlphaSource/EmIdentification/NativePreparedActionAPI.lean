import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourceFullSylvesterMatrix
import Lean.Elab.Term

open Lean Elab Term Meta
private def preparedActionName (leaf : Name) : Name :=
  (Name.num `_private.H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMeromorphicResponse 0).append
    (`LowEnergy.SourcePropagationAlgebraicResponse ++ leaf)

-- Emit fixed existing kernel declarations; no target, caller certificate, or goal data is read.
elab "originalLeftAssembly" : term =>
  pure <| mkConst (preparedActionName `leftMultiplication)
elab "originalRightPolynomial" : term =>
  mkConstWithFreshMVarLevels (preparedActionName `right_polynomial)

#check originalLeftAssembly
#check originalRightPolynomial
