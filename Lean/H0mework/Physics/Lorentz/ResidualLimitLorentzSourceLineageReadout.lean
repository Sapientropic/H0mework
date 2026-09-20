import H0mework.Physics.Lorentz.ResidualLimitLorentzSourceTransportLocalCompatibilityAudit

/-!
# S9-C3h55: source-derived q_D provenance and Lorentz readout boundary

C3h31 computed the sparse coordinate `q_D` as the unique preimage of the
residual-limit differential response inside the existing 24-coordinate
Lorentz origin-response carrier.  This module makes that provenance explicit:
the displayed `q_D` is exactly the existing response inverse applied to the
24 basis coordinates read from the actual differential response `D`.  It is
therefore a derived response readout, not a primitive source field or a new
physical parameter.

C3h32 then uses `q_D` together with the same positive source's `sigma` and
source-generated origin connection to construct the uniquely forced relative
origin `q*`.  The package below keeps the exact P506/L0 lineage, selected
endpoint `11`, source-derived coordinate formula, and actual Lorentz balance
readout in one theorem about that fixed source.

The absolute `q_D` audit reader is nevertheless not the C3h32 one-step
transport reader.  A concrete origin-connection component distinguishes them.
This is a narrow negative regression against treating direct installation of
the diagonal response preimage as one-step source reachability.  It is not a
whole-shell or source-class no-go, does not claim full nine-field production,
and does not authorize a new field, source slot, branch receipt, or repair
carrier.
-/

open SaturationMonoid

namespace SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceLineageReadout

open StageEightProofFreeSource
open StageNineConnectionSectorSourceBalance
open StageNineEnrichedProofFreeSource
open StageNineHolonomicField
open StageNineLorentzConnectionPointwiseEquation
open StageNineLorentzConnectionVariation
open StageNineResidualLimitLorentzClassObstruction
open StageNineResidualLimitLorentzOriginResponsePreimage
open StageNineResidualLimitLorentzSourceTransport
open StageNineResidualLimitLorentzSourceTransportLocalCompatibilityAudit
open StageNineResidualLimitSameCurvatureLorentzTransport
open RepresentationArithmeticAtomProjectionDefect.BorromeanPreRealization

noncomputable section

set_option autoImplicit false

/-! ## q_D is derived from the actual differential response -/

/-- The 24 basis coordinates read directly from the actual differential
response of the fixed positive-source residual-limit carrier. -/
def sourceDerivedReferenceDivergenceCoordinates : LorentzBivectorOneForm :=
  fun formDirection internalPair =>
    residualLimitReferenceDivergenceResponse
      (residualLimitLorentzBasisDirection formDirection internalPair)

/-- The displayed sparse `q_D` is not an independently selectable source
slot.  It is exactly the existing response operator's inverse applied to the
actual differential-response coordinates. -/
theorem residualLimitReferenceDivergenceOriginPreimage_eq_sourceDerived :
    residualLimitReferenceDivergenceOriginPreimage =
      residualLimitOriginAlgebraicResponsePreimage
        sourceDerivedReferenceDivergenceCoordinates := by
  funext formDirection internalPair
  fin_cases formDirection <;> fin_cases internalPair <;>
    simp [residualLimitReferenceDivergenceOriginPreimage,
      residualLimitOriginAlgebraicResponsePreimage,
      sourceDerivedReferenceDivergenceCoordinates,
      residualLimitReferenceDivergenceResponse_apply,
      residualLimitLorentzBasisDirection] <;>
    norm_num

/-! ## Fixed-positive-source q* lineage and Lorentz readout -/

/-- All inputs used by the parameter-free C3h32 endpoint are tied to the same
fixed proof-free positive source.  This packages provenance only for the
Lorentz response projection; it is not a full joint-shell credential. -/
theorem residualLimitRequiredTransportReader_sameSourceProjection :
    positiveSmoothUnifiedSource.stageEight.generatedP506L0Lineage =
        canonicalP506SourceAffineL0ObservableLineageReference ∧
      positiveSmoothUnifiedSource.stageEight.generatedSelectedEndpoint
          canonicalSource_generatedLineage_height_pos = 11 ∧
      residualLimitRequiredTransportRelativeOrigin =
        -positiveSmoothUnifiedSource.legacy.sigma •
          (residualLimitSourceOriginCoordinate -
            residualLimitOriginAlgebraicResponsePreimage
              sourceDerivedReferenceDivergenceCoordinates) ∧
      (fun direction =>
        lorentzGravityBFBalanceCoefficient
          residualLimitRequiredTransportReader direction 0) =
        (1 - positiveSmoothUnifiedSource.legacy.sigma) •
          positiveResidualLimitLorentzBalance := by
  refine ⟨positiveSmoothUnifiedSource_generates_exactP506L0Lineage,
    positiveSmoothUnifiedSource_generates_endpoint_eleven, ?_,
    residualLimitRequiredTransportReader_gravityBFBalance⟩
  unfold residualLimitRequiredTransportRelativeOrigin
  rw [residualLimitReferenceDivergenceOriginPreimage_eq_sourceDerived]

/-! ## Direct q_D installation is not the one-step q* endpoint -/

/-- The absolute `q_D` audit reader is not the C3h32 one-step source-transport
endpoint.  The coordinate `q_D` is a legal derived diagonal readout, but
directly installing it does not establish one-step source reachability. -/
theorem residualLimitAbsoluteQDReader_ne_requiredTransportReader :
    residualLimitArbitraryOriginReader
        residualLimitReferenceDivergenceOriginPreimage ≠
      residualLimitRequiredTransportReader := by
  intro readersEqual
  have entryEqual := congrArg
    (fun reader : StageNineHolonomicConfiguration =>
      reader.gravityConnection 0 1 0 2) readersEqual
  rw [residualLimitArbitraryOriginReader_gravityConnection_origin,
    residualLimitReferenceDivergenceOriginPreimage_lift_one_zero_two,
    residualLimitRequiredTransportReader_connection_origin_one_zero_two]
    at entryEqual
  norm_num at entryEqual

end

end SaturationMonoid.PhysicsCore.StageNineResidualLimitLorentzSourceLineageReadout
