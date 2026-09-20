import H0mework.Physics.SourceContracts.P444

/-!
# Proposition 445: master equivalence for the current grand-unification front door

P436 and P444 describe the same current strict good-cover holy-grail output
from two different sides:

* P436: under the formal-exact geometry audit, the output exists exactly when a
  raw matrix-only sigma/RG producer exists.
* P444: under the same audit, the output exists exactly when the SU(7)-resolved
  opened Standard-Model synthesis front door exists.

This file welds those two front doors together and connects them back to the
P415 single-source physical holy-grail receipt.  No new physical derivation is
introduced here.  The point is bookkeeping strength: the present Lean spine now
has one master existence surface instead of three parallel ones.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## Geometry-free receipt and matrix producer equivalence -/

/-- THEOREM 1: the current single-source physical holy-grail receipt exists
exactly when the raw matrix-only producer from P436 is inhabited.

This fuses P415's nine-row receipt normal form, P424's matrix normal form, and
P436's raw matrix-only normal form. -/
theorem singleSourcePhysicalHolyGrailReceipt_nonempty_iff_rawMatrixUnifiedFields :
    Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) := by
  exact
    (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      ((primitiveTable_nonempty_iff_matrixPrimitiveTable
          (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
        (existsMatrixPrimitiveTable_iff_rawMatrixUnifiedFields
          (Index := Index) (A := A) (CKMCarrier := CKMCarrier)))

/-! ## SU(7)-resolved front door and matrix producer equivalence -/

/-- THEOREM 2: after P444 removes the arbitrary SU(7) field and P436 removes
the formal-exact geometry fields, the SU(7)-resolved opened front door is
exactly the raw matrix-only producer.

The proof instantiates the P435 formal-exact audit at the concrete harmless
carrier `(Unit, ℝ, ℝ)` so the statement itself is geometry-free. -/
theorem su7Resolved_iff_rawMatrixUnifiedFields :
    ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) := by
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_su7Resolved_under_currentFormalExactGeometry
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
        (CoverIndex := Unit) (E := ℝ) (F := ℝ)).symm.trans
      (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_rawMatrixUnifiedFields_under_currentFormalExactGeometry
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
        (CoverIndex := Unit) (E := ℝ) (F := ℝ))

/-- THEOREM 3: the SU(7)-resolved opened front door is exactly the current
single-source physical holy-grail receipt.

This is the main bridge: the opened Standard-Model synthesis surface and the
single-source physical receipt surface are the same existence problem in the
current Lean spine. -/
theorem su7Resolved_iff_singleSourcePhysicalHolyGrailReceipt :
    ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier) := by
  exact
    su7Resolved_iff_rawMatrixUnifiedFields
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier) |>.trans
      (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_rawMatrixUnifiedFields
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).symm

/-! ## Central constants from the SU(7)-resolved front door -/

/-- The explicit central-constant statement exposed by the current formal-exact
audit, specialized to the harmless `(Unit, ℝ, ℝ)` cover carrier. -/
def CurrentFormalExactGeometryCentralHolyGrailConstants
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
      Index A CKMCarrier
      (GoodCoverPoincarePhysicalGeometry Unit ℝ ℝ)
      GoodCoverPoincarePhysicalGeometry.adapter,
    NoContinuousFreeParameters
      O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
    (∀ p : ParameterVector ℝ,
      O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
        p StandardModelParameter.qcd_theta = 0) ∧
    alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
    gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
    alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
    O.output.receipt.receipt.spine.target.strongResidualProducer.correctedOutput =
      alphaStrongDisplayed ℝ ∧
    (ckmCPDepthSum : ℝ) *
        O.output.receipt.receipt.spine.target.cpRunningSigma =
      cpRawPhaseClaim ℝ ∧
    cpDeltaCPClaim ℝ =
      cpTauProxy ℝ -
        (ckmCPDepthSum : ℝ) *
          O.output.receipt.receipt.spine.target.cpRunningSigma ∧
    (∀ p : ParameterVector ℝ,
      O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
        ∀ y : YukawaParameter,
          p (yukawaSlot y) =
            O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
              AffineRelaxation.realDecayResidual
                (O.output.receipt.receipt.spine.target.sampled.yukawaLambda y)
                ((O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                    O.output.receipt.receipt.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
                  O.output.receipt.receipt.spine.target.sampled.yukawaStep y)) ∧
    Nonempty
      (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
    Function.Surjective yukawaPoincareSlot ∧
    IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
    AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
      ℝ (ParameterVector ℝ) ∧
    (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
      parameterVectorComponentsEquiv ℝ
          (AffineRelaxation.relaxModule target sigma x) =
        AffineRelaxation.relaxModule
          (parameterVectorComponentsEquiv ℝ target)
          sigma
          (parameterVectorComponentsEquiv ℝ x))

/-- THEOREM 4: the SU(7)-resolved front door directly supplies the central
holy-grail constants already exposed by P436.

This is not an extra assumption: the proof converts the SU(7)-resolved front
door to the raw matrix producer by Theorem 2 and then cites P436's central
constant theorem. -/
theorem su7Resolved_currentFormalExactGeometry_central_holy_grail_constants :
    ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ->
      ∃ O : StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry Unit ℝ ℝ)
          GoodCoverPoincarePhysicalGeometry.adapter,
        NoContinuousFreeParameters
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            p StandardModelParameter.qcd_theta = 0) ∧
        alphaEMFromIntegerConstraint ℝ = (1 : ℝ) / (137 : ℝ) ∧
        gutWeakMixingFromStructuralCards ℝ = threeEighths ℝ ∧
        alphaGUTInverseFromStructuralCards ℝ = ((133 : ℝ) / (3 : ℝ)) ∧
        O.output.receipt.receipt.spine.target.strongResidualProducer.correctedOutput =
          alphaStrongDisplayed ℝ ∧
        (ckmCPDepthSum : ℝ) *
            O.output.receipt.receipt.spine.target.cpRunningSigma =
          cpRawPhaseClaim ℝ ∧
        cpDeltaCPClaim ℝ =
          cpTauProxy ℝ -
            (ckmCPDepthSum : ℝ) *
              O.output.receipt.receipt.spine.target.cpRunningSigma ∧
        (∀ p : ParameterVector ℝ,
          O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.base.constraints p ->
            ∀ y : YukawaParameter,
              p (yukawaSlot y) =
                O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaAmplitude y *
                  AffineRelaxation.realDecayResidual
                    (O.output.receipt.receipt.spine.target.sampled.yukawaLambda y)
                    ((O.output.receipt.receipt.spine.target.sampled.zeroFree.running.pinned.yukawaExponent
                        O.output.receipt.receipt.spine.target.sampled.zeroFree.selectedSeed y : ℝ) *
                      O.output.receipt.receipt.spine.target.sampled.yukawaStep y)) ∧
        Nonempty
          (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
        Function.Surjective yukawaPoincareSlot ∧
        IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) ∧
        AffineRelaxation.UnifiedAffineRelaxationModuleCertificate
          ℝ (ParameterVector ℝ) ∧
        (∀ target x : ParameterVector ℝ, ∀ sigma : ℝ,
          parameterVectorComponentsEquiv ℝ
              (AffineRelaxation.relaxModule target sigma x) =
            AffineRelaxation.relaxModule
              (parameterVectorComponentsEquiv ℝ target)
              sigma
              (parameterVectorComponentsEquiv ℝ x)) := by
  intro h
  rcases
    (su7Resolved_iff_rawMatrixUnifiedFields
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).mp h with
    ⟨R⟩
  exact
    rawMatrixUnified_currentFormalExactGeometry_central_holy_grail_constants
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
      (CoverIndex := Unit) (E := ℝ) (F := ℝ) R

/-- THEOREM 5: the explicit central-constant statement is equivalent to the
SU(7)-resolved front door, not merely downstream of it. -/
theorem currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier := by
  constructor
  · rintro ⟨O, _hfree, _htheta, _halpha, _hweak, _hgut, _hstrong,
      _hcpRaw, _hcpDelta, _hyukawa, _hgen, _hsurj, _hno4, _hparam,
      _hconj⟩
    exact
      (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_su7Resolved_under_currentFormalExactGeometry
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)
        (CoverIndex := Unit) (E := ℝ) (F := ℝ)).mp
        ⟨O⟩
  · exact
      su7Resolved_currentFormalExactGeometry_central_holy_grail_constants
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)

/-- THEOREM 6: compact master equivalence package for downstream citation. -/
theorem currentGrandUnificationFrontDoor_masterEquivalence :
    (ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier)) ∧
    (Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier)) ∧
    (ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier)) := by
  exact
    ⟨su7Resolved_iff_rawMatrixUnifiedFields
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_rawMatrixUnifiedFields
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).symm,
      su7Resolved_iff_singleSourcePhysicalHolyGrailReceipt
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)⟩

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
