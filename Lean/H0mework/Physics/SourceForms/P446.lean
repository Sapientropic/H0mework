import H0mework.Physics.SourceContracts.P445

/-!
# Proposition 446: the grand-unification equivalence ladder

P445 made the current grand-unification front door into one master existence
problem: central constants, the SU(7)-resolved opened synthesis front door,
the raw matrix-only sigma/RG producer, and the single-source receipt are all
equivalent.

This file extends that master equivalence through the whole P437-P444 normal
form ladder.  The result is a compact citation surface: the current central
holy-grail statement is equivalent to every already-opened producer surface
down to the naked primitive atom-native sigma corridor.

No physical instance is manufactured here.  The theorem says that all present
Lean front doors name the same remaining obligation.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

namespace GrandUnificationProducerNormalForm

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-! ## Central statement through the primitive and opened-producer ladder -/

/-- THEOREM 1: the explicit central-constant statement is equivalent to the
naked primitive atom-native sigma corridor. -/
theorem currentCentralHolyGrailConstants_iff_nakedPrimitive :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsNakedPrimitiveAtomNativeSigmaCorridor
        Index A CKMCarrier := by
  exact
    (currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      ((su7Resolved_iff_rawMatrixUnifiedFields
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
        ((rawMatrixUnifiedFields_nonempty_iff_atomNativeSigmaCorridor
          (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
          (atomNativeSigmaCorridor_nonempty_iff_nakedPrimitive
            (Index := Index) (A := A) (CKMCarrier := CKMCarrier))))

/-- THEOREM 2: the central statement is equivalent to the minimal zero-free
sampled-Yukawa-clock physical sigma corridor. -/
theorem currentCentralHolyGrailConstants_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    (currentCentralHolyGrailConstants_iff_nakedPrimitive
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (nakedPrimitive_iff_existsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 3: the central statement is equivalent to the opened zero-free
sampled-Yukawa-clock corridor. -/
theorem currentCentralHolyGrailConstants_iff_openedZeroFree :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    (currentCentralHolyGrailConstants_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (zeroFreeSampledYukawaClocksPhysicalSigmaCorridor_iff_openedZeroFree
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 4: the central statement is equivalent to the opened running-sigma
front door. -/
theorem currentCentralHolyGrailConstants_iff_openedRunningSigma :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    (currentCentralHolyGrailConstants_iff_openedZeroFree
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (openedZeroFree_iff_openedRunningSigma
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 5: the central statement is equivalent to the opened pinned
Standard-Model constraint surface. -/
theorem currentCentralHolyGrailConstants_iff_openedPinned :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier := by
  exact
    (currentCentralHolyGrailConstants_iff_openedRunningSigma
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (openedRunningSigma_iff_openedPinned
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-- THEOREM 6: the central statement is equivalent to the fully opened
producer-relative synthesis front door before P444's SU(7) field elimination. -/
theorem currentCentralHolyGrailConstants_iff_fullyOpenedProducerRelative :
    CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsFullyOpenedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier := by
  exact
    (currentCentralHolyGrailConstants_iff_openedPinned
      (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
      (openedPinned_iff_fullyOpenedProducerRelative
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier))

/-! ## Compact downstream package -/

/-- THEOREM 7: compact ladder package.  Every current opened front door in the
P437-P445 chain is just a different presentation of the same central
holy-grail existence statement. -/
theorem currentGrandUnificationFrontDoor_equivalenceLadder :
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsNakedPrimitiveAtomNativeSigmaCorridor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsOpenedPinnedRunningSigmaZeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsFullyOpenedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      ExistsSU7ResolvedProducerRelativeHolyGrailFrontDoor
        Index A CKMCarrier) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier)) ∧
    (CurrentFormalExactGeometryCentralHolyGrailConstants
        Index A CKMCarrier ↔
      Nonempty
        (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
          Index A CKMCarrier)) := by
  exact
    ⟨currentCentralHolyGrailConstants_iff_nakedPrimitive
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentCentralHolyGrailConstants_iff_zeroFreeSampledYukawaClocksPhysicalSigmaCorridor
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentCentralHolyGrailConstants_iff_openedZeroFree
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentCentralHolyGrailConstants_iff_openedRunningSigma
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentCentralHolyGrailConstants_iff_openedPinned
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentCentralHolyGrailConstants_iff_fullyOpenedProducerRelative
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier),
      (currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
        (su7Resolved_iff_rawMatrixUnifiedFields
          (Index := Index) (A := A) (CKMCarrier := CKMCarrier)),
      (currentFormalExactGeometryCentralHolyGrailConstants_iff_su7Resolved
        (Index := Index) (A := A) (CKMCarrier := CKMCarrier)).trans
        (su7Resolved_iff_singleSourcePhysicalHolyGrailReceipt
          (Index := Index) (A := A) (CKMCarrier := CKMCarrier))⟩

end GrandUnificationProducerNormalForm

end StandardModelConstraint
end SaturationMonoid
