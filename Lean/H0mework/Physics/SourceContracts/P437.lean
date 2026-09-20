import H0mework.Physics.SourceForms.P436

/-!
# Proposition 437: holy-grail front door as an atom-native sigma corridor

P436 reduces the current formal-exact good-cover holy-grail output to a raw
matrix-only producer.  This file connects that matrix-only producer back to
the atom-native physical sigma corridor from P413/P414.

The result is the current tight front door:

`formal-exact holy-grail output` exists iff one primitive atom object has

* `fourPi = 4*pi`;
* every selected Yukawa sigma below the weak sigma endpoint.

The matrix/RG table is not a separate physical obligation at this layer; it is
the finite star-graph presentation of the same atom-native corridor.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Direct conversions between the corridor and matrix-only producer -/

namespace PrimitiveAtomNativePhysicalSigmaCorridor

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: an atom-native sigma corridor supplies the raw matrix-only
producer by using the minimal selected-Yukawa-to-weak star graph. -/
def toRawMatrixUnifiedProducerFields
    (P : PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier) :
    RawMatrixUnifiedProducerFields Index A CKMCarrier where
  toGrandUnificationPrimitiveProducerAtoms := P.atoms
  step := minimalAtomNativeSigmaWeakStep
  reach_not_sigma_order :=
    minimalAtomNativeSigmaWeakStep_reach_not_sigma_order P.atoms
  fourPi_eq_realFourPi := P.fourPi_eq_realFourPi
  matrix_reaches_weak := by
    intro g s
    exact RGStepReach.tail (RGStepReach.refl _)
      (by exact ⟨yukawaMatrixParameter g s, rfl, rfl⟩)
  step_sigma_monotone := by
    intro a b hab
    rcases hab with ⟨y, hsrc, hdst⟩
    subst hsrc
    subst hdst
    exact P.selected_yukawa_sigma_le_weak y

end PrimitiveAtomNativePhysicalSigmaCorridor

namespace RawMatrixUnifiedProducerFields

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 2: a raw matrix-only producer supplies the atom-native sigma
corridor, because local step monotonicity propagates along the selected
Yukawa-to-weak reachability paths. -/
def toPrimitiveAtomNativePhysicalSigmaCorridor
    (R : RawMatrixUnifiedProducerFields Index A CKMCarrier) :
    PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier where
  atoms := R.toGrandUnificationPrimitiveProducerAtoms
  fourPi_eq_realFourPi := R.fourPi_eq_realFourPi
  selected_yukawa_sigma_le_weak := by
    intro y
    let Cmat :
        MatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
          R.toGrandUnificationPrimitiveProducerAtoms :=
      R.toMatrixPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    let Cnamed :
        PrimitiveAtomNativeSigmaYukawaRGPathTableProducer
          R.toGrandUnificationPrimitiveProducerAtoms :=
      Cmat.toPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
    let Cstep :
        PrimitiveAtomNativeSigmaRGStepPathProducer
          R.toGrandUnificationPrimitiveProducerAtoms :=
      Cnamed.toPrimitiveAtomNativeSigmaRGStepPathProducer
    exact Cstep.sigma_monotone_of_reach
      (Cstep.selected_yukawa_reaches_weak y)

end RawMatrixUnifiedProducerFields

/-! ## Exact front-door normal form -/

/-- THEOREM 3: the raw matrix-only producer and the atom-native physical sigma
corridor have the same existence content. -/
theorem rawMatrixUnifiedFields_nonempty_iff_atomNativeSigmaCorridor
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (RawMatrixUnifiedProducerFields Index A CKMCarrier) ↔
      Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier) := by
  constructor
  · rintro ⟨R⟩
    exact ⟨R.toPrimitiveAtomNativePhysicalSigmaCorridor⟩
  · rintro ⟨P⟩
    exact ⟨P.toRawMatrixUnifiedProducerFields⟩

/-- THEOREM 4: under the P435 formal-exact geometry audit, the current
strict good-cover holy-grail output exists exactly when the atom-native sigma
corridor exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_atomNativeSigmaCorridor_under_currentFormalExactGeometry
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor
        Index A CKMCarrier) := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_rawMatrixUnifiedFields_under_currentFormalExactGeometry.trans
      rawMatrixUnifiedFields_nonempty_iff_atomNativeSigmaCorridor

/-- THEOREM 5: an atom-native sigma corridor directly supplies a formal-exact
strict good-cover holy-grail output.  P436 gives the central-constants payload
from the resulting raw matrix producer. -/
theorem atomNativeSigmaCorridor_supplies_currentFormalExactGeometry_holyGrailOutput
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    PrimitiveAtomNativePhysicalSigmaCorridor Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro P
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_atomNativeSigmaCorridor_under_currentFormalExactGeometry).mpr
      ⟨P⟩

end StandardModelConstraint
end SaturationMonoid
