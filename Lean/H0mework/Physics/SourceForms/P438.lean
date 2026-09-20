import H0mework.Physics.SourceContracts.P437

/-!
# Proposition 438: naked primitive holy-grail normal form

P437 identifies the current formal-exact strict good-cover holy-grail front
door with P413's atom-native physical sigma corridor.  This file removes even
that record wrapper.

The current Lean front door is the naked primitive statement:

there exists one `GrandUnificationPrimitiveProducerAtoms` object whose native
fields satisfy

* `atoms.fourPi = realFourPi`;
* `atoms.sigma (yukawa y) <= atoms.sigma weak` for every selected Yukawa row.

Everything else in the current formal-exact holy-grail output is downstream of
that primitive atom object and those two native physical conditions.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-- The naked primitive atom-native sigma-corridor predicate, with no record
wrapper. -/
def ExistsNakedPrimitiveAtomNativeSigmaCorridor
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ∃ atoms : GrandUnificationPrimitiveProducerAtoms Index A CKMCarrier,
    atoms.fourPi = realFourPi ∧
      ∀ y : YukawaParameter,
        atoms.sigma (StandardModelScaleCode.yukawa y) ≤
          atoms.sigma StandardModelScaleCode.weak

/-- THEOREM 1: P413's atom-native corridor record is exactly the naked
primitive atom plus its two native physical fields. -/
theorem atomNativeSigmaCorridor_nonempty_iff_nakedPrimitive
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (PrimitiveAtomNativePhysicalSigmaCorridor
        Index A CKMCarrier) ↔
      ExistsNakedPrimitiveAtomNativeSigmaCorridor
        Index A CKMCarrier := by
  constructor
  · rintro ⟨P⟩
    exact ⟨P.atoms, P.fourPi_eq_realFourPi, P.selected_yukawa_sigma_le_weak⟩
  · rintro ⟨atoms, hfour, hyukawa⟩
    exact
      ⟨{ atoms := atoms
         fourPi_eq_realFourPi := hfour
         selected_yukawa_sigma_le_weak := hyukawa }⟩

/-- THEOREM 2: under the P435 formal-exact geometry audit, the current strict
good-cover holy-grail output exists exactly when the naked primitive
atom-native sigma corridor exists. -/
theorem goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_nakedPrimitive_under_currentFormalExactGeometry
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) ↔
      ExistsNakedPrimitiveAtomNativeSigmaCorridor
        Index A CKMCarrier := by
  exact
    goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_atomNativeSigmaCorridor_under_currentFormalExactGeometry.trans
      atomNativeSigmaCorridor_nonempty_iff_nakedPrimitive

/-- THEOREM 3: a naked primitive atom-native sigma corridor directly supplies
a formal-exact strict good-cover holy-grail output. -/
theorem nakedPrimitive_supplies_currentFormalExactGeometry_holyGrailOutput
    {Index A CKMCarrier CoverIndex E F : Type*} [AddCommGroup A]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [Inhabited CoverIndex] :
    ExistsNakedPrimitiveAtomNativeSigmaCorridor Index A CKMCarrier ->
      Nonempty
        (StrictPhysicalMatrixUnifiedHolyGrailOutput
          Index A CKMCarrier
          (GoodCoverPoincarePhysicalGeometry CoverIndex E F)
          GoodCoverPoincarePhysicalGeometry.adapter) := by
  intro h
  exact
    (goodCoverPoincareStrictMatrixUnifiedOutput_nonempty_iff_nakedPrimitive_under_currentFormalExactGeometry).mpr h

end StandardModelConstraint
end SaturationMonoid
