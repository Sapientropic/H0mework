import H0mework.Physics.SourceContracts.P420

/-!
# Proposition 421: atom-native final Standard-Model holy-grail kernel

P420 exposes the concrete Standard-Model holy-grail front door as a raw kernel:
a zero-free certificate, a non-tautological physical scale relation, physical
`fourPi`, selected Yukawa-to-weak reachability, physical-alpha monotonicity,
and a 4D Poincare-duality geometry certificate.

This file lowers the alpha/RG half of that front door to the already certified
P415 finite surface: one primitive atom object carrying the explicit nine-row
native sigma RG path table, plus the same 4D geometry certificate.

Boundary: this is still a normal-form theorem.  It does not derive the nine
table rows from beta functions/threshold matching, and it does not construct
Poincare duality from a smooth physical spacetime.  It proves that no extra
wrapper remains between the concrete holy-grail output and those two raw
producer obligations.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Atom-native final front door -/

/-- The current tightest atom-native front door for the concrete
Standard-Model Poincare holy-grail surface:

* an explicit nine-row primitive sigma RG table;
* a 4D Poincare generation-slot geometry certificate.

This is not a new assumption over P420.  It is the P415 normal form paired with
the geometry certificate that P419/P420 already require. -/
def ExistsAtomNativeNineRowPoincareGeometryProducer
    (Index A CKMCarrier : Type*) [AddCommGroup A] : Prop :=
  ExistsPrimitiveAtomNativeSigmaYukawaRGPathTableProducer
      Index A CKMCarrier ∧
    Nonempty FourDimensionalPoincareGenerationSlotCertificate

/-! ## Equivalence to previous front doors -/

/-- THEOREM 1: P419's physical-alpha/geometry front door is exactly the
atom-native nine-row sigma table plus geometry certificate. -/
theorem physicalAlphaRGPoincareGeometry_nonempty_iff_atomNativeNineRow_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier ↔
      ExistsAtomNativeNineRowPoincareGeometryProducer
        Index A CKMCarrier := by
  constructor
  · rintro ⟨hphysical, hgeometry⟩
    have hreceipt :
        Nonempty
          (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
            Index A CKMCarrier) :=
      (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mpr
        hphysical
    exact
      ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable).mp
          hreceipt,
        hgeometry⟩
  · rintro ⟨htable, hgeometry⟩
    have hreceipt :
        Nonempty
          (SingleSourcePhysicalGrandUnificationHolyGrailReceipt
            Index A CKMCarrier) :=
      (singleSourcePhysicalHolyGrailReceipt_nonempty_iff_sigmaYukawaRGPathTable).mpr
        htable
    exact
      ⟨(singleSourcePhysicalHolyGrailReceipt_nonempty_iff_physicalAlphaRGMonotonicity).mp
          hreceipt,
        hgeometry⟩

/-- THEOREM 2: the P420 expanded raw kernel exists exactly when the atom-native
nine-row sigma table and the 4D geometry certificate exist. -/
theorem concreteHolyGrailKernel_nonempty_iff_atomNativeNineRow_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) ↔
      ExistsAtomNativeNineRowPoincareGeometryProducer
        Index A CKMCarrier := by
  exact
    standardModelPoincareHolyGrailOutput_nonempty_iff_concreteKernel.symm.trans
      (standardModelPoincareHolyGrailOutput_nonempty_iff_physicalAlphaRG_and_geometry.trans
        physicalAlphaRGPoincareGeometry_nonempty_iff_atomNativeNineRow_and_geometry)

/-- THEOREM 3: the concrete Standard-Model Poincare-resolved surface is exactly
the atom-native nine-row sigma table plus the 4D geometry certificate. -/
theorem standardModelPoincareResolved_nonempty_iff_atomNativeNineRow_and_geometry
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      ExistsAtomNativeNineRowPoincareGeometryProducer
        Index A CKMCarrier := by
  exact
    standardModelPoincareResolved_nonempty_iff_concreteKernel.trans
      concreteHolyGrailKernel_nonempty_iff_atomNativeNineRow_and_geometry

/-- THEOREM 4: compact citation form.  The atom-native nine-row table plus 4D
geometry certificate yields the full concrete holy-grail output package. -/
theorem atomNativeNineRow_and_geometry_concrete_holy_grail_output
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsAtomNativeNineRowPoincareGeometryProducer Index A CKMCarrier ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro h
  exact
    physicalAlphaRG_and_geometry_concrete_holy_grail_output
      ((physicalAlphaRGPoincareGeometry_nonempty_iff_atomNativeNineRow_and_geometry).mpr h)

end StandardModelConstraint
end SaturationMonoid
