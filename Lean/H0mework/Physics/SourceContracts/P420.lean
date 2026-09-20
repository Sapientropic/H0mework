import H0mework.Physics.JointSources.P419

/-!
# Proposition 420: fully expanded Standard-Model holy-grail front door

P419 reduces the concrete Standard-Model holy-grail output to two remaining
central producers:

* a physical alpha-RG monotonicity producer;
* a 4D Poincare generation-slot geometry certificate.

This file removes the last naming opacity in that front door.  It defines one
fully expanded kernel whose fields are the exact remaining data:

* a zero-free Standard-Model certificate;
* a physical scale relation that is not definitionally the target alpha order;
* `fourPi = 4*pi`;
* selected Yukawa scales below the weak endpoint;
* monotonicity of physical alpha `g^2/(4*pi)` along that relation;
* a 4D Poincare-duality cohomology certificate.

Lean proves that this expanded kernel is existence-equivalent to the concrete
holy-grail output of P419.  Thus the central producer debt is now exposed as
raw fields rather than hidden behind two producer names.

Boundary: these fields are still producer obligations.  This file does not
derive beta functions, threshold matching, CKM depths, representation breaking,
or manifold Poincare duality from smooth geometry.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

open AffineRelaxation.GeometryConnection

/-! ## Expanded final producer kernel -/

/-- The fully expanded remaining front door for the concrete Standard-Model
holy-grail output.

This structure is deliberately not a new physics assumption over P419.  It is
P404's physical alpha-RG producer and P280's 4D Poincare-duality cohomology
producer with their fields opened in one object. -/
structure ConcreteStandardModelHolyGrailProducerKernel
    (Index A CKMCarrier : Type*) [AddCommGroup A] where
  zeroFree : ZeroContinuousFreeStandardModelCertificate Index A ℝ CKMCarrier
  physicalScaleLe : StandardModelScaleCode -> StandardModelScaleCode -> Prop
  scale_relation_not_alpha_order :
    physicalScaleLe ≠
      fun a b : StandardModelScaleCode =>
        alphaFromGaugeCoupling realFourPi (zeroFree.running.gaugeCoupling a) ≤
          alphaFromGaugeCoupling realFourPi (zeroFree.running.gaugeCoupling b)
  fourPi_eq_realFourPi : zeroFree.running.fourPi = realFourPi
  selected_yukawa_le_weak :
    ∀ y : YukawaParameter, physicalScaleLe (StandardModelScaleCode.yukawa y)
      StandardModelScaleCode.weak
  alpha_monotone :
    ∀ {a b : StandardModelScaleCode}, physicalScaleLe a b ->
      alphaFromGaugeCoupling realFourPi (zeroFree.running.gaugeCoupling a) ≤
        alphaFromGaugeCoupling realFourPi (zeroFree.running.gaugeCoupling b)
  poincareGeometry : PoincareDualityCohomologyCertificate.{0} 4

namespace ConcreteStandardModelHolyGrailProducerKernel

variable {Index A CKMCarrier : Type*} [AddCommGroup A]

/-- THEOREM 1: the expanded kernel closes back to P404's physical alpha-RG
producer. -/
def toPhysicalAlphaRGMonotonicityProducer
    (K : ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier) :
    PhysicalAlphaRGMonotonicityProducer K.zeroFree where
  physicalScaleLe := K.physicalScaleLe
  scale_relation_not_alpha_order := K.scale_relation_not_alpha_order
  fourPi_eq_realFourPi := K.fourPi_eq_realFourPi
  selected_yukawa_le_weak := K.selected_yukawa_le_weak
  alpha_monotone := K.alpha_monotone

/-- THEOREM 2: the expanded kernel closes back to P280's 4D Poincare generation
slot certificate. -/
def toFourDimensionalPoincareGenerationSlotCertificate
    (K : ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier) :
    FourDimensionalPoincareGenerationSlotCertificate where
  geometry := K.poincareGeometry

/-- THEOREM 3: the expanded kernel supplies P419's two-producer front door. -/
theorem toPhysicalAlphaRGPoincareGeometryProducer
    (K : ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier) :
    ExistsPhysicalAlphaRGPoincareGeometryProducer Index A CKMCarrier := by
  exact
    ⟨⟨K.zeroFree, ⟨K.toPhysicalAlphaRGMonotonicityProducer⟩⟩,
      ⟨K.toFourDimensionalPoincareGenerationSlotCertificate⟩⟩

end ConcreteStandardModelHolyGrailProducerKernel

/-! ## Exact front-door equivalence -/

/-- THEOREM 4: a P419 concrete holy-grail output opens into the fully expanded
producer kernel. -/
theorem concreteHolyGrailKernel_of_output
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) ->
      Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) := by
  rintro ⟨O⟩
  exact
    ⟨{ zeroFree := O.receipt.atoms.toZeroFree
       physicalScaleLe := O.receipt.physicalRG.physicalScaleLe
       scale_relation_not_alpha_order :=
        O.receipt.physicalRG.scale_relation_not_alpha_order
       fourPi_eq_realFourPi := O.receipt.physicalRG.fourPi_eq_realFourPi
       selected_yukawa_le_weak := O.receipt.physicalRG.selected_yukawa_le_weak
       alpha_monotone := O.receipt.physicalRG.alpha_monotone
       poincareGeometry := O.geometry.geometry }⟩

/-- THEOREM 5: the fully expanded producer kernel constructs the P419 concrete
holy-grail output. -/
theorem output_of_concreteHolyGrailKernel
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) ->
      Nonempty (StandardModelPoincareHolyGrailOutput
        Index A CKMCarrier) := by
  rintro ⟨K⟩
  exact
    (standardModelPoincareHolyGrailOutput_nonempty_iff_physicalAlphaRG_and_geometry).mpr
      K.toPhysicalAlphaRGPoincareGeometryProducer

/-- THEOREM 6: final expanded front-door normal form.  The concrete
Standard-Model holy-grail output exists iff the expanded raw producer kernel
exists. -/
theorem standardModelPoincareHolyGrailOutput_nonempty_iff_concreteKernel
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (StandardModelPoincareHolyGrailOutput Index A CKMCarrier) ↔
      Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) := by
  constructor
  · exact concreteHolyGrailKernel_of_output
  · exact output_of_concreteHolyGrailKernel

/-- THEOREM 7: combining P419 and P420, the concrete Standard-Model
Poincare-resolved surface is exactly the expanded raw producer kernel. -/
theorem standardModelPoincareResolved_nonempty_iff_concreteKernel
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    ExistsStandardModelPoincareResolvedSigmaYukawaRGPathTableProducer
        Index A CKMCarrier ↔
      Nonempty (ConcreteStandardModelHolyGrailProducerKernel
        Index A CKMCarrier) := by
  exact
    standardModelPoincareResolved_nonempty_iff_holyGrailOutput.trans
      standardModelPoincareHolyGrailOutput_nonempty_iff_concreteKernel

/-- THEOREM 8: compact citation form.  The expanded kernel yields the complete
P419 output statement. -/
theorem concreteKernel_concrete_holy_grail_output
    {Index A CKMCarrier : Type*} [AddCommGroup A] :
    Nonempty (ConcreteStandardModelHolyGrailProducerKernel Index A CKMCarrier) ->
      ∃ O : StandardModelPoincareHolyGrailOutput Index A CKMCarrier,
        SingleSourceHolyGrailReceiptStatement O.receipt ∧
          Nonempty
            (StandardModelFermionGeneration ≃ FourDimensionalPoincareSlot) ∧
          Function.Surjective yukawaPoincareSlot ∧
          IsEmpty (Fin 4 ↪ StandardModelFermionGeneration) := by
  intro h
  rcases output_of_concreteHolyGrailKernel h with ⟨O⟩
  exact
    ⟨O, O.holy_grail, ⟨O.generation_equiv⟩, O.yukawa_slots_cover,
      O.no_fourth_generation⟩

end StandardModelConstraint
end SaturationMonoid
