import H0mework.Versions.R2.Arithmetic.RiemannLineage.DerivedLineagePoint
import H0mework.Versions.R2.Arithmetic.RiemannLineage.FullRowSuccessor

/-!
# Complete-datum caps for the full actual row family

The endpoint cochain and strict source boundary of an arbitrary corrected
derived point are evaluated together against every actual factor row.  For a
q-rich point the source correction vanishes, leaving the literal quotient cap
and its source-owned inhomogeneous outer shift.  No point specialization or
fixedness statement occurs here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace QRich

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockFrame
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockLinearGlobalEndpointSection
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedSolutionCofinal
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockDerivedPointActualDatum
open CanonicalUnitArithmeticFactorizationFullEulerWholePrimeDualBlockWholeComplexAdjugateTotalFiber
open CochainMappingCoconeMappedBoundaryAtomOver

noncomputable section

noncomputable def rawFamilyCap (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage)
    (coordinate : LocalWholeComplex stage ⟶ blockRowFamilySingle stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  (localDerivedEndpointCochain stage point).comp
    (Cochain.ofHom coordinate) (add_zero (-1))

noncomputable def sourceFamilyCorrectionCap (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  (Cochain.ofHom (localDerivedStrictSource stage point)).comp
    (Cochain.ofHomotopy (blockFactorizationFamilyHomotopy stage))
      (zero_add (-1))

noncomputable def rawFamilyPrimePowerQuotientCap (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  (rawFamilyCap stage point (blockQuotientFamilyMap stage)).comp
    (Cochain.ofHom (blockPrimePowerFamilyMap stage)) (add_zero (-1))

noncomputable def rawFamilyDifferenceCap (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  rawFamilyCap stage point
    (blockWholeFamilyMap stage -
      blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage)

theorem rawFamilyDifferenceCap_expand (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    rawFamilyDifferenceCap stage point =
      rawFamilyCap stage point (blockWholeFamilyMap stage) -
        rawFamilyPrimePowerQuotientCap stage point := by
  ext source target related
  simp [rawFamilyDifferenceCap, rawFamilyCap,
    rawFamilyPrimePowerQuotientCap, Cochain.ofHom_sub,
    Cochain.ofHom_comp]

theorem rawFamilyDifferenceCap_add_sourceCorrection (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    rawFamilyDifferenceCap stage point +
        sourceFamilyCorrectionCap stage point = 0 := by
  let endpoint := localDerivedEndpointCochain stage point
  let homotopy := Cochain.ofHomotopy
    (blockFactorizationFamilyHomotopy stage)
  have doubleZero : endpoint.comp homotopy
      (show (-1 : ℤ) + (-1) = -2 by omega) = 0 := by
    ext source : 1
    by_cases sourceOne : source = 1
    · subst source
      rename_i target related
      have targetNegOne : target = -1 := by omega
      subst target
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0
        (ModuleCat.of BlockCoordinateRing (BlockRowFamily stage)) (-1)
        (by norm_num)).eq_of_tgt _ _
    · rename_i target related
      exact (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 1
        (CochainMappingCoconeMappedBoundaryAtomOver.ScalarUnit
          (R := BlockCoordinateRing)) source sourceOne).eq_of_src _ _
  have deltaDouble := congrArg (δ (-2) (-1)) doubleZero
  rw [δ_zero] at deltaDouble
  rw [δ_comp endpoint homotopy (by omega)
      0 0 (-1) (by omega) (by omega) (by omega)] at deltaDouble
  have endpointDelta : δ (-1) 0 endpoint =
      -Cochain.ofHom (localDerivedStrictSource stage point) :=
    localDerivedEndpointCochain_delta stage point
  have homotopyDelta : δ (-1) 0 homotopy =
      Cochain.ofHom
        (blockWholeFamilyMap stage -
          blockQuotientFamilyMap stage ≫ blockPrimePowerFamilyMap stage) := by
    dsimp only [homotopy]
    rw [δ_ofHomotopy, Cochain.ofHom_zero, sub_zero]
  rw [homotopyDelta, endpointDelta] at deltaDouble
  change rawFamilyDifferenceCap stage point +
      sourceFamilyCorrectionCap stage point = 0
  simpa [rawFamilyDifferenceCap, rawFamilyCap,
    sourceFamilyCorrectionCap, endpoint, homotopy] using deltaDouble

theorem rawFamilyCap_row (stage : Nat)
    (point : ScalarSingleOne (R := BlockCoordinateRing) ⟶
      LocalDerivedSolution stage) :
    rawFamilyCap stage point (blockWholeFamilyMap stage) -
        rawFamilyPrimePowerQuotientCap stage point +
      sourceFamilyCorrectionCap stage point = 0 := by
  rw [← rawFamilyDifferenceCap_expand]
  exact rawFamilyDifferenceCap_add_sourceCorrection stage point

theorem sourceFamilyCorrectionCap_localQRichDerivedPoint_eq_zero
    (stage : Nat) (base : BlockDualBase) :
    sourceFamilyCorrectionCap stage
        (localQRichDerivedPoint stage base) = 0 := by
  unfold sourceFamilyCorrectionCap
  rw [localQRichDerivedPoint_strictSource_zero,
    Cochain.ofHom_zero, Cochain.zero_comp]

theorem rawFamilyCap_localQRichDerivedPoint_row
    (stage : Nat) (base : BlockDualBase) :
    rawFamilyCap stage (localQRichDerivedPoint stage base)
        (blockWholeFamilyMap stage) =
      rawFamilyPrimePowerQuotientCap stage
        (localQRichDerivedPoint stage base) := by
  have relation := rawFamilyCap_row stage
    (localQRichDerivedPoint stage base)
  rw [sourceFamilyCorrectionCap_localQRichDerivedPoint_eq_zero,
    add_zero, sub_eq_zero] at relation
  exact relation

noncomputable def qRichFullRowQuotientCap (stage : Nat)
    (base : BlockDualBase) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-1) :=
  rawFamilyCap stage (localQRichDerivedPoint stage base)
    (blockQuotientFamilyMap stage)

theorem qRichFullRowQuotientCap_delta (stage : Nat)
    (base : BlockDualBase) :
    δ (-1) 0 (qRichFullRowQuotientCap stage base) = 0 := by
  unfold qRichFullRowQuotientCap rawFamilyCap
  rw [δ_comp_ofHom, localDerivedEndpointCochain_delta,
    localQRichDerivedPoint_strictSource_zero,
    Cochain.ofHom_zero, neg_zero, Cochain.zero_comp]

theorem rawFamilyPrimePowerQuotientCap_localQRich_delta
    (stage : Nat) (base : BlockDualBase) :
    δ (-1) 0
        (rawFamilyPrimePowerQuotientCap stage
          (localQRichDerivedPoint stage base)) = 0 := by
  unfold rawFamilyPrimePowerQuotientCap
  rw [δ_comp_ofHom]
  change (δ (-1) 0 (qRichFullRowQuotientCap stage base)).comp
      (Cochain.ofHom (blockPrimePowerFamilyMap stage)) (add_zero 0) = 0
  rw [qRichFullRowQuotientCap_delta, Cochain.zero_comp]

/-- The canonical inhomogeneous outer shift retains the actual q cap in its
first coordinate and zero in its second coordinate. -/
noncomputable def qRichFullRowOuterShift (stage : Nat)
    (base : BlockDualBase) :
    Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (CochainComplex.mappingCocone
        (blockPrimePowerFamilyMap stage)) (-1) :=
  CochainComplex.mappingCocone.liftCochain
    (blockPrimePowerFamilyMap stage)
    (qRichFullRowQuotientCap stage base)
    (0 : Cochain (ScalarSingleOne (R := BlockCoordinateRing))
      (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichFullRowOuterShift_comp_fst (stage : Nat)
    (base : BlockDualBase) :
    (qRichFullRowOuterShift stage base).comp
        (Cochain.ofHom (CochainComplex.mappingCocone.fst
          (blockPrimePowerFamilyMap stage))) (add_zero (-1)) =
      qRichFullRowQuotientCap stage base := by
  exact CochainComplex.mappingCocone.liftCochain_comp_fst
    (blockPrimePowerFamilyMap stage)
      (qRichFullRowQuotientCap stage base)
      (0 : Cochain (ScalarSingleOne (R := BlockCoordinateRing))
        (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichFullRowOuterShift_comp_snd (stage : Nat)
    (base : BlockDualBase) :
    (qRichFullRowOuterShift stage base).comp
        (CochainComplex.mappingCocone.snd
          (blockPrimePowerFamilyMap stage))
            (show (-1 : ℤ) + (-1) = -2 by omega) =
      (0 : Cochain (ScalarSingleOne (R := BlockCoordinateRing))
        (blockRowFamilySingle stage) (-2)) := by
  exact CochainComplex.mappingCocone.liftCochain_comp_snd
    (blockPrimePowerFamilyMap stage)
      (qRichFullRowQuotientCap stage base)
      (0 : Cochain (ScalarSingleOne (R := BlockCoordinateRing))
        (blockRowFamilySingle stage) (-2)) (by omega)

theorem qRichFullRowOuterShift_delta (stage : Nat)
    (base : BlockDualBase) :
    δ (-1) 0 (qRichFullRowOuterShift stage base) =
      -(rawFamilyPrimePowerQuotientCap stage
          (localQRichDerivedPoint stage base)).comp
        (CochainComplex.mappingCocone.inr
          (blockPrimePowerFamilyMap stage)).1 (by omega) := by
  unfold qRichFullRowOuterShift
  rw [CochainComplex.mappingCocone.δ_liftCochain
    (blockPrimePowerFamilyMap stage)
      (qRichFullRowQuotientCap stage base)
      (0 : Cochain (ScalarSingleOne (R := BlockCoordinateRing))
        (blockRowFamilySingle stage) (-2)) (by omega) 0 (by omega)]
  rw [qRichFullRowQuotientCap_delta, δ_zero]
  unfold rawFamilyPrimePowerQuotientCap qRichFullRowQuotientCap
  simp

end
end QRich
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
