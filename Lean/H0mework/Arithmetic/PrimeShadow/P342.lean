import H0mework.Arithmetic.PrimeProjection.P341

/-!
# Proposition 342: special-fiber transfer has Goldbach strength

P341 isolates the deformation boundary: the absorbing fiber `σ = 1` unifies the
sigma-carrier by collapsing all positive exponents to the same rate, while every
nondegenerate fiber `0 < σ < 1` is exponent-faithful and equivalent to ordinary
Goldbach.

This proposition sharpens that boundary into an equivalence.  For any fixed
nondegenerate general fiber, a pointwise specialization principle

`SigmaEvenGoldbachStatement 1 -> SigmaEvenGoldbachStatement σ`

is not a cheap consequence of the special fiber.  It has exactly ordinary
Goldbach strength.  In contrapositive form, if ordinary Goldbach fails, then no
such transfer can exist for any nondegenerate fiber.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace AffineRelaxation

open SatOrFieldAlgebra

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A pointwise special-to-general transfer principle at a chosen fiber `σ`. -/
def PointwiseSigmaGoldbachSpecializationTransfer (σ : K) : Prop :=
  SigmaEvenGoldbachStatement (1 : K) -> SigmaEvenGoldbachStatement σ

/-- THEOREM 1: on any nondegenerate general fiber, pointwise special-to-general
transfer is exactly ordinary Goldbach. -/
theorem pointwiseSpecialFiberTransfer_iff_evenGoldbach_of_mem_Ioo
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ ↔
      EvenGoldbachStatement := by
  constructor
  · intro htransfer
    have hgeneral : SigmaEvenGoldbachStatement σ :=
      htransfer specialFiber_sigmaEvenGoldbachStatement
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mp hgeneral
  · intro hgoldbach _hspecial
    exact (sigmaEvenGoldbach_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1).mpr hgoldbach

/-- THEOREM 2: if ordinary Goldbach fails, then no pointwise special-to-general
transfer exists on any nondegenerate general fiber. -/
theorem no_pointwiseSpecialFiberTransfer_of_not_evenGoldbach
    (hnot : ¬ EvenGoldbachStatement)
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ¬ PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ := by
  intro htransfer
  exact hnot
    ((pointwiseSpecialFiberTransfer_iff_evenGoldbach_of_mem_Ioo
      (K := K) hσ0 hσ1).mp htransfer)

/-- THEOREM 3: any returned special-to-general transfer at a nondegenerate
fiber can be used directly as an ordinary Goldbach proof. -/
theorem evenGoldbach_of_pointwiseSpecialFiberTransfer
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (htransfer : PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ) :
    EvenGoldbachStatement :=
  (pointwiseSpecialFiberTransfer_iff_evenGoldbach_of_mem_Ioo
    (K := K) hσ0 hσ1).mp htransfer

/-- THEOREM 4: ordinary Goldbach is sufficient to manufacture a pointwise
special-to-general transfer at every nondegenerate fiber. -/
theorem pointwiseSpecialFiberTransfer_of_evenGoldbach
    (hgoldbach : EvenGoldbachStatement)
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ :=
  (pointwiseSpecialFiberTransfer_iff_evenGoldbach_of_mem_Ioo
    (K := K) hσ0 hσ1).mpr hgoldbach

/-- THEOREM 5: the global specialization-transfer principle is at least
ordinary-Goldbach-strength as soon as one nondegenerate fiber is named. -/
theorem evenGoldbach_of_globalSpecializationTransfer_at
    {σ : K} (hσ0 : 0 < σ) (hσ1 : σ < 1)
    (T : SigmaGoldbachSpecializationTransfer K) :
    EvenGoldbachStatement :=
  evenGoldbach_of_pointwiseSpecialFiberTransfer (K := K) hσ0 hσ1
    (T hσ0 hσ1)

/-- THEOREM 6: the global special-to-general transfer principle is exactly
ordinary Goldbach.  The forward direction evaluates the global transfer at the
canonical nondegenerate fiber `σ = 1 / 2`; the reverse direction ignores the
collapsed special-fiber premise and uses the ordinary-Goldbach equivalence on
each nondegenerate fiber. -/
theorem globalSpecializationTransfer_iff_evenGoldbach :
    SigmaGoldbachSpecializationTransfer K ↔ EvenGoldbachStatement := by
  constructor
  · intro T
    have hhalf0 : (0 : K) < (1 : K) / 2 := by norm_num
    have hhalf1 : (1 : K) / 2 < 1 := by norm_num
    exact evenGoldbach_of_globalSpecializationTransfer_at
      (K := K) hhalf0 hhalf1 T
  · intro hgoldbach σ hσ0 hσ1 _hspecial
    exact evenGoldbach_gives_generalFiber_sigmaGoldbach
      (K := K) hgoldbach hσ0 hσ1

/-- THEOREM 7: if ordinary Goldbach fails, then no global special-to-general
transfer principle exists. -/
theorem no_globalSpecializationTransfer_of_not_evenGoldbach
    (hnot : ¬ EvenGoldbachStatement) :
    ¬ SigmaGoldbachSpecializationTransfer K := by
  intro T
  exact hnot ((globalSpecializationTransfer_iff_evenGoldbach (K := K)).mp T)

/-- A compact certificate for the exact cost of the special-fiber method. -/
structure P342SpecialFiberTransferStrengthCertificate : Prop where
  pointwise_transfer_iff :
    ∀ {σ : K}, 0 < σ -> σ < 1 ->
      (PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ ↔
        EvenGoldbachStatement)
  no_transfer_if_not_goldbach :
    ¬ EvenGoldbachStatement ->
      ∀ {σ : K}, 0 < σ -> σ < 1 ->
        ¬ PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ
  transfer_yields_goldbach :
    ∀ {σ : K}, 0 < σ -> σ < 1 ->
      PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ ->
        EvenGoldbachStatement
  goldbach_yields_transfer :
    EvenGoldbachStatement ->
      ∀ {σ : K}, 0 < σ -> σ < 1 ->
        PointwiseSigmaGoldbachSpecializationTransfer (K := K) σ
  global_transfer_yields_goldbach_at :
    ∀ {σ : K}, 0 < σ -> σ < 1 ->
      SigmaGoldbachSpecializationTransfer K -> EvenGoldbachStatement
  global_transfer_iff :
    SigmaGoldbachSpecializationTransfer K ↔ EvenGoldbachStatement
  no_global_transfer_if_not_goldbach :
    ¬ EvenGoldbachStatement -> ¬ SigmaGoldbachSpecializationTransfer K

/-- THEOREM 8: the canonical transfer-strength certificate. -/
theorem p342SpecialFiberTransferStrengthCertificate :
    P342SpecialFiberTransferStrengthCertificate (K := K) where
  pointwise_transfer_iff := by
    intro σ hσ0 hσ1
    exact pointwiseSpecialFiberTransfer_iff_evenGoldbach_of_mem_Ioo
      (K := K) hσ0 hσ1
  no_transfer_if_not_goldbach := by
    intro hnot σ hσ0 hσ1
    exact no_pointwiseSpecialFiberTransfer_of_not_evenGoldbach
      (K := K) hnot hσ0 hσ1
  transfer_yields_goldbach := by
    intro σ hσ0 hσ1 htransfer
    exact evenGoldbach_of_pointwiseSpecialFiberTransfer
      (K := K) hσ0 hσ1 htransfer
  goldbach_yields_transfer := by
    intro hgoldbach σ hσ0 hσ1
    exact pointwiseSpecialFiberTransfer_of_evenGoldbach
      (K := K) hgoldbach hσ0 hσ1
  global_transfer_yields_goldbach_at := by
    intro σ hσ0 hσ1 T
    exact evenGoldbach_of_globalSpecializationTransfer_at
      (K := K) hσ0 hσ1 T
  global_transfer_iff := globalSpecializationTransfer_iff_evenGoldbach (K := K)
  no_global_transfer_if_not_goldbach := by
    intro hnot
    exact no_globalSpecializationTransfer_of_not_evenGoldbach (K := K) hnot

end AffineRelaxation
end SaturationMonoid
