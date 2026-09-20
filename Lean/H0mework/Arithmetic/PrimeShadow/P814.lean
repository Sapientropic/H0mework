import H0mework.Arithmetic.PrimeShadow.P813

/-!
# Proposition 814: Goldbach native/carrier bidirectional reconstruction

P813 identifies the sharper sigma-carrier producer:

`SigmaAtomicSatOrCoversEvenCarrier σ`.

This file turns that iff into the active goal's bidirectional shape.  The
color-loop native object and the sigma-atomic residual-carrier object are
presented as two surfaces.  Lean proves that, on any real nondegenerate
sigma-fiber, each surface reconstructs the other uniquely.

No Goldbach witness is manufactured here.  The theorem is stronger in the
right direction: any native color-loop zero-energy producer is exactly the same
object as a sigma-atomic binary `satOr` cover, and conversely.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

open StandardModelConstraint

/-! ## The two surfaces -/

/-- Native color-loop Goldbach surface: a unit-indexed witness of the P812
zero-energy color-loop producer.  The `Unit` carrier lets us state surface
equivalence without assuming the producer is inhabited. -/
abbrev GoldbachColorLoopZeroEnergyNativeSurface : Type :=
  { _u : Unit // ColorLoopZeroEnergyPrimePairProducer }

/-- Sigma-atomic residual-carrier surface: a unit-indexed witness that the
binary `satOr` image of the sigma-atomic support covers all even carrier
points. -/
abbrev SigmaAtomicGoldbachResidualCarrierSurface
    (σ : ℝ) (hσ : σ ≠ 1) : Type :=
  { _u : Unit // SigmaAtomicSatOrCoversEvenCarrier σ hσ }

/-! ## Surface truth conditions -/

/-- THEOREM 1: the native color-loop surface is inhabited exactly when the
zero-energy color-loop producer exists. -/
theorem colorLoopNativeSurface_nonempty_iff :
    Nonempty GoldbachColorLoopZeroEnergyNativeSurface ↔
      ColorLoopZeroEnergyPrimePairProducer := by
  constructor
  · rintro ⟨x⟩
    exact x.2
  · intro h
    exact ⟨⟨(), h⟩⟩

/-- THEOREM 2: the sigma-atomic carrier surface is inhabited exactly when the
binary atomic cover exists. -/
theorem sigmaAtomicCarrierSurface_nonempty_iff
    {σ : ℝ} {hσ : σ ≠ 1} :
    Nonempty (SigmaAtomicGoldbachResidualCarrierSurface σ hσ) ↔
      SigmaAtomicSatOrCoversEvenCarrier σ hσ := by
  constructor
  · rintro ⟨x⟩
    exact x.2
  · intro h
    exact ⟨⟨(), h⟩⟩

/-- THEOREM 3: native color-loop surface inhabitation is exactly ordinary
Goldbach. -/
theorem colorLoopNativeSurface_nonempty_iff_goldbach :
    Nonempty GoldbachColorLoopZeroEnergyNativeSurface ↔
      EvenGoldbachStatement := by
  rw [colorLoopNativeSurface_nonempty_iff,
    colorLoopZeroEnergyProducer_iff_evenGoldbach]

/-- THEOREM 4: sigma-atomic carrier surface inhabitation is exactly ordinary
Goldbach on the active real sigma-fiber. -/
theorem sigmaAtomicCarrierSurface_nonempty_iff_goldbach
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Nonempty (SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1)) ↔
      EvenGoldbachStatement := by
  rw [sigmaAtomicCarrierSurface_nonempty_iff,
    atomicSatOrCover_iff_evenGoldbach_of_mem_Ioo hσ0 hσ1]

/-! ## Bidirectional reconstruction -/

/-- THEOREM 5: a native color-loop zero-energy producer reconstructs the
sigma-atomic residual-carrier cover. -/
def colorLoopNativeToSigmaAtomicCarrier
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    GoldbachColorLoopZeroEnergyNativeSurface ->
      SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1) :=
  fun x =>
    ⟨(), (realAtomicSatOrCover_iff_colorLoopZeroEnergyProducer
      hσ0 hσ1).mpr x.2⟩

/-- THEOREM 6: a sigma-atomic residual-carrier cover reconstructs the native
color-loop zero-energy producer. -/
def sigmaAtomicCarrierToColorLoopNative
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1) ->
      GoldbachColorLoopZeroEnergyNativeSurface :=
  fun x =>
    ⟨(), (realAtomicSatOrCover_iff_colorLoopZeroEnergyProducer
      hσ0 hσ1).mp x.2⟩

/-- THEOREM 7: the color-loop native surface and the sigma-atomic residual
carrier surface are equivalent. -/
def colorLoopNativeSigmaAtomicCarrierEquiv
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    GoldbachColorLoopZeroEnergyNativeSurface ≃
      SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1) where
  toFun :=
    colorLoopNativeToSigmaAtomicCarrier hσ0 hσ1
  invFun :=
    sigmaAtomicCarrierToColorLoopNative hσ0 hσ1
  left_inv := by
    intro x
    apply Subtype.ext
    cases x.1
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    cases x.1
    rfl

/-- THEOREM 8: the two surfaces are inhabited together. -/
theorem colorLoopNative_nonempty_iff_sigmaAtomicCarrier_nonempty
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Nonempty GoldbachColorLoopZeroEnergyNativeSurface ↔
      Nonempty (SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1)) := by
  constructor
  · rintro ⟨x⟩
    exact ⟨colorLoopNativeToSigmaAtomicCarrier hσ0 hσ1 x⟩
  · rintro ⟨x⟩
    exact ⟨sigmaAtomicCarrierToColorLoopNative hσ0 hσ1 x⟩

/-! ## Certificate packaging -/

/-- P814 certificate: the Goldbach color-loop native surface and the
sigma-atomic residual carrier surface are the same object up to canonical
reconstruction. -/
structure GoldbachColorLoopSigmaAtomicBidirectionalCertificate
    (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ < 1) : Prop where
  native_nonempty_iff_goldbach :
    Nonempty GoldbachColorLoopZeroEnergyNativeSurface ↔
      EvenGoldbachStatement
  carrier_nonempty_iff_goldbach :
    Nonempty (SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1)) ↔
      EvenGoldbachStatement
  native_carrier_equiv :
    Nonempty
      (GoldbachColorLoopZeroEnergyNativeSurface ≃
        SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1))
  native_nonempty_iff_carrier_nonempty :
    Nonempty GoldbachColorLoopZeroEnergyNativeSurface ↔
      Nonempty (SigmaAtomicGoldbachResidualCarrierSurface σ (ne_of_lt hσ1))
  pointwise_cover_iff_zero_energy :
    SigmaAtomicSatOrCoversEvenCarrier σ (ne_of_lt hσ1) ↔
      ColorLoopZeroEnergyPrimePairProducer

/-- THEOREM 9: canonical bidirectional reconstruction certificate. -/
theorem goldbachColorLoopSigmaAtomicBidirectionalCertificate
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    GoldbachColorLoopSigmaAtomicBidirectionalCertificate σ hσ0 hσ1 where
  native_nonempty_iff_goldbach :=
    colorLoopNativeSurface_nonempty_iff_goldbach
  carrier_nonempty_iff_goldbach :=
    sigmaAtomicCarrierSurface_nonempty_iff_goldbach hσ0 hσ1
  native_carrier_equiv :=
    ⟨colorLoopNativeSigmaAtomicCarrierEquiv hσ0 hσ1⟩
  native_nonempty_iff_carrier_nonempty :=
    colorLoopNative_nonempty_iff_sigmaAtomicCarrier_nonempty hσ0 hσ1
  pointwise_cover_iff_zero_energy :=
    realAtomicSatOrCover_iff_colorLoopZeroEnergyProducer hσ0 hσ1

end AffineRelaxation
end SaturationMonoid
