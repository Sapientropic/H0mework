import H0mework.Arithmetic.PrimeShadow.P545

/-!
# Proposition 546: spectral exponent codes are support-indexed producers

P545 proved that the coded descent quotient has no extra mathematical content:
it is canonically the exponent spine `ℕ`.  The remaining danger is subtler:
the field

`SpectralExponentCodeAdapter.code : H1SpectralProjection (1 / 2 : ℝ) -> ℕ`

looks total, while the intended Euler/physics data will usually certify only a
spectral support, not every possible H¹ point.

This file makes that boundary explicit.  A support-indexed spectral producer
codes only supported spectral points.  It yields a total P543/P544 adapter
exactly when the support is all of the spectral space.  Thus future work can
bring a genuine Euler/physics support certificate without pretending that an
arbitrary unsupported H¹ point already has a mathematical exponent.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Support-indexed spectral exponent producer -/

/-- A spectral exponent producer with an explicit support predicate.  The code
is available only for supported H¹ spectral projections. -/
structure SupportedSpectralExponentCodeProducer where
  support : H1SpectralProjection (1 / 2 : ℝ) -> Prop
  code :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      support s -> ℕ
  spectral_complete_iff :
    ∀ (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : support s),
      HasPrimeAdditiveDecomposition (code s hs) ↔
        H1SpectralNoObstructionComplete s

/-- The supported spectral domain of a support-indexed producer. -/
def SupportedSpectralPoint
    (B : SupportedSpectralExponentCodeProducer) : Type :=
  { s : H1SpectralProjection (1 / 2 : ℝ) // B.support s }

namespace SupportedSpectralPoint

/-- The canonical exponent code on a supported spectral point. -/
def code (B : SupportedSpectralExponentCodeProducer)
    (s : SupportedSpectralPoint B) : ℕ :=
  B.code s.1 s.2

/-- THEOREM 1: supported spectral completeness is exactly additive-prime
decomposition of the supported code. -/
theorem complete_iff
    (B : SupportedSpectralExponentCodeProducer)
    (s : SupportedSpectralPoint B) :
    HasPrimeAdditiveDecomposition (code B s) ↔
      H1SpectralNoObstructionComplete s.1 :=
  B.spectral_complete_iff s.1 s.2

end SupportedSpectralPoint

/-! ## The support-indexed exponent pullback carrier -/

/-- Pullback carrier over the direct exponent spine, restricted to supported
spectral points. -/
def SupportedExponentCarrier
    (B : SupportedSpectralExponentCodeProducer) : Type :=
  { z : HalfSigmaArithmeticImage × SupportedSpectralPoint B //
      SigmaExponentImage.exponent z.1 =
        SupportedSpectralPoint.code B z.2 }

namespace SupportedExponentCarrier

/-- Arithmetic projection of the support-indexed pullback. -/
def arithmetic {B : SupportedSpectralExponentCodeProducer}
    (z : SupportedExponentCarrier B) : HalfSigmaArithmeticImage :=
  z.1.1

/-- Supported spectral projection of the support-indexed pullback. -/
def spectral {B : SupportedSpectralExponentCodeProducer}
    (z : SupportedExponentCarrier B) : SupportedSpectralPoint B :=
  z.1.2

/-- THEOREM 2: membership in the supported exponent pullback is exactly
equality of the arithmetic exponent and the supported spectral code. -/
theorem mk_shadow_agreement_iff
    (B : SupportedSpectralExponentCodeProducer)
    (a : HalfSigmaArithmeticImage)
    (s : SupportedSpectralPoint B) :
    (∃ z : SupportedExponentCarrier B,
      arithmetic z = a ∧ spectral z = s) ↔
      SigmaExponentImage.exponent a =
        SupportedSpectralPoint.code B s := by
  constructor
  · rintro ⟨z, ha, hs⟩
    calc
      SigmaExponentImage.exponent a =
          SigmaExponentImage.exponent (arithmetic z) := by rw [ha]
      _ = SupportedSpectralPoint.code B (spectral z) := z.2
      _ = SupportedSpectralPoint.code B s := by rw [hs]
  · intro h
    exact ⟨⟨(a, s), h⟩, rfl, rfl⟩

end SupportedExponentCarrier

/-! ## Support-aware admissible states -/

/-- A seven-facet state is supported and code-compatible when its spectral
point is in the producer support and its arithmetic exponent matches that
supported code. -/
def SupportedCodedDescentAllowed
    (B : SupportedSpectralExponentCodeProducer)
    (x : ArithmeticAdmissibleSevenFacet) : Prop :=
  ∃ hs : B.support x.spectral,
    SigmaExponentImage.exponent x.arithmetic =
      B.code x.spectral hs

/-- THEOREM 3: support-aware code compatibility is exactly pointwise lift into
the support-indexed exponent pullback. -/
theorem supportedCodedDescentAllowed_iff_liftable
    (B : SupportedSpectralExponentCodeProducer)
    (x : ArithmeticAdmissibleSevenFacet) :
    SupportedCodedDescentAllowed B x ↔
      ∃ hs : B.support x.spectral,
        ∃ z : SupportedExponentCarrier B,
          SupportedExponentCarrier.arithmetic z = x.arithmetic ∧
            SupportedExponentCarrier.spectral z = ⟨x.spectral, hs⟩ := by
  constructor
  · rintro ⟨hs, hcode⟩
    exact
      ⟨hs,
        ⟨⟨(x.arithmetic, ⟨x.spectral, hs⟩), hcode⟩, rfl, rfl⟩⟩
  · rintro ⟨hs, z, ha, hspectral⟩
    refine ⟨hs, ?_⟩
    have hmem :
        SigmaExponentImage.exponent (SupportedExponentCarrier.arithmetic z) =
          SupportedSpectralPoint.code B (SupportedExponentCarrier.spectral z) :=
      z.2
    calc
      SigmaExponentImage.exponent x.arithmetic =
          SigmaExponentImage.exponent
            (SupportedExponentCarrier.arithmetic z) := by rw [ha]
      _ = SupportedSpectralPoint.code B
            (SupportedExponentCarrier.spectral z) := hmem
      _ = SupportedSpectralPoint.code B ⟨x.spectral, hs⟩ := by rw [hspectral]
      _ = B.code x.spectral hs := rfl

/-- The supported admissible domain. -/
def SupportedCodedAdmissibleDomain
    (B : SupportedSpectralExponentCodeProducer) : Type :=
  { x : ArithmeticAdmissibleSevenFacet // SupportedCodedDescentAllowed B x }

/-! ## Total support recovers the P543/P544 adapter -/

namespace SupportedSpectralExponentCodeProducer

/-- A support-indexed producer becomes a total P543/P544 adapter exactly when
its support covers every H¹ spectral point. -/
def toTotalAdapter
    (B : SupportedSpectralExponentCodeProducer)
    (htotal : ∀ s : H1SpectralProjection (1 / 2 : ℝ), B.support s) :
    SpectralExponentCodeAdapter where
  code := fun s => B.code s (htotal s)
  spectral_complete_iff := by
    intro s
    exact B.spectral_complete_iff s (htotal s)

/-- THEOREM 4: totalization does not change the code on any supported point;
it only chooses the unique proof-irrelevant support witness. -/
theorem toTotalAdapter_code_eq_supported
    (B : SupportedSpectralExponentCodeProducer)
    (htotal : ∀ s : H1SpectralProjection (1 / 2 : ℝ), B.support s)
    (s : H1SpectralProjection (1 / 2 : ℝ)) (hs : B.support s) :
    (B.toTotalAdapter htotal).code s = B.code s hs := by
  simp [toTotalAdapter]

/-- THEOREM 5: on a total support, the old `CodedDescentAllowed` predicate is
exactly the support-aware compatibility predicate. -/
theorem toTotalAdapter_allowed_iff_supported
    (B : SupportedSpectralExponentCodeProducer)
    (htotal : ∀ s : H1SpectralProjection (1 / 2 : ℝ), B.support s)
    (x : ArithmeticAdmissibleSevenFacet) :
    CodedDescentAllowed (B.toTotalAdapter htotal) x ↔
      SupportedCodedDescentAllowed B x := by
  constructor
  · intro h
    exact ⟨htotal x.spectral, h⟩
  · rintro ⟨hs, h⟩
    calc
      SigmaExponentImage.exponent x.arithmetic =
          B.code x.spectral hs := h
      _ = (B.toTotalAdapter htotal).code x.spectral :=
        (B.toTotalAdapter_code_eq_supported htotal x.spectral hs).symm

end SupportedSpectralExponentCodeProducer

/-! ## Packaged support-indexed front door -/

/-- Compact certificate for the support-indexed spectral-code front door.

This is the honest replacement for a bare total `code` field: unsupported
spectral points are not silently assigned an exponent; if a future producer
proves total support, it recovers the P543/P544 adapter exactly. -/
structure SupportedSpectralExponentFrontDoorCertificate where
  supportedCode :
    ∀ B : SupportedSpectralExponentCodeProducer,
      SupportedSpectralPoint B -> ℕ
  supported_complete_iff :
    ∀ (B : SupportedSpectralExponentCodeProducer)
      (s : SupportedSpectralPoint B),
      HasPrimeAdditiveDecomposition (supportedCode B s) ↔
        H1SpectralNoObstructionComplete s.1
  supportedCarrier :
    SupportedSpectralExponentCodeProducer -> Type
  liftable_iff_supported_allowed :
    ∀ (B : SupportedSpectralExponentCodeProducer)
      (x : ArithmeticAdmissibleSevenFacet),
      SupportedCodedDescentAllowed B x ↔
        ∃ hs : B.support x.spectral,
          ∃ z : SupportedExponentCarrier B,
            SupportedExponentCarrier.arithmetic z = x.arithmetic ∧
              SupportedExponentCarrier.spectral z = ⟨x.spectral, hs⟩
  total_adapter :
    ∀ (B : SupportedSpectralExponentCodeProducer),
      (∀ s : H1SpectralProjection (1 / 2 : ℝ), B.support s) ->
        SpectralExponentCodeAdapter
  total_allowed_iff_supported :
    ∀ (B : SupportedSpectralExponentCodeProducer)
      (htotal : ∀ s : H1SpectralProjection (1 / 2 : ℝ), B.support s)
      (x : ArithmeticAdmissibleSevenFacet),
      CodedDescentAllowed (B.toTotalAdapter htotal) x ↔
        SupportedCodedDescentAllowed B x

/-- THEOREM 6: the support-indexed spectral exponent front-door certificate.
-/
def supportedSpectralExponentFrontDoorCertificate :
    SupportedSpectralExponentFrontDoorCertificate where
  supportedCode := SupportedSpectralPoint.code
  supported_complete_iff := SupportedSpectralPoint.complete_iff
  supportedCarrier := SupportedExponentCarrier
  liftable_iff_supported_allowed :=
    supportedCodedDescentAllowed_iff_liftable
  total_adapter := SupportedSpectralExponentCodeProducer.toTotalAdapter
  total_allowed_iff_supported :=
    SupportedSpectralExponentCodeProducer.toTotalAdapter_allowed_iff_supported

end AffineRelaxation
end SaturationMonoid
