import H0mework.Arithmetic.PrimeShadow.P675

/-!
# Proposition 676: even support-code source object

P675 proves the canonical normal form

`coded-descent pullback producer ↔ adapter even-code range ∧ Goldbach`.

This file turns the range side into an explicit source object.  An
`EvenSupportCodeSource` is the part of the final Euler/RH producer that is
allowed to be constructed without proving Goldbach: it supplies a
support-indexed prime-shadow producer, arithmetic-shadow injectivity, and
support-code coverage of every ordinary even exponent.

Once such a source is present, the actual Euler-pullback representative
producer is equivalent to ordinary even Goldbach with no extra ambient
hypotheses.  For canonical coded descent, an adapter even-code range proof
constructs this source directly.

Boundary: this does not prove the adapter even-code range source.  It isolates
that source as a concrete object and removes it from the final representative
producer theorem's ambient assumptions.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Even support-code source -/

/-- The range/injectivity part of the final Euler/RH mathematical producer.

This is the part that can be supplied before the actual Goldbach/H¹
no-obstruction content. -/
structure EvenSupportCodeSource where
  B : SupportIndexedPrimeShadowProducer
  arithmeticShadow_injective :
    Function.Injective B.producer.arithmeticShadow
  even_support_code_surjective :
    PrimeShadowEvenSupportCodeSurjective B

/-- The actual pullback representative producer associated with a source. -/
abbrev EvenSupportCodeSource.PullbackProducer
    (S : EvenSupportCodeSource) : Type :=
  EvenEulerPullbackRepresentativeProducer S.B

/-- THEOREM 1: once the even support-code source is supplied, the actual
Euler-pullback representative producer is equivalent to ordinary even
Goldbach, with no remaining range or injectivity assumptions in the theorem
statement. -/
theorem evenSupportCodeSource_pullbackProducer_iff_goldbach
    (S : EvenSupportCodeSource) :
    Nonempty S.PullbackProducer ↔ EvenGoldbachStatement := by
  have hnormal :
      Nonempty (EvenEulerPullbackRepresentativeProducer S.B) ↔
        PrimeShadowEvenSupportCodeSurjective S.B ∧ EvenGoldbachStatement :=
    eulerPullbackRepresentativeProducer_iff_supportCodeSurjective_and_goldbach_of_injective
      S.B S.arithmeticShadow_injective
  constructor
  · intro hP
    exact (hnormal.mp hP).2
  · intro hgold
    exact hnormal.mpr ⟨S.even_support_code_surjective, hgold⟩

/-! ## Canonical coded-descent source from adapter range -/

/-- A spectral exponent adapter whose range covers every ordinary even
exponent induces an `EvenSupportCodeSource` through canonical coded descent.
-/
def codedDescentEvenSupportCodeSource
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    EvenSupportCodeSource where
  B := codedDescentSupportIndexedPrimeShadowProducer A
  arithmeticShadow_injective :=
    codedDescentSupportIndexedPrimeShadowProducer_arithmeticShadow_injective A
  even_support_code_surjective :=
    (codedDescentEvenSupportCodeSurjective_iff_adapterEvenCodeSurjective A).mpr
      hrange

/-- THEOREM 2: for a coded-descent adapter range source, the source-level
pullback representative producer is exactly ordinary even Goldbach. -/
theorem codedDescentEvenSupportCodeSource_pullbackProducer_iff_goldbach
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    Nonempty (codedDescentEvenSupportCodeSource A hrange).PullbackProducer ↔
      EvenGoldbachStatement :=
  evenSupportCodeSource_pullbackProducer_iff_goldbach
    (codedDescentEvenSupportCodeSource A hrange)

/-- THEOREM 3: the source-level theorem agrees with P675's canonical
coded-descent normal form under the same adapter range proof. -/
theorem codedDescentEvenSupportCodeSource_pullbackProducer_iff_codedDescentProducer
    (A : SpectralExponentCodeAdapter)
    (hrange : SpectralExponentEvenCodeSurjective A) :
    Nonempty (codedDescentEvenSupportCodeSource A hrange).PullbackProducer ↔
      Nonempty (CodedDescentEulerPullbackRepresentativeProducer A) := by
  rfl

/-! ## Packaged source certificate -/

/-- P676 packages the even support-code source object and its canonical
coded-descent construction from adapter range. -/
structure EvenSupportCodeSourceCertificate where
  p675_normal_form :
    CodedDescentEulerPullbackNormalFormCertificate
  source_producer_iff_goldbach :
    ∀ S : EvenSupportCodeSource,
      Nonempty S.PullbackProducer ↔ EvenGoldbachStatement
  coded_descent_source :
    ∀ A : SpectralExponentCodeAdapter,
      SpectralExponentEvenCodeSurjective A -> EvenSupportCodeSource
  coded_descent_source_producer_iff_goldbach :
    ∀ (A : SpectralExponentCodeAdapter)
      (hrange : SpectralExponentEvenCodeSurjective A),
      Nonempty (coded_descent_source A hrange).PullbackProducer ↔
        EvenGoldbachStatement

/-- DEFINITION 1: canonical P676 even support-code source certificate. -/
def evenSupportCodeSourceCertificate :
    EvenSupportCodeSourceCertificate where
  p675_normal_form :=
    codedDescentEulerPullbackNormalFormCertificate
  source_producer_iff_goldbach :=
    evenSupportCodeSource_pullbackProducer_iff_goldbach
  coded_descent_source :=
    codedDescentEvenSupportCodeSource
  coded_descent_source_producer_iff_goldbach :=
    codedDescentEvenSupportCodeSource_pullbackProducer_iff_goldbach

end AffineRelaxation

namespace GrandUnification

open AffineRelaxation

universe u

/-- The current unified root with P676's explicit even support-code source
object welded below P675's coded-descent normal form. -/
structure EvenSupportCodeSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  p675_root :
    CodedDescentEulerPullbackNormalFormUnifiedRootCertificate E
  even_support_code_source :
    EvenSupportCodeSourceCertificate
  source_producer_iff_goldbach :
    ∀ S : EvenSupportCodeSource,
      Nonempty S.PullbackProducer ↔ EvenGoldbachStatement
  alpha_s_residual :
    StandardModelConstraint.inverseCorrectionFromAlphaGap
        (StandardModelConstraint.alphaStrongTwoLoopSMOutput ℚ)
        (StandardModelConstraint.alphaStrongPhysicalFiniteGeometryProducer
          StandardModelConstraint.currentFormalFourDPoincareCertificate
          StandardModelConstraint.unifiedGaugeIntoAlphaEMStructural).producedGap =
      -((89000 : ℚ) / 128511)

/-- THEOREM 4: the current central root with P676's explicit support-code
source object. -/
def evenSupportCodeSourceUnifiedRootCertificate
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] :
    EvenSupportCodeSourceUnifiedRootCertificate E where
  p675_root := codedDescentEulerPullbackNormalFormUnifiedRootCertificate (E := E)
  even_support_code_source :=
    evenSupportCodeSourceCertificate
  source_producer_iff_goldbach :=
    evenSupportCodeSource_pullbackProducer_iff_goldbach
  alpha_s_residual :=
    (codedDescentEulerPullbackNormalFormUnifiedRootCertificate (E := E)).alpha_s_residual

end GrandUnification
end SaturationMonoid
