import H0mework.Realization.Descent.P542

/-!
# Proposition 543: coded descent preserves the prime-indexed spine

P542 proved that the free descent quotient is too coarse: if every
arithmetic-admissible state may glue freely, distinct prime arithmetic codes
can be identified through the same H¹ spectral point.

This file builds the next front door.  The spectral side must carry an
exponent code, and gluing is allowed only through the same code.  The resulting
descent quotient has a canonical projection back to `ℕ`, so prime-indexed
support is preserved by construction.

Boundary: this still does not prove Goldbach/RH.  It proves the correct shape
of the next producer: a coded/restricted descent, not the free quotient from
P540.
-/

noncomputable section

namespace SaturationMonoid
namespace AffineRelaxation

/-! ## Coded descent atoms and quotient -/

/-- A spectral-code adapter reads the arithmetic exponent that a spectral
point is allowed to represent.  The second field is the concrete H¹/Goldbach
predicate compatibility required to build a full bridge once a domain has
been restricted to code-compatible states. -/
structure SpectralExponentCodeAdapter where
  code : H1SpectralProjection (1 / 2 : ℝ) -> ℕ
  spectral_complete_iff :
    ∀ s : H1SpectralProjection (1 / 2 : ℝ),
      HasPrimeAdditiveDecomposition (code s) ↔
        H1SpectralNoObstructionComplete s

/-- The raw atoms for coded descent.  Arithmetic atoms carry only the natural
iteration exponent; spectral atoms are tagged by the same exponent. -/
abbrev CodedDescentShadowAtom : Type :=
  Sum ℕ (Sigma fun _n : ℕ => H1SpectralProjection (1 / 2 : ℝ))

/-- Coded gluing only identifies an arithmetic exponent with spectral points
tagged by that same exponent. -/
inductive CodedDescentShadowRel :
    CodedDescentShadowAtom -> CodedDescentShadowAtom -> Prop
  | glue (n : ℕ) (s : H1SpectralProjection (1 / 2 : ℝ)) :
      CodedDescentShadowRel
        (Sum.inl n)
        (Sum.inr ⟨n, s⟩)

/-- The coded descent prime shadow. -/
abbrev CodedDescentPrimeShadow : Type :=
  Quot CodedDescentShadowRel

/-- Arithmetic image points enter the coded shadow through their iteration
exponent. -/
def codedDescentArithmeticShadow (r : HalfSigmaArithmeticImage) :
    CodedDescentPrimeShadow :=
  Quot.mk CodedDescentShadowRel
    (Sum.inl (SigmaExponentImage.exponent r))

/-- Spectral points enter the coded shadow through the adapter's exponent
code. -/
def codedDescentSpectralShadow
    (A : SpectralExponentCodeAdapter)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    CodedDescentPrimeShadow :=
  Quot.mk CodedDescentShadowRel
    (Sum.inr ⟨A.code s, s⟩)

/-- Code-compatible admissible states are exactly the states whose arithmetic
exponent agrees with the exponent read from their spectral projection. -/
def CodedDescentAllowed
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet) : Prop :=
  SigmaExponentImage.exponent x.arithmetic = A.code x.spectral

/-- THEOREM 1: coded descent supplies shadow equality on the code-compatible
domain. -/
theorem codedDescent_shadow_eq_of_allowed
    (A : SpectralExponentCodeAdapter)
    (x : ArithmeticAdmissibleSevenFacet)
    (hallowed : CodedDescentAllowed A x) :
    codedDescentArithmeticShadow x.arithmetic =
      codedDescentSpectralShadow A x.spectral := by
  unfold codedDescentArithmeticShadow codedDescentSpectralShadow
  rw [← hallowed]
  exact
    Quot.sound
      (CodedDescentShadowRel.glue
        (SigmaExponentImage.exponent x.arithmetic) x.spectral)

/-! ## The quotient remembers the exponent -/

/-- Read the preserved exponent from a raw coded atom. -/
def codedDescentAtomExponent : CodedDescentShadowAtom -> ℕ
  | Sum.inl n => n
  | Sum.inr tagged => tagged.1

/-- THEOREM 2: coded gluing preserves the exponent label. -/
theorem codedDescentRel_preserves_exponent
    {a b : CodedDescentShadowAtom}
    (h : CodedDescentShadowRel a b) :
    codedDescentAtomExponent a = codedDescentAtomExponent b := by
  cases h
  rfl

/-- The coded descent quotient has a canonical exponent projection. -/
def codedDescentShadowExponent :
    CodedDescentPrimeShadow -> ℕ :=
  Quot.lift codedDescentAtomExponent (by
    intro a b h
    exact codedDescentRel_preserves_exponent h)

/-- THEOREM 3: arithmetic shadows project back to their chosen exponent. -/
theorem codedDescentShadowExponent_arithmetic
    (r : HalfSigmaArithmeticImage) :
    codedDescentShadowExponent (codedDescentArithmeticShadow r) =
      SigmaExponentImage.exponent r :=
  rfl

/-- THEOREM 4: spectral shadows project back to the adapter's exponent code.
-/
theorem codedDescentShadowExponent_spectral
    (A : SpectralExponentCodeAdapter)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    codedDescentShadowExponent (codedDescentSpectralShadow A s) =
      A.code s :=
  rfl

/-! ## Producer and bridge data -/

/-- The coded descent producer.  Unlike the free descent quotient, the spectral
map is not anonymous: it is routed through the adapter's exponent code. -/
def codedDescentEulerPrimeCouplingProducer
    (A : SpectralExponentCodeAdapter) :
    EulerPrimeCouplingProducers where
  PrimeShadow := CodedDescentPrimeShadow
  arithmeticShadow := codedDescentArithmeticShadow
  spectralShadow := codedDescentSpectralShadow A
  seed := eulerProductCouplingSeedCertificate

/-- Completeness on the coded shadow is ordinary additive prime decomposition
of the preserved exponent. -/
def codedDescentCommonComplete :
    CodedDescentPrimeShadow -> Prop :=
  fun z => HasPrimeAdditiveDecomposition (codedDescentShadowExponent z)

/-- THEOREM 5: the coded common predicate pulls back to half-sigma Goldbach on
the arithmetic side. -/
theorem codedDescentCommonComplete_arithmetic
    (r : HalfSigmaArithmeticImage) :
    codedDescentCommonComplete (codedDescentArithmeticShadow r) ↔
      HalfSigmaImageGoldbachComplete r := by
  rw [codedDescentCommonComplete, codedDescentShadowExponent_arithmetic]
  exact (halfSigmaImageGoldbachComplete_iff_exponentGoldbach r).symm

/-- THEOREM 6: the coded common predicate pulls back to H¹ no-obstruction on
the spectral side when the adapter supplies the concrete compatibility. -/
theorem codedDescentCommonComplete_spectral
    (A : SpectralExponentCodeAdapter)
    (s : H1SpectralProjection (1 / 2 : ℝ)) :
    codedDescentCommonComplete (codedDescentSpectralShadow A s) ↔
      H1SpectralNoObstructionComplete s := by
  rw [codedDescentCommonComplete, codedDescentShadowExponent_spectral]
  exact A.spectral_complete_iff s

/-- The restricted admissible domain for a coded adapter. -/
def CodedAdmissibleDomain (A : SpectralExponentCodeAdapter) : Type :=
  { x : ArithmeticAdmissibleSevenFacet // CodedDescentAllowed A x }

/-- The coded restricted lift into the pullback carrier. -/
def codedDescentRestrictedLift
    (A : SpectralExponentCodeAdapter) :
    CodedAdmissibleDomain A ->
      (codedDescentEulerPrimeCouplingProducer A).Carrier :=
  fun x =>
    ⟨(x.1.arithmetic, x.1.spectral),
      codedDescent_shadow_eq_of_allowed A x.1 x.2⟩

/-- THEOREM 7: the restricted lift preserves the arithmetic projection. -/
theorem codedDescentRestrictedLift_arithmetic
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    EulerPrimeCouplingProducers.Carrier.arithmetic
        (codedDescentRestrictedLift A x) =
      x.1.arithmetic :=
  rfl

/-- THEOREM 8: the restricted lift preserves the spectral projection. -/
theorem codedDescentRestrictedLift_spectral
    (A : SpectralExponentCodeAdapter)
    (x : CodedAdmissibleDomain A) :
    EulerPrimeCouplingProducers.Carrier.spectral
        (codedDescentRestrictedLift A x) =
      x.1.spectral :=
  rfl

/-! ## Prime-indexed support is preserved -/

/-- The coded prime code uses the arithmetic face of the coded producer. -/
def codedDescentPrimeCode
    (_A : SpectralExponentCodeAdapter) :
    PrimeExponent -> CodedDescentPrimeShadow :=
  fun p => codedDescentArithmeticShadow (halfSigmaPrimeImage p)

/-- THEOREM 9: the exponent of a named half-sigma prime image is the prime
itself. -/
theorem halfSigmaPrimeImage_exponent
    (p : PrimeExponent) :
    SigmaExponentImage.exponent (halfSigmaPrimeImage p) = p.1 := by
  exact
    SigmaExponentImage.exponent_ofNat_of_mem_Ioo
      halfSigma_mem_Ioo.1 halfSigma_mem_Ioo.2 p.1

/-- THEOREM 10: coded descent keeps prime-indexed support injective. -/
theorem codedDescentPrimeCode_injective
    (A : SpectralExponentCodeAdapter) :
    Function.Injective (codedDescentPrimeCode A) := by
  intro p q h
  have hnat :
      SigmaExponentImage.exponent (halfSigmaPrimeImage p) =
        SigmaExponentImage.exponent (halfSigmaPrimeImage q) := by
    have h' := congrArg codedDescentShadowExponent h
    dsimp [codedDescentPrimeCode] at h'
    rw [codedDescentShadowExponent_arithmetic,
      codedDescentShadowExponent_arithmetic] at h'
    exact h'
  apply Subtype.ext
  simpa [halfSigmaPrimeImage_exponent] using hnat

/-- THEOREM 11: every coded adapter gives a prime-indexed shadow structure. -/
def codedDescentPrimeIndexedShadowStructure
    (A : SpectralExponentCodeAdapter) :
    PrimeIndexedShadowStructure
      (codedDescentEulerPrimeCouplingProducer A) where
  primeCode := codedDescentPrimeCode A
  primeCode_injective := codedDescentPrimeCode_injective A

/-! ## Full-domain adapters are impossible on the current admissible domain -/

/-- A full-domain adapter would make every arithmetic-admissible state
code-compatible.  P542's collapse witness shows that this is too strong for
the current unrestricted domain. -/
structure FullDomainSpectralExponentCodeAdapter extends
    SpectralExponentCodeAdapter where
  global_code_eq :
    ∀ x : ArithmeticAdmissibleSevenFacet,
      CodedDescentAllowed toSpectralExponentCodeAdapter x

/-- The admissible state pairing a prime image with the zero spectral point. -/
def zeroSpectralPrimeState
    (p : PrimeExponent) :
    ArithmeticAdmissibleSevenFacet :=
  ArithmeticAdmissibleSevenFacet.ofArithmetic
    (fun _ => True)
    zeroDescentSpectralPoint.phase
    zeroDescentSpectralPoint.analytic
    (halfSigmaPrimeImage p)

/-- THEOREM 12: `zeroSpectralPrimeState` has the requested arithmetic image. -/
theorem zeroSpectralPrimeState_arithmetic
    (p : PrimeExponent) :
    (zeroSpectralPrimeState p).arithmetic = halfSigmaPrimeImage p :=
  ofArithmetic_arithmetic_eq
    (halfSigmaPrimeImage p)
    (fun _ => True)
    zeroDescentSpectralPoint.phase
    zeroDescentSpectralPoint.analytic

/-- THEOREM 13: `zeroSpectralPrimeState` has the fixed zero spectral point. -/
theorem zeroSpectralPrimeState_spectral
    (p : PrimeExponent) :
    (zeroSpectralPrimeState p).spectral = zeroDescentSpectralPoint := by
  rfl

/-- THEOREM 14: no full-domain spectral exponent adapter can exist for the
current unrestricted arithmetic-admissible domain.  This is the front-door
version of P542's collapse result. -/
theorem no_fullDomainSpectralExponentCodeAdapter :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter) := by
  rintro ⟨A⟩
  have h2 := A.global_code_eq (zeroSpectralPrimeState primeTwo)
  have h3 := A.global_code_eq (zeroSpectralPrimeState primeThree)
  have h2' : (primeTwo : PrimeExponent).1 =
      A.code zeroDescentSpectralPoint := by
    simpa [CodedDescentAllowed, zeroSpectralPrimeState_arithmetic,
      zeroSpectralPrimeState_spectral, halfSigmaPrimeImage_exponent] using h2
  have h3' : (primeThree : PrimeExponent).1 =
      A.code zeroDescentSpectralPoint := by
    simpa [CodedDescentAllowed, zeroSpectralPrimeState_arithmetic,
      zeroSpectralPrimeState_spectral, halfSigmaPrimeImage_exponent] using h3
  have h23 : (primeTwo : PrimeExponent).1 =
      (primeThree : PrimeExponent).1 := h2'.trans h3'.symm
  norm_num [primeTwo, primeThree] at h23

/-! ## Packaged certificate -/

/-- Compact certificate for the coded descent front door. -/
structure CodedDescentPrimeSpineCertificate where
  producer :
    SpectralExponentCodeAdapter -> EulerPrimeCouplingProducers
  allowed :
    SpectralExponentCodeAdapter ->
      ArithmeticAdmissibleSevenFacet -> Prop
  shadow_eq_on_allowed :
    ∀ (A : SpectralExponentCodeAdapter)
      (x : ArithmeticAdmissibleSevenFacet),
      allowed A x ->
        (producer A).arithmeticShadow x.arithmetic =
          (producer A).spectralShadow x.spectral
  prime_indexed :
    ∀ A : SpectralExponentCodeAdapter,
      PrimeIndexedShadowStructure (producer A)
  common_arithmetic :
    ∀ (r : HalfSigmaArithmeticImage),
      codedDescentCommonComplete (codedDescentArithmeticShadow r) ↔
        HalfSigmaImageGoldbachComplete r
  common_spectral :
    ∀ (A : SpectralExponentCodeAdapter)
      (s : H1SpectralProjection (1 / 2 : ℝ)),
      codedDescentCommonComplete (codedDescentSpectralShadow A s) ↔
        H1SpectralNoObstructionComplete s
  no_full_domain_adapter :
    Not (Nonempty FullDomainSpectralExponentCodeAdapter)

/-- THEOREM 15: the coded descent prime-spine certificate. -/
def codedDescentPrimeSpineCertificate :
    CodedDescentPrimeSpineCertificate where
  producer := codedDescentEulerPrimeCouplingProducer
  allowed := CodedDescentAllowed
  shadow_eq_on_allowed := codedDescent_shadow_eq_of_allowed
  prime_indexed := codedDescentPrimeIndexedShadowStructure
  common_arithmetic := codedDescentCommonComplete_arithmetic
  common_spectral := codedDescentCommonComplete_spectral
  no_full_domain_adapter := no_fullDomainSpectralExponentCodeAdapter

end AffineRelaxation
end SaturationMonoid
