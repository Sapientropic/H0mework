import H0mework.Physics.AlphaSources.P610

/-!
# Proposition 611: minimal active-source carrier for the alpha_s residual law

P610 proves that the current finite `alpha_s` source law factors through a
singleton active-source carrier.  This file proves the matching minimality
statement: any injective carrier whose image is exactly the nonzero support of a
finite-law contribution is necessarily equivalent to `Unit`.

So the singleton active-source carrier is not merely a convenient
presentation.  It is the unique exact support carrier, up to equivalence, for
the accepted finite source law.

Boundary: this remains a theorem about the accepted finite law.  It still does
not supply the physical dynamics that selects `SU(7)` breaking as the active
source.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-! ## Exact support carriers -/

/-- A carrier `ι` exactly supports the nonzero coordinates of a contribution
function `c` when its source embedding is injective and its image is precisely
the active support of `c`. -/
def AlphaStrongExactSupportCarrierFor
    (ι : Type*) (embed : ι -> AlphaStrongResidualSource)
    (c : AlphaStrongResidualSource -> ℚ) : Prop :=
  Function.Injective embed ∧
    ∀ s : AlphaStrongResidualSource,
      (∃ i : ι, embed i = s) ↔
        AlphaStrongResidualActiveSourceSupport c s

/-- THEOREM 1: the canonical singleton active-source carrier exactly supports
any finite-law contribution function. -/
theorem alphaStrongResidualActiveSourceEmbedding_exactSupportCarrierFor
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c) :
    AlphaStrongExactSupportCarrierFor
      AlphaStrongResidualActiveSourceCarrier
      alphaStrongResidualActiveSourceEmbedding
      c := by
  constructor
  · intro x y _
    cases x
    cases y
    rfl
  · intro s
    constructor
    · rintro ⟨u, hu⟩
      exact
        (alphaStrongSU7FiniteContributionLaw_activeSupport_iff c hc s).mpr
          (by
            rw [← hu]
            cases u
            rfl)
    · intro hs
      have hs_su7 : s = AlphaStrongResidualSource.su7Breaking :=
        (alphaStrongSU7FiniteContributionLaw_activeSupport_iff c hc s).mp hs
      subst s
      exact ⟨Unit.unit, rfl⟩

/-- THEOREM 2: any exact support carrier for a finite-law contribution is
inhabited and subsingleton. -/
theorem alphaStrongExactSupportCarrier_nonempty_subsingleton_of_finiteLaw
    {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (hcarrier : AlphaStrongExactSupportCarrierFor ι embed c) :
    Nonempty ι ∧ Subsingleton ι := by
  rcases hcarrier with ⟨hembed, hsupport⟩
  have hsu7_active :
      AlphaStrongResidualActiveSourceSupport c
        AlphaStrongResidualSource.su7Breaking :=
    (alphaStrongSU7FiniteContributionLaw_activeSupport_iff
      c hc AlphaStrongResidualSource.su7Breaking).mpr rfl
  rcases (hsupport AlphaStrongResidualSource.su7Breaking).mpr
      hsu7_active with
    ⟨i0, hi0⟩
  refine ⟨⟨i0⟩, ?_⟩
  refine ⟨?_⟩
  intro i j
  have hi_active :
      AlphaStrongResidualActiveSourceSupport c (embed i) :=
    (hsupport (embed i)).mp ⟨i, rfl⟩
  have hj_active :
      AlphaStrongResidualActiveSourceSupport c (embed j) :=
    (hsupport (embed j)).mp ⟨j, rfl⟩
  have hi_su7 : embed i = AlphaStrongResidualSource.su7Breaking :=
    (alphaStrongSU7FiniteContributionLaw_activeSupport_iff
      c hc (embed i)).mp hi_active
  have hj_su7 : embed j = AlphaStrongResidualSource.su7Breaking :=
    (alphaStrongSU7FiniteContributionLaw_activeSupport_iff
      c hc (embed j)).mp hj_active
  exact hembed (hi_su7.trans hj_su7.symm)

/-- THEOREM 3: any exact support carrier for a finite-law contribution is
equivalent to `Unit`. -/
noncomputable def alphaStrongExactSupportCarrier_equiv_unit_of_finiteLaw
    {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
    (c : AlphaStrongResidualSource -> ℚ)
    (hc : AlphaStrongSU7FiniteContributionLaw c)
    (hcarrier : AlphaStrongExactSupportCarrierFor ι embed c) :
    ι ≃ Unit := by
  have h := alphaStrongExactSupportCarrier_nonempty_subsingleton_of_finiteLaw
    embed c hc hcarrier
  classical
  let i0 : ι := Classical.choice h.1
  exact
    { toFun := fun _ => Unit.unit
      invFun := fun _ => i0
      left_inv := by
        intro i
        exact h.2.elim _ _
      right_inv := by
        intro u
        cases u
        rfl }

/-- THEOREM 4: the canonical finite source contribution has a unique exact
support carrier up to equivalence with `Unit`. -/
noncomputable def canonicalAlphaStrongActiveSourceExtension_exactCarrier_equiv_unit
    {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
    (hcarrier :
      AlphaStrongExactSupportCarrierFor ι embed
        canonicalAlphaStrongActiveSourceExtension) :
    ι ≃ Unit :=
  alphaStrongExactSupportCarrier_equiv_unit_of_finiteLaw
    embed
    canonicalAlphaStrongActiveSourceExtension
    ((alphaStrongSU7FiniteContributionLaw_iff_eq_activeSourceExtension
      canonicalAlphaStrongActiveSourceExtension).mpr rfl)
    hcarrier

/-- THEOREM 5: exact support carriers for P608 combined source-surface alpha
residuals are also equivalent to `Unit`. -/
noncomputable def mainProducerObjectSourceSurface_exactCarrier_equiv_unit
    (M : MainProducerObjectCandidate)
    (hM : MainProducerObjectSourceSurface M)
    {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
    (hcarrier :
      AlphaStrongExactSupportCarrierFor ι embed
        M.alphaResidual.contribution) :
    ι ≃ Unit :=
  alphaStrongExactSupportCarrier_equiv_unit_of_finiteLaw
    embed
    M.alphaResidual.contribution
    hM.1
    hcarrier

/-! ## Receipt -/

/-- Compact receipt: the singleton active-source carrier is support-minimal
and unique up to equivalence for the finite alpha_s source law. -/
structure AlphaStrongActiveSourceMinimalCarrierReceipt where
  canonical_exact :
    ∀ c : AlphaStrongResidualSource -> ℚ,
      AlphaStrongSU7FiniteContributionLaw c ->
        AlphaStrongExactSupportCarrierFor
          AlphaStrongResidualActiveSourceCarrier
          alphaStrongResidualActiveSourceEmbedding
          c
  exact_nonempty_subsingleton :
    ∀ {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
      (c : AlphaStrongResidualSource -> ℚ),
        AlphaStrongSU7FiniteContributionLaw c ->
          AlphaStrongExactSupportCarrierFor ι embed c ->
            Nonempty ι ∧ Subsingleton ι
  exact_equiv_unit :
    ∀ {ι : Type*} (embed : ι -> AlphaStrongResidualSource)
      (c : AlphaStrongResidualSource -> ℚ),
        AlphaStrongSU7FiniteContributionLaw c ->
          AlphaStrongExactSupportCarrierFor ι embed c ->
            Nonempty (ι ≃ Unit)
  canonical_extension_equiv_unit :
    ∀ {ι : Type*} (embed : ι -> AlphaStrongResidualSource),
      AlphaStrongExactSupportCarrierFor ι embed
          canonicalAlphaStrongActiveSourceExtension ->
        Nonempty (ι ≃ Unit)
  combined_surface_equiv_unit :
    ∀ M : MainProducerObjectCandidate,
      MainProducerObjectSourceSurface M ->
        ∀ {ι : Type*} (embed : ι -> AlphaStrongResidualSource),
          AlphaStrongExactSupportCarrierFor ι embed
              M.alphaResidual.contribution ->
            Nonempty (ι ≃ Unit)

/-- THEOREM 6: minimal-carrier receipt for the finite alpha_s source law. -/
theorem alphaStrongActiveSourceMinimalCarrierReceipt :
    AlphaStrongActiveSourceMinimalCarrierReceipt where
  canonical_exact :=
    alphaStrongResidualActiveSourceEmbedding_exactSupportCarrierFor
  exact_nonempty_subsingleton := by
    intro ι embed c hc hcarrier
    exact
      alphaStrongExactSupportCarrier_nonempty_subsingleton_of_finiteLaw
        embed c hc hcarrier
  exact_equiv_unit := by
    intro ι embed c hc hcarrier
    exact
      ⟨alphaStrongExactSupportCarrier_equiv_unit_of_finiteLaw
        embed c hc hcarrier⟩
  canonical_extension_equiv_unit := by
    intro ι embed hcarrier
    exact
      ⟨canonicalAlphaStrongActiveSourceExtension_exactCarrier_equiv_unit
        embed hcarrier⟩
  combined_surface_equiv_unit := by
    intro M hM ι embed hcarrier
    exact
      ⟨mainProducerObjectSourceSurface_exactCarrier_equiv_unit
        M hM embed hcarrier⟩

end StandardModelConstraint
end SaturationMonoid
