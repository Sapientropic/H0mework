import H0mework.Arithmetic.PrimeProjection.P345

/-!
# Proposition 346: no-free-lunch boundary for the SM color route

P345 gives the honest conditional route:

`ColorSingletGoldbachObstructionLaw + confinement exclusion -> Goldbach`.

This file proves the converse calibration.  Once confinement-style exclusion is
assumed, the color-singlet classifier is not an independent source of hidden
strength: it can be reconstructed from ordinary Goldbach plus that exclusion.

Thus the Standard-Model color route is exactly:

`Goldbach + no SM-allowed obstructed color cycle`.

That is the "no free lunch" statement.  The route does not prove Goldbach
unless confinement excludes the obstructed color cycles and the color-singlet
classifier has been supplied; and if Goldbach is false, any such classifier
forces an explicit allowed obstruction by P345.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace SaturationMonoid
namespace StandardModelConstraint

open SaturationMonoid.AffineRelaxation

/-- A completed Standard-Model color route to Goldbach consists exactly of the
color-singlet classifier plus a confinement-style exclusion of allowed
obstructed prime-edge cycles. -/
structure CompletedSMColorGoldbachRoute : Prop where
  classifier : ColorSingletGoldbachObstructionLaw
  confinement : ColorConfinementExcludesPrimeEdgeObstructions

/-- THEOREM 1: a completed SM color route implies ordinary Goldbach. -/
theorem completedSMColorRoute_implies_evenGoldbach
    (R : CompletedSMColorGoldbachRoute) :
    EvenGoldbachStatement :=
  colorConfinement_plus_classifier_implies_evenGoldbach
    R.classifier R.confinement

/-- THEOREM 2: Goldbach plus confinement reconstructs the color-singlet
classifier.  Soundness becomes impossible-by-confinement; completeness is
vacuous because Goldbach supplies a decomposition for every even number. -/
theorem colorSingletLaw_of_evenGoldbach_and_confinement
    (Hgoldbach : EvenGoldbachStatement)
    (Hconf : ColorConfinementExcludesPrimeEdgeObstructions) :
    ColorSingletGoldbachObstructionLaw where
  sound := by
    intro n p q hn hsinglet hobs
    exfalso
    exact Hconf ⟨n, p, q, hn, hsinglet, hobs⟩
  complete := by
    intro n hn hbad
    exact False.elim (hbad (Hgoldbach n hn))

/-- THEOREM 3: Goldbach plus confinement gives a completed SM color route. -/
theorem completedSMColorRoute_of_evenGoldbach_and_confinement
    (Hgoldbach : EvenGoldbachStatement)
    (Hconf : ColorConfinementExcludesPrimeEdgeObstructions) :
    CompletedSMColorGoldbachRoute where
  classifier := colorSingletLaw_of_evenGoldbach_and_confinement
    Hgoldbach Hconf
  confinement := Hconf

/-- THEOREM 4: the completed SM color route is equivalent to ordinary Goldbach
plus confinement-style exclusion.  This is the calibrated boundary: the SM
route does not contain an unaccounted proof of Goldbach; it is precisely a
Goldbach theorem together with the extra color-sector exclusion claim. -/
theorem completedSMColorRoute_iff_evenGoldbach_and_confinement :
    CompletedSMColorGoldbachRoute ↔
      EvenGoldbachStatement ∧ ColorConfinementExcludesPrimeEdgeObstructions := by
  constructor
  · intro R
    exact ⟨completedSMColorRoute_implies_evenGoldbach R, R.confinement⟩
  · rintro ⟨Hgoldbach, Hconf⟩
    exact completedSMColorRoute_of_evenGoldbach_and_confinement
      Hgoldbach Hconf

/-- THEOREM 5: if Goldbach is false, no completed SM color route exists. -/
theorem no_completedSMColorRoute_of_not_evenGoldbach
    (Hbad : ¬ EvenGoldbachStatement) :
    ¬ CompletedSMColorGoldbachRoute := by
  intro R
  exact Hbad (completedSMColorRoute_implies_evenGoldbach R)

/-- THEOREM 6: if confinement-style exclusion fails, no completed SM color
route exists. -/
theorem no_completedSMColorRoute_of_not_confinement
    (Hbad : ¬ ColorConfinementExcludesPrimeEdgeObstructions) :
    ¬ CompletedSMColorGoldbachRoute := by
  intro R
  exact Hbad R.confinement

/-- THEOREM 7: a compact no-free-lunch certificate for the SM color route. -/
structure P346SMColorRouteNoFreeLunchCertificate : Prop where
  route_implies_goldbach :
    CompletedSMColorGoldbachRoute -> EvenGoldbachStatement
  law_from_goldbach_and_confinement :
    EvenGoldbachStatement ->
      ColorConfinementExcludesPrimeEdgeObstructions ->
        ColorSingletGoldbachObstructionLaw
  route_from_goldbach_and_confinement :
    EvenGoldbachStatement ->
      ColorConfinementExcludesPrimeEdgeObstructions ->
        CompletedSMColorGoldbachRoute
  route_iff_goldbach_and_confinement :
    CompletedSMColorGoldbachRoute ↔
      EvenGoldbachStatement ∧ ColorConfinementExcludesPrimeEdgeObstructions
  no_route_if_not_goldbach :
    ¬ EvenGoldbachStatement -> ¬ CompletedSMColorGoldbachRoute
  no_route_if_not_confinement :
    ¬ ColorConfinementExcludesPrimeEdgeObstructions ->
      ¬ CompletedSMColorGoldbachRoute

/-- THEOREM 8: the no-free-lunch boundary is fully formalized. -/
theorem p346SMColorRouteNoFreeLunchCertificate :
    P346SMColorRouteNoFreeLunchCertificate where
  route_implies_goldbach := completedSMColorRoute_implies_evenGoldbach
  law_from_goldbach_and_confinement :=
    colorSingletLaw_of_evenGoldbach_and_confinement
  route_from_goldbach_and_confinement :=
    completedSMColorRoute_of_evenGoldbach_and_confinement
  route_iff_goldbach_and_confinement :=
    completedSMColorRoute_iff_evenGoldbach_and_confinement
  no_route_if_not_goldbach := no_completedSMColorRoute_of_not_evenGoldbach
  no_route_if_not_confinement :=
    no_completedSMColorRoute_of_not_confinement

end StandardModelConstraint
end SaturationMonoid
