import H0mework.Physics.Cartan.CartanContorsionTorsionEquiv

/-!
# Typed Cartan torsion three-form coordinates

This module fixes the coordinate bridges needed by the nondegenerate
Cartan response inverse.  It reuses the existing 24-dimensional typed
torsion carrier, reconstructs ordered spacetime three-form components, and
lifts the authoritative internal Hodge inverse to bivector-valued
three-forms.

The public forward is literally the existing KIN-1 expression
`star_I (T wedge e)`.  No action, current, source, residual, equation,
stationarity receipt, inverse witness, or target solution enters it.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineCartanTorsionThreeFormCoordinates

open ProofFreeRicherAnholonomicSource
open StageNineCartanContorsionTorsionEquiv
open StageNineLorentzConnectionVariation
open StageNineResidualLinearPlebanskiTorsionReduction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Evaluation of a canonical oriented three-form basis element on an
ordered triple of coordinate directions.  The six permutation signs are
`+,-,-,+,+,-`. -/
def orientedLorentzThreeFormBasisCoefficient
    (triple : Fin 4) (first second third : LorentzianIndex) : ℝ :=
  let basisFirst := threeFormFirst triple
  let basisSecond := threeFormSecond triple
  let basisThird := threeFormThird triple
  (if basisFirst = first then 1 else 0) *
      ((if basisSecond = second then 1 else 0) *
          (if basisThird = third then 1 else 0) -
        (if basisSecond = third then 1 else 0) *
          (if basisThird = second then 1 else 0)) -
    (if basisFirst = second then 1 else 0) *
      ((if basisSecond = first then 1 else 0) *
          (if basisThird = third then 1 else 0) -
        (if basisSecond = third then 1 else 0) *
          (if basisThird = first then 1 else 0)) +
    (if basisFirst = third then 1 else 0) *
      ((if basisSecond = first then 1 else 0) *
          (if basisThird = second then 1 else 0) -
        (if basisSecond = second then 1 else 0) *
          (if basisThird = first then 1 else 0))

/-- Recover an ordered spacetime three-form component. -/
def orderedSpacetimeThreeFormComponent
    (form : PhysicalBivectorThreeForm)
    (internalPair : Fin 6)
    (first second third : LorentzianIndex) : ℝ :=
  ∑ triple : Fin 4,
    form internalPair triple *
      orientedLorentzThreeFormBasisCoefficient triple first second third

@[simp] theorem orderedSpacetimeThreeFormComponent_canonical
    (form : PhysicalBivectorThreeForm)
    (internalPair : Fin 6) (triple : Fin 4) :
    orderedSpacetimeThreeFormComponent form internalPair
        (threeFormFirst triple) (threeFormSecond triple)
        (threeFormThird triple) =
      form internalPair triple := by
  fin_cases triple <;>
    simp [orderedSpacetimeThreeFormComponent,
      orientedLorentzThreeFormBasisCoefficient,
      threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_four]

/-- Recover an ordered internal bivector component while retaining the
canonical spacetime-three-form coordinate. -/
def orderedInternalBivectorThreeFormComponent
    (form : PhysicalBivectorThreeForm)
    (internalFirst internalSecond : LorentzianIndex)
    (triple : Fin 4) : ℝ :=
  ∑ internalPair : Fin 6,
    form internalPair triple *
      orientedLorentzBivectorBasisCoefficient internalPair
        internalFirst internalSecond

/-- Recover both ordered internal-bivector and spacetime-three-form
components. -/
def orderedPhysicalBivectorThreeFormComponent
    (form : PhysicalBivectorThreeForm)
    (internalFirst internalSecond : LorentzianIndex)
    (first second third : LorentzianIndex) : ℝ :=
  ∑ triple : Fin 4,
    orderedInternalBivectorThreeFormComponent form
        internalFirst internalSecond triple *
      orientedLorentzThreeFormBasisCoefficient triple first second third

/-- The inverse internal Hodge on each spacetime three-form coordinate. -/
def internalBivectorUndualThreeForm
    (form : PhysicalBivectorThreeForm) : PhysicalBivectorThreeForm :=
  fun internalPair triple =>
    -lorentzianCoframeHodge
      (fun sourceInternalPair => form sourceInternalPair triple)
      internalPair

@[simp] theorem internalBivectorUndualThreeForm_dual
    (form : PhysicalBivectorThreeForm) :
    internalBivectorUndualThreeForm
        (internalBivectorDualThreeForm form) = form := by
  funext internalPair triple
  fin_cases internalPair <;>
    simp [internalBivectorUndualThreeForm,
      internalBivectorDualThreeForm, lorentzianCoframeHodge]

@[simp] theorem internalBivectorDualThreeForm_undual
    (form : PhysicalBivectorThreeForm) :
    internalBivectorDualThreeForm
        (internalBivectorUndualThreeForm form) = form := by
  funext internalPair triple
  fin_cases internalPair <;>
    simp [internalBivectorUndualThreeForm,
      internalBivectorDualThreeForm, lorentzianCoframeHodge]

/-- Raw ordered torsion readout with argument order expected by the existing
`torsionCoframeWedgeThreeForm`. -/
def rawPointwiseCartanTorsion
    (torsion : PointwiseCartanTorsionTwoForm)
    (first second internal : LorentzianIndex) : ℝ :=
  orderedCartanTorsionComponent torsion internal first second

@[simp] theorem rawPointwiseCartanTorsion_canonical
    (torsion : PointwiseCartanTorsionTwoForm)
    (pair : Fin 6) (internal : LorentzianIndex) :
    rawPointwiseCartanTorsion torsion
        (pairFirst pair) (pairSecond pair) internal =
      torsion pair internal := by
  exact orderedCartanTorsionComponent_canonical torsion internal pair

theorem rawPointwiseCartanTorsion_antisymm
    (torsion : PointwiseCartanTorsionTwoForm)
    (first second internal : LorentzianIndex) :
    rawPointwiseCartanTorsion torsion first second internal =
      -rawPointwiseCartanTorsion torsion second first internal := by
  exact orderedCartanTorsionComponent_antisymm torsion internal first second

@[simp] theorem rawPointwiseCartanTorsion_diagonal
    (torsion : PointwiseCartanTorsionTwoForm)
    (direction internal : LorentzianIndex) :
    rawPointwiseCartanTorsion torsion direction direction internal = 0 := by
  exact orderedCartanTorsionComponent_diagonal torsion internal direction

/-- The undualized, existing KIN-1 torsion--coframe wedge. -/
def cartanTorsionCoframeWedgeThreeForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm) :
    PhysicalBivectorThreeForm :=
  torsionCoframeWedgeThreeForm coframe
    (rawPointwiseCartanTorsion torsion)

/-- Ordered internal-bivector reconstruction of the existing
torsion--coframe wedge at a canonical spacetime triple. -/
theorem orderedInternal_cartanTorsionCoframeWedgeThreeForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internalFirst internalSecond : LorentzianIndex)
    (triple : Fin 4) :
    orderedInternalBivectorThreeFormComponent
        (cartanTorsionCoframeWedgeThreeForm coframe torsion)
        internalFirst internalSecond triple =
      rawPointwiseCartanTorsion torsion
          (threeFormFirst triple) (threeFormSecond triple) internalFirst *
            coframe internalSecond (threeFormThird triple) +
        rawPointwiseCartanTorsion torsion
          (threeFormSecond triple) (threeFormThird triple) internalFirst *
            coframe internalSecond (threeFormFirst triple) +
        rawPointwiseCartanTorsion torsion
          (threeFormThird triple) (threeFormFirst triple) internalFirst *
            coframe internalSecond (threeFormSecond triple) -
        rawPointwiseCartanTorsion torsion
          (threeFormFirst triple) (threeFormSecond triple) internalSecond *
            coframe internalFirst (threeFormThird triple) -
        rawPointwiseCartanTorsion torsion
          (threeFormSecond triple) (threeFormThird triple) internalSecond *
            coframe internalFirst (threeFormFirst triple) -
        rawPointwiseCartanTorsion torsion
          (threeFormThird triple) (threeFormFirst triple) internalSecond *
            coframe internalFirst (threeFormSecond triple) := by
  fin_cases internalFirst <;> fin_cases internalSecond <;>
    simp [orderedInternalBivectorThreeFormComponent,
      cartanTorsionCoframeWedgeThreeForm,
      torsionCoframeWedgeThreeForm,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond, Fin.sum_univ_six] <;>
    ring

/-- Fully ordered reconstruction of the authoritative undualized response. -/
theorem ordered_cartanTorsionCoframeWedgeThreeForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm)
    (internalFirst internalSecond : LorentzianIndex)
    (first second third : LorentzianIndex) :
    orderedPhysicalBivectorThreeFormComponent
        (cartanTorsionCoframeWedgeThreeForm coframe torsion)
        internalFirst internalSecond first second third =
      rawPointwiseCartanTorsion torsion first second internalFirst *
            coframe internalSecond third +
        rawPointwiseCartanTorsion torsion second third internalFirst *
            coframe internalSecond first +
        rawPointwiseCartanTorsion torsion third first internalFirst *
            coframe internalSecond second -
        rawPointwiseCartanTorsion torsion first second internalSecond *
            coframe internalFirst third -
        rawPointwiseCartanTorsion torsion second third internalSecond *
            coframe internalFirst first -
        rawPointwiseCartanTorsion torsion third first internalSecond *
            coframe internalFirst second := by
  unfold orderedPhysicalBivectorThreeFormComponent
  simp_rw [orderedInternal_cartanTorsionCoframeWedgeThreeForm]
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    simp [orientedLorentzThreeFormBasisCoefficient,
      rawPointwiseCartanTorsion,
      orderedCartanTorsionComponent,
      orientedLorentzBivectorBasisCoefficient,
      pairFirst, pairSecond,
      threeFormFirst, threeFormSecond, threeFormThird,
      Fin.sum_univ_four, Fin.sum_univ_six] <;>
    ring

/-- Authoritative action-facing Cartan response `star_I (T wedge e)`. -/
def cartanTorsionThreeForm
    (coframe : LorentzianCoframe)
    (torsion : PointwiseCartanTorsionTwoForm) :
    PhysicalBivectorThreeForm :=
  internalBivectorDualThreeForm
    (cartanTorsionCoframeWedgeThreeForm coframe torsion)

end

end
  SaturationMonoid.PhysicsCore.StageNineCartanTorsionThreeFormCoordinates
