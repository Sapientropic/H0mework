import H0mework.Physics.Lie.SU7MotherLieAlgebra
import H0mework.Physics.Gauge.NonseparableGravityGaugeSourceAction

/-!
# A single source-generated SU(7) mother gauge connection

This module introduces one finite SU(7)-valued connection jet.  Its carrier
does not store strong, weak, or hypercharge fields.  A source-generated order
operator selects the P286 tangent image operationally; only then are the
three sector connections read from the mother connection.

The curvature is genuinely non-Abelian:

`F_{μν} = (dA)_{μν} + [A_μ,A_ν]`.

The P286 projection preserves both addition and the Lie bracket, so the
curvature of the projected connection is exactly the projection of mother
curvature.  P286 and P523 certificates remain downstream identifications and
are not fields of any datum in this file.
-/

namespace SaturationMonoid.PhysicsCore.SU7MotherGaugeTheory

open ProofFreeRicherAnholonomicSource
open SU7MotherLieAlgebra
open NonseparableGravityGaugeSourceAction
open Matrix

noncomputable section

/-- The matrix commutator closes in every finite special-unitary Lie algebra.
-/
def suLieBracket
    {n : Type*} [Fintype n] [DecidableEq n]
    (first second : SpecialUnitaryLieMatrix n) :
    SpecialUnitaryLieMatrix n := by
  refine ⟨(first : Matrix n n ℂ) * second - second * first, ?_, ?_⟩
  · rw [star_sub, star_mul, star_mul,
      specialUnitaryLieMatrix_star first,
      specialUnitaryLieMatrix_star second]
    noncomm_ring
  · rw [Matrix.trace_sub]
    exact sub_eq_zero.mpr (Matrix.trace_mul_comm
      (first : Matrix n n ℂ) (second : Matrix n n ℂ))

/-- Componentwise P286 bracket.  The hypercharge component is Abelian. -/
def p286LieBracket (first second : P286LieBlockData) : P286LieBlockData :=
  (suLieBracket first.1 second.1,
    suLieBracket first.2.1 second.2.1,
    0)

def colorCartanRaw : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun index =>
    if index = 0 then Complex.I else if index = 1 then -Complex.I else 0

def colorCartanGenerator : SU3BlockLieMatrix := by
  refine ⟨colorCartanRaw, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;> simp [colorCartanRaw]
  · simp [colorCartanRaw, Matrix.trace, Fin.sum_univ_three]

def colorMixingRaw : Matrix (Fin 3) (Fin 3) ℂ :=
  fun row column =>
    if row = 0 ∧ column = 1 then 1
    else if row = 1 ∧ column = 0 then -1
    else 0

def colorMixingGenerator : SU3BlockLieMatrix := by
  refine ⟨colorMixingRaw, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;> simp [colorMixingRaw]
  · simp [colorMixingRaw, Matrix.trace, Fin.sum_univ_three]

/-- The two color generators used by the source connection genuinely fail to
commute; the live bracket is not a decorative zero term. -/
theorem colorGenerators_bracket_entry :
    (suLieBracket colorCartanGenerator colorMixingGenerator :
      Matrix (Fin 3) (Fin 3) ℂ) 0 1 = 2 * Complex.I := by
  norm_num [suLieBracket, colorCartanGenerator, colorCartanRaw,
    colorMixingGenerator, colorMixingRaw, Matrix.mul_apply,
    Fin.sum_univ_three]
  ring

theorem colorGenerators_bracket_ne_zero :
    suLieBracket colorCartanGenerator colorMixingGenerator ≠ 0 := by
  intro bracketZero
  have entryZero := congrArg
    (fun matrix : SU3BlockLieMatrix =>
      (matrix : Matrix (Fin 3) (Fin 3) ℂ) 0 1) bracketZero
  rw [colorGenerators_bracket_entry] at entryZero
  norm_num at entryZero

def weakCartanRaw : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun index => if index = 0 then Complex.I else -Complex.I

def weakCartanGenerator : SU2BlockLieMatrix := by
  refine ⟨weakCartanRaw, ?_, ?_⟩
  · ext row column
    fin_cases row <;> fin_cases column <;> simp [weakCartanRaw]
  · simp [weakCartanRaw, Matrix.trace, Fin.sum_univ_two]

def hyperchargeGenerator : HyperchargeLieScalar := by
  refine ⟨Complex.I, ?_⟩
  change star (Complex.I : ℂ) = -Complex.I
  simp

/-- One normalized generator in each derived P286 sector. -/
def canonicalP286Generator : P286LieBlockData :=
  (colorCartanGenerator, weakCartanGenerator, hyperchargeGenerator)

def realScaleHypercharge
    (scalar : ℝ) (value : HyperchargeLieScalar) : HyperchargeLieScalar := by
  refine ⟨(scalar : ℂ) * value, ?_⟩
  change star ((scalar : ℂ) * (value : ℂ)) =
    -((scalar : ℂ) * (value : ℂ))
  rw [star_mul, value.property]
  simp
  ring

def realScaleP286 (scalar : ℝ) (data : P286LieBlockData) :
    P286LieBlockData :=
  (scalar • data.1, scalar • data.2.1,
    realScaleHypercharge scalar data.2.2)

@[simp] theorem realScaleP286_zero (data : P286LieBlockData) :
    realScaleP286 0 data = 0 := by
  ext <;> simp [realScaleP286, realScaleHypercharge]

@[simp] theorem p286LieBlockEmbed_zero :
    p286LieBlockEmbed (0 : P286LieBlockData) = 0 := by
  apply Subtype.ext
  simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
    hyperchargeLieBlock, scalarLieBlock]

theorem p286LieBlockEmbed_add (first second : P286LieBlockData) :
    p286LieBlockEmbed (first + second) =
      p286LieBlockEmbed first + p286LieBlockEmbed second := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock]; ring

theorem p286LieBlockEmbed_neg (data : P286LieBlockData) :
    p286LieBlockEmbed (-data) = -p286LieBlockEmbed data := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
      hyperchargeLieBlock, scalarLieBlock]

theorem p286LieBlockEmbed_sub (first second : P286LieBlockData) :
    p286LieBlockEmbed (first - second) =
      p286LieBlockEmbed first - p286LieBlockEmbed second := by
  rw [sub_eq_add_neg, sub_eq_add_neg, p286LieBlockEmbed_add,
    p286LieBlockEmbed_neg]

theorem p286LieBlockEmbed_bracket (first second : P286LieBlockData) :
    p286LieBlockEmbed (p286LieBracket first second) =
      suLieBracket (p286LieBlockEmbed first) (p286LieBlockEmbed second) := by
  apply Subtype.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [p286LieBlockEmbed, p286LieBracket, suLieBracket, rawP286LieBlock,
      weakHyperchargeLieBlock, hyperchargeLieBlock, scalarLieBlock,
      Matrix.fromBlocks_multiply] <;> ring

theorem p286LieBlockEmbed_injective :
    Function.Injective p286LieBlockEmbed := by
  intro first second embedded_eq
  rcases first with ⟨firstColor, firstWeak, firstHyper⟩
  rcases second with ⟨secondColor, secondWeak, secondHyper⟩
  apply Prod.ext
  · apply Subtype.ext
    ext row column
    have entryEq := congrArg
      (fun matrix : SU7MotherLieMatrix =>
        (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
          (Sum.inl row) (Sum.inl column)) embedded_eq
    simpa [p286LieBlockEmbed, rawP286LieBlock] using entryEq
  · apply Prod.ext
    · apply Subtype.ext
      ext row column
      have entryEq := congrArg
        (fun matrix : SU7MotherLieMatrix =>
          (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
            (Sum.inr (Sum.inl row)) (Sum.inr (Sum.inl column))) embedded_eq
      simpa [p286LieBlockEmbed, rawP286LieBlock,
        weakHyperchargeLieBlock] using entryEq
    · apply Subtype.ext
      have entryEq := congrArg
        (fun matrix : SU7MotherLieMatrix =>
          (matrix : Matrix SU7MotherIndex SU7MotherIndex ℂ)
            hyperPlusIndex hyperPlusIndex) embedded_eq
      simpa [p286LieBlockEmbed, rawP286LieBlock, weakHyperchargeLieBlock,
        hyperchargeLieBlock, scalarLieBlock, hyperPlusIndex] using entryEq

/-- One connection potential and its antisymmetric first jet, both valued in
the single SU(7) mother Lie algebra. -/
structure SU7MotherGaugeConnection where
  potential : LorentzianIndex → SU7MotherLieMatrix
  exteriorDerivative : Fin 6 → SU7MotherLieMatrix

def motherCurvature
    (connection : SU7MotherGaugeConnection) (pair : Fin 6) :
    SU7MotherLieMatrix :=
  connection.exteriorDerivative pair +
    suLieBracket (connection.potential (pairFirst pair))
      (connection.potential (pairSecond pair))

/-- Proof-only source breaking of one mother connection.  No projected sector
connection is stored here. -/
structure SourceSelectedMotherConnection (source : Source) where
  mother : SU7MotherGaugeConnection
  potential_selected : ∀ direction,
    SelectedBySourceBreaking source (mother.potential direction)
  exteriorDerivative_selected : ∀ pair,
    SelectedBySourceBreaking source (mother.exteriorDerivative pair)

/-- The three P286 tangent components are the codomain of a projection, not
the carrier of the mother connection. -/
structure P286BlockGaugeConnection where
  potential : LorentzianIndex → P286LieBlockData
  exteriorDerivative : Fin 6 → P286LieBlockData

def p286BlockCurvature
    (connection : P286BlockGaugeConnection) (pair : Fin 6) :
    P286LieBlockData :=
  connection.exteriorDerivative pair +
    p286LieBracket (connection.potential (pairFirst pair))
      (connection.potential (pairSecond pair))

def projectSelectedMotherConnection
    (source : Source) (connection : SourceSelectedMotherConnection source) :
    P286BlockGaugeConnection where
  potential := fun direction =>
    selectedP286LieBlockReadout source
      (connection.mother.potential direction)
      (connection.potential_selected direction)
  exteriorDerivative := fun pair =>
    selectedP286LieBlockReadout source
      (connection.mother.exteriorDerivative pair)
      (connection.exteriorDerivative_selected pair)

/-- Strong/color connection read from the projected mother connection. -/
def projectedColorConnection (connection : P286BlockGaugeConnection) :
    LorentzianIndex → SU3BlockLieMatrix :=
  fun direction => (connection.potential direction).1

/-- Weak connection read from the projected mother connection. -/
def projectedWeakConnection (connection : P286BlockGaugeConnection) :
    LorentzianIndex → SU2BlockLieMatrix :=
  fun direction => (connection.potential direction).2.1

/-- Hypercharge connection read from the projected mother connection. -/
def projectedHyperchargeConnection (connection : P286BlockGaugeConnection) :
    LorentzianIndex → HyperchargeLieScalar :=
  fun direction => (connection.potential direction).2.2

def projectedColorCurvature (connection : P286BlockGaugeConnection) :
    Fin 6 → SU3BlockLieMatrix :=
  fun pair => (p286BlockCurvature connection pair).1

def projectedWeakCurvature (connection : P286BlockGaugeConnection) :
    Fin 6 → SU2BlockLieMatrix :=
  fun pair => (p286BlockCurvature connection pair).2.1

def projectedHyperchargeCurvature (connection : P286BlockGaugeConnection) :
    Fin 6 → HyperchargeLieScalar :=
  fun pair => (p286BlockCurvature connection pair).2.2

/-- Curvature commutes with operational breaking projection. -/
theorem projectedMother_curvature_naturality
    (source : Source) (connection : SourceSelectedMotherConnection source)
    (pair : Fin 6) :
    p286LieBlockEmbed
        (p286BlockCurvature
          (projectSelectedMotherConnection source connection) pair) =
      motherCurvature connection.mother pair := by
  rw [p286BlockCurvature, motherCurvature, p286LieBlockEmbed_add,
    p286LieBlockEmbed_bracket]
  simp only [projectSelectedMotherConnection]
  rw [p286LieBlockEmbed_selectedReadout,
    p286LieBlockEmbed_selectedReadout,
    p286LieBlockEmbed_selectedReadout]

/-- The source scale multiplies two noncommuting color generators in two
connection directions.  The remaining directions are zero. -/
def sourceP286Potential (source : Source) :
    LorentzianIndex → P286LieBlockData
  | 0 => realScaleP286 source.sigma (colorCartanGenerator, 0, 0)
  | 1 => realScaleP286 source.sigma (colorMixingGenerator, 0, 0)
  | _ => 0

/-- The Stage-5 source curvature is lifted into all three normalized P286
directions.  It is a source readout, not a supplied sector configuration. -/
def sourceP286TargetCurvature (source : Source) (pair : Fin 6) :
    P286LieBlockData :=
  realScaleP286 (sourceGaugeCurvature source pair) canonicalP286Generator

/-- The first jet is generated so that the full non-Abelian curvature equals
the source target; it explicitly compensates the live `[A,A]` term. -/
def sourceP286ExteriorDerivative (source : Source) (pair : Fin 6) :
    P286LieBlockData :=
  sourceP286TargetCurvature source pair -
    p286LieBracket
      (sourceP286Potential source (pairFirst pair))
      (sourceP286Potential source (pairSecond pair))

/-- A single mother connection generated from `Source`; no three-sector
configuration is accepted as an input. -/
def sourceMotherConnection (source : Source) : SU7MotherGaugeConnection where
  potential := fun direction =>
    p286LieBlockEmbed (sourceP286Potential source direction)
  exteriorDerivative := fun pair =>
    p286LieBlockEmbed (sourceP286ExteriorDerivative source pair)

def sourceSelectedMotherConnection (source : Source) :
    SourceSelectedMotherConnection source where
  mother := sourceMotherConnection source
  potential_selected := fun direction =>
    p286LieBlockEmbed_selected source (sourceP286Potential source direction)
  exteriorDerivative_selected := fun pair =>
    p286LieBlockEmbed_selected source
      (sourceP286ExteriorDerivative source pair)

theorem sourceMotherCurvature_eq_target
    (source : Source) (pair : Fin 6) :
    motherCurvature (sourceMotherConnection source) pair =
      p286LieBlockEmbed (sourceP286TargetCurvature source pair) := by
  change
    p286LieBlockEmbed (sourceP286ExteriorDerivative source pair) +
        suLieBracket
          (p286LieBlockEmbed
            (sourceP286Potential source (pairFirst pair)))
          (p286LieBlockEmbed
            (sourceP286Potential source (pairSecond pair))) =
      p286LieBlockEmbed (sourceP286TargetCurvature source pair)
  rw [sourceP286ExteriorDerivative,
    p286LieBlockEmbed_sub, p286LieBlockEmbed_bracket]
  abel

theorem sourceProjectedMother_curvature_eq_target
    (source : Source) (pair : Fin 6) :
    p286BlockCurvature
        (projectSelectedMotherConnection source
          (sourceSelectedMotherConnection source)) pair =
      sourceP286TargetCurvature source pair := by
  apply p286LieBlockEmbed_injective
  rw [projectedMother_curvature_naturality,
    sourceSelectedMotherConnection, sourceMotherCurvature_eq_target]

theorem sourceProjectedMother_colorCurvature
    (source : Source) (pair : Fin 6) :
    projectedColorCurvature
        (projectSelectedMotherConnection source
          (sourceSelectedMotherConnection source)) pair =
      (sourceGaugeCurvature source pair) • colorCartanGenerator := by
  simpa [projectedColorCurvature, sourceP286TargetCurvature,
    realScaleP286, canonicalP286Generator] using congrArg Prod.fst
      (sourceProjectedMother_curvature_eq_target source pair)

theorem sourceProjectedMother_weakCurvature
    (source : Source) (pair : Fin 6) :
    projectedWeakCurvature
        (projectSelectedMotherConnection source
          (sourceSelectedMotherConnection source)) pair =
      (sourceGaugeCurvature source pair) • weakCartanGenerator := by
  have component := congrArg (fun data : P286LieBlockData => data.2.1)
    (sourceProjectedMother_curvature_eq_target source pair)
  simpa [projectedWeakCurvature, sourceP286TargetCurvature,
    realScaleP286, canonicalP286Generator] using component

theorem sourceProjectedMother_hyperchargeCurvature
    (source : Source) (pair : Fin 6) :
    projectedHyperchargeCurvature
        (projectSelectedMotherConnection source
          (sourceSelectedMotherConnection source)) pair =
      realScaleHypercharge (sourceGaugeCurvature source pair)
        hyperchargeGenerator := by
  have component := congrArg (fun data : P286LieBlockData => data.2.2)
    (sourceProjectedMother_curvature_eq_target source pair)
  simpa [projectedHyperchargeCurvature, sourceP286TargetCurvature,
    realScaleP286, canonicalP286Generator] using component

end
end SaturationMonoid.PhysicsCore.SU7MotherGaugeTheory
