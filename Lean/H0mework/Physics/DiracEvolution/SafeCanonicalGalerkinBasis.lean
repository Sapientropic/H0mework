import H0mework.Physics.DiracEvolution.SafeCountableDenseTestCarrier
import H0mework.Physics.DiracEvolution.SafeWeakEnergyEstimate
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Canonical interior Galerkin basis

This module constructs the nested, source-independent finite test spaces used
by the fixed P506/L0 matter approximation producer.  A canonical cutoff
exhaustion first replaces the incompatible globally supported dense tests by
an interior-supported dense enumeration.  Each finite prefix is then reduced
to a genuine basis of its span, so the action synthesis is faithful while all
entered tests retain exact finite representation.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis

open Filter MeasureTheory Set
open ProofFreeRicherAnholonomicSource
open StageNineCauchySafeMatterCountableDenseTestCarrier
open StageNineCauchySafeMatterSpatialL2TestCarrier
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracDualFormNativeFixedP506CauchySafeMatterWeakEnergyEstimate
open StageNineDiracMatterWeakSpatialGalerkinMass
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open StageNineSourceActionGeneratedP506MatterCurrentCanonicalLorentzAdjointDiagonalActual
open scoped ContDiff Topology

noncomputable section

set_option autoImplicit false

local instance two_ne_top : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- The canonical smooth cutoff for the `level`-th interior exhaustion of a
fixed spatial box. -/
def cauchySafeMatterCanonicalBoxCutoff
    (a b : DiracMatterSpatialCoordinates)
    (level : ℕ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  ∏ direction : Fin 3,
    Real.smoothTransition
        ((level + 1 : ℕ) * (space direction - a direction)) *
      Real.smoothTransition
        ((level + 1 : ℕ) * (b direction - space direction))

theorem cauchySafeMatterCanonicalBoxCutoff_contDiff
    (a b : DiracMatterSpatialCoordinates)
    (level : ℕ) :
    ContDiff ℝ ∞ (cauchySafeMatterCanonicalBoxCutoff a b level) := by
  unfold cauchySafeMatterCanonicalBoxCutoff
  fun_prop

theorem cauchySafeMatterCanonicalBoxCutoff_mem_Icc
    (a b : DiracMatterSpatialCoordinates)
    (level : ℕ)
    (space : DiracMatterSpatialCoordinates) :
    cauchySafeMatterCanonicalBoxCutoff a b level space ∈ Icc (0 : ℝ) 1 := by
  refine ⟨Finset.prod_nonneg fun direction _ ↦ mul_nonneg
    (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
  apply Finset.prod_le_one
  · intro direction _
    exact mul_nonneg (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.nonneg _)
  · intro direction _
    calc
      Real.smoothTransition
            ((level + 1 : ℕ) * (space direction - a direction)) *
          Real.smoothTransition
            ((level + 1 : ℕ) * (b direction - space direction))
          ≤ Real.smoothTransition
              ((level + 1 : ℕ) * (space direction - a direction)) * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)
      _ = Real.smoothTransition
          ((level + 1 : ℕ) * (space direction - a direction)) := mul_one _
      _ ≤ 1 := Real.smoothTransition.le_one _

theorem cauchySafeMatterCanonicalBoxCutoff_zero_of_not_interior
    (a b : DiracMatterSpatialCoordinates)
    (level : ℕ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    cauchySafeMatterCanonicalBoxCutoff a b level space = 0 := by
  simp only [DiracMatterSpatialBoxInterior, not_forall] at outside
  obtain ⟨direction, outside⟩ := outside
  unfold cauchySafeMatterCanonicalBoxCutoff
  rw [Finset.prod_eq_zero (Finset.mem_univ direction)]
  by_cases leftInside : a direction < space direction
  · have rightOutside : b direction ≤ space direction :=
      le_of_not_gt fun rightInside ↦ outside ⟨leftInside, rightInside⟩
    have rightZero : Real.smoothTransition
        ((level + 1 : ℕ) * (b direction - space direction)) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (sub_nonpos.mpr rightOutside))
    exact mul_eq_zero.mpr (Or.inr rightZero)
  · have leftOutside : space direction ≤ a direction := le_of_not_gt leftInside
    have leftZero : Real.smoothTransition
        ((level + 1 : ℕ) * (space direction - a direction)) = 0 :=
      Real.smoothTransition.zero_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (sub_nonpos.mpr leftOutside))
    exact mul_eq_zero.mpr (Or.inl leftZero)

theorem cauchySafeMatterCanonicalBoxCutoff_hasCompactSupport
    (a b : DiracMatterSpatialCoordinates)
    (level : ℕ) :
    HasCompactSupport (cauchySafeMatterCanonicalBoxCutoff a b level) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro space spaceOutside
  apply cauchySafeMatterCanonicalBoxCutoff_zero_of_not_interior
  intro interior
  exact spaceOutside ⟨fun direction ↦ (interior direction).1.le,
    fun direction ↦ (interior direction).2.le⟩

theorem cauchySafeMatterCanonicalBoxCutoff_eventually_eq_one
    (a b : DiracMatterSpatialCoordinates)
    (space : DiracMatterSpatialCoordinates)
    (interior : DiracMatterSpatialBoxInterior a b space) :
    ∀ᶠ level : ℕ in atTop,
      cauchySafeMatterCanonicalBoxCutoff a b level space = 1 := by
  have leftPositive : ∀ direction : Fin 3,
      0 < space direction - a direction := fun direction ↦
    sub_pos.mpr (interior direction).1
  have rightPositive : ∀ direction : Fin 3,
      0 < b direction - space direction := fun direction ↦
    sub_pos.mpr (interior direction).2
  choose leftEntry leftEntrySpec using fun direction ↦
    exists_nat_ge (1 / (space direction - a direction))
  choose rightEntry rightEntrySpec using fun direction ↦
    exists_nat_ge (1 / (b direction - space direction))
  let entry := max (Finset.univ.sup leftEntry) (Finset.univ.sup rightEntry)
  filter_upwards [eventually_ge_atTop entry] with level levelLarge
  unfold cauchySafeMatterCanonicalBoxCutoff
  apply Finset.prod_eq_one
  intro direction _
  have leftLarge : leftEntry direction ≤ level := by
    exact le_trans (Finset.le_sup (Finset.mem_univ direction))
      (le_trans (le_max_left _ _) levelLarge)
  have rightLarge : rightEntry direction ≤ level := by
    exact le_trans (Finset.le_sup (Finset.mem_univ direction))
      (le_trans (le_max_right _ _) levelLarge)
  have leftOne : Real.smoothTransition
      ((level + 1 : ℕ) * (space direction - a direction)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have entryBound : 1 / (space direction - a direction) ≤ level :=
      (leftEntrySpec direction).trans (by exact_mod_cast leftLarge)
    calc
      1 = (1 / (space direction - a direction)) *
          (space direction - a direction) :=
        (one_div_mul_cancel (leftPositive direction).ne').symm
      _ ≤ (level : ℝ) * (space direction - a direction) :=
        mul_le_mul_of_nonneg_right entryBound (leftPositive direction).le
      _ ≤ ((level + 1 : ℕ) : ℝ) * (space direction - a direction) :=
        mul_le_mul_of_nonneg_right (by norm_num) (leftPositive direction).le
  have rightOne : Real.smoothTransition
      ((level + 1 : ℕ) * (b direction - space direction)) = 1 := by
    apply Real.smoothTransition.one_of_one_le
    have entryBound : 1 / (b direction - space direction) ≤ level :=
      (rightEntrySpec direction).trans (by exact_mod_cast rightLarge)
    calc
      1 = (1 / (b direction - space direction)) *
          (b direction - space direction) :=
        (one_div_mul_cancel (rightPositive direction).ne').symm
      _ ≤ (level : ℝ) * (b direction - space direction) :=
        mul_le_mul_of_nonneg_right entryBound (rightPositive direction).le
      _ ≤ ((level + 1 : ℕ) : ℝ) * (b direction - space direction) :=
        mul_le_mul_of_nonneg_right (by norm_num) (rightPositive direction).le
  rw [leftOne, rightOne, one_mul]

/-- A generated smooth test multiplied by one canonical interior cutoff. -/
def cauchySafeMatterCanonicalInteriorTest
    (a b : DiracMatterSpatialCoordinates)
    (test level : ℕ) : CauchySafeMatterSmoothCompactTest := by
  refine ⟨fun space ↦
    cauchySafeMatterCanonicalBoxCutoff a b level space •
      (cauchySafeMatterCountableDenseTest a b test).1 space, ?_⟩
  constructor
  · exact (cauchySafeMatterCanonicalBoxCutoff_hasCompactSupport
      a b level).smul_right
  · exact (cauchySafeMatterCanonicalBoxCutoff_contDiff a b level).smul
      (cauchySafeMatterCountableDenseTest a b test).property.2

theorem cauchySafeMatterCanonicalInteriorTest_zero_of_not_interior
    (a b : DiracMatterSpatialCoordinates)
    (test level : ℕ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    (cauchySafeMatterCanonicalInteriorTest a b test level).1 space = 0 := by
  simp only [cauchySafeMatterCanonicalInteriorTest]
  rw [cauchySafeMatterCanonicalBoxCutoff_zero_of_not_interior
    a b level space outside, zero_smul]

private theorem canonicalInteriorTest_uniformIntegrable
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    UnifIntegrable
      (fun level space ↦
        (cauchySafeMatterCanonicalInteriorTest a b test level).1 space)
      2 (volume.restrict (Icc a b)) := by
  let original : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    (cauchySafeMatterCountableDenseTest a b test).1
  have originalMemLp : MemLp original 2 (volume.restrict (Icc a b)) :=
    cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCountableDenseTest a b test)
  have originalUniform : UnifIntegrable
      (fun _ : ℕ ↦ original) 2 (volume.restrict (Icc a b)) :=
    unifIntegrable_const (p := (2 : ENNReal)) (by norm_num) (by norm_num)
      originalMemLp
  intro epsilon epsilonPositive
  obtain ⟨delta, deltaPositive, originalSmall⟩ :=
    originalUniform epsilonPositive
  refine ⟨delta, deltaPositive, fun level measurableSet measurable hmeasure ↦ ?_⟩
  apply (eLpNorm_mono_ae (μ := volume.restrict (Icc a b)) ?_).trans
    (originalSmall level measurableSet measurable hmeasure)
  filter_upwards [] with space
  by_cases spaceMem : space ∈ measurableSet
  · rw [Set.indicator_of_mem spaceMem, Set.indicator_of_mem spaceMem]
    change ‖cauchySafeMatterCanonicalBoxCutoff a b level space •
        original space‖ ≤ ‖original space‖
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (cauchySafeMatterCanonicalBoxCutoff_mem_Icc
        a b level space).1]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (cauchySafeMatterCanonicalBoxCutoff_mem_Icc a b level space).2
  · simp [Set.indicator_of_notMem spaceMem]

private theorem canonicalInteriorTest_ae_tendsto
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    ∀ᵐ space ∂volume.restrict (Icc a b),
      Tendsto
        (fun level ↦
          (cauchySafeMatterCanonicalInteriorTest a b test level).1 space)
        atTop
        (𝓝 ((cauchySafeMatterCountableDenseTest a b test).1 space)) := by
  have boxAE :
      (pi univ fun direction : Fin 3 ↦ Ioo (a direction) (b direction))
        =ᵐ[volume] Icc a b := by
    simpa only [MeasureTheory.volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc
        (μ := fun _ : Fin 3 ↦ (volume : Measure ℝ))
        (f := a) (g := b))
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [boxAE] with space boxEq spaceMem
  have interior : DiracMatterSpatialBoxInterior a b space := by
    have spaceOpen : space ∈
        pi univ fun direction : Fin 3 ↦ Ioo (a direction) (b direction) :=
      boxEq.mpr spaceMem
    intro direction
    exact spaceOpen direction (mem_univ direction)
  apply tendsto_const_nhds.congr'
  filter_upwards [cauchySafeMatterCanonicalBoxCutoff_eventually_eq_one
    a b space interior] with level cutoffOne
  simp [cauchySafeMatterCanonicalInteriorTest, cutoffOne]

/-- The interior cutoff exhaustion converges in the physical spatial `L²`
carrier to the original generated test. -/
theorem cauchySafeMatterCanonicalInteriorTestToL2_tendsto
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    Tendsto
      (fun level ↦ cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorTest a b test level))
      atTop
      (𝓝 (cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCountableDenseTest a b test))) := by
  letI : IsFiniteMeasure (volume.restrict (Icc a b)) :=
    { measure_univ_lt_top := by simp [isCompact_Icc.measure_lt_top] }
  let cutoffField : ℕ → DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    fun level ↦ (cauchySafeMatterCanonicalInteriorTest a b test level).1
  let original : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    (cauchySafeMatterCountableDenseTest a b test).1
  have cutoffMemLp : ∀ level,
      MemLp (cutoffField level) 2 (volume.restrict (Icc a b)) := fun level ↦
    cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCanonicalInteriorTest a b test level)
  have originalMemLp : MemLp original 2 (volume.restrict (Icc a b)) :=
    cauchySafeMatterSmoothCompactTest_memLp a b
      (cauchySafeMatterCountableDenseTest a b test)
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' cutoffField cutoffMemLp
    original originalMemLp).2
  exact tendsto_Lp_finite_of_tendsto_ae (p := (2 : ENNReal))
    (by norm_num) (by norm_num)
    (fun level ↦ (cutoffMemLp level).1) originalMemLp
    (canonicalInteriorTest_uniformIntegrable a b test)
    (canonicalInteriorTest_ae_tendsto a b test)

/-- The original `L²`-dense enumeration of the full cutoff exhaustion.  It is
retained as the density witness for the stronger first-jet enumeration below. -/
def cauchySafeMatterCanonicalInteriorL2DenseTest
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ) : CauchySafeMatterSmoothCompactTest :=
  cauchySafeMatterCanonicalInteriorTest a b
    (Nat.unpair index).1 (Nat.unpair index).2

theorem cauchySafeMatterCanonicalInteriorL2DenseTest_zero_of_not_interior
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    (cauchySafeMatterCanonicalInteriorL2DenseTest a b index).1 space = 0 := by
  exact cauchySafeMatterCanonicalInteriorTest_zero_of_not_interior a b
    (Nat.unpair index).1 (Nat.unpair index).2 space outside

/-- The cutoff enumeration remains dense in the same
physical spatial `L²` carrier. -/
theorem cauchySafeMatterCanonicalInteriorL2DenseTest_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (fun index ↦
      cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorL2DenseTest a b index)) := by
  let original : ℕ → CauchySafeMatterSpatialL2 a b := fun test ↦
    cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCountableDenseTest a b test)
  let interior : ℕ → CauchySafeMatterSpatialL2 a b := fun index ↦
    cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorL2DenseTest a b index)
  have originalSubset : range original ⊆ closure (range interior) := by
    rintro _ ⟨test, rfl⟩
    apply mem_closure_of_tendsto
      (cauchySafeMatterCanonicalInteriorTestToL2_tendsto a b test)
    filter_upwards [] with level
    refine ⟨Nat.pair test level, ?_⟩
    simp [interior, cauchySafeMatterCanonicalInteriorL2DenseTest]
  have closureSubset : closure (range original) ⊆ closure (range interior) :=
    closure_minimal originalSubset isClosed_closure
  change Dense (range interior)
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro field
  apply closureSubset
  rw [(cauchySafeMatterCountableDenseTest_denseRange a b).closure_eq]
  exact mem_univ field

local instance canonicalMatterCoordinateSeparableSpace :
    TopologicalSpace.SeparableSpace MatterCoordinateCarrier :=
  TopologicalSpace.SecondCountableTopology.to_separableSpace

local instance canonicalFirstJetL2SecondCountable
    (a b : DiracMatterSpatialCoordinates) :
    SecondCountableTopology (CauchySafeMatterSpatialL2 a b) :=
  MeasureTheory.Lp.SecondCountableTopology

/-- Smooth compact tests supported in the open canonical box. -/
def CauchySafeMatterCanonicalInteriorSmoothTest
    (a b : DiracMatterSpatialCoordinates) :=
  { test : CauchySafeMatterSmoothCompactTest //
    ∀ space, ¬ DiracMatterSpatialBoxInterior a b space → test.1 space = 0 }

/-- One spatial derivative of an interior smooth test, retained before
completion as an exact smooth compact test. -/
def cauchySafeMatterCanonicalInteriorSmoothTestDerivative
    {a b : DiracMatterSpatialCoordinates}
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b)
    (direction : Fin 3) : CauchySafeMatterSmoothCompactTest := by
  refine ⟨fun space ↦
    fderiv ℝ (test.1.1 : DiracMatterSpatialCoordinates →
      MatterCoordinateCarrier) space (Pi.single direction 1), ?_⟩
  constructor
  · exact test.1.property.1.fderiv_apply ℝ (Pi.single direction 1)
  · exact (test.1.property.2.fderiv_right (m := ∞) (by simp)).clm_apply
      contDiff_const

/-- The exact finite spatial first-jet topology of canonical action tests. -/
abbrev CauchySafeMatterCanonicalInteriorFirstJetL2
    (a b : DiracMatterSpatialCoordinates) :=
  CauchySafeMatterSpatialL2 a b ×
    (Fin 3 → CauchySafeMatterSpatialL2 a b)

def cauchySafeMatterCanonicalInteriorFirstJetToL2
    (a b : DiracMatterSpatialCoordinates)
    (test : CauchySafeMatterCanonicalInteriorSmoothTest a b) :
    CauchySafeMatterCanonicalInteriorFirstJetL2 a b :=
  (cauchySafeMatterSmoothCompactTestToL2 a b test.1,
    fun direction ↦ cauchySafeMatterSmoothCompactTestToL2 a b
      (cauchySafeMatterCanonicalInteriorSmoothTestDerivative test direction))

private abbrev CauchySafeMatterCanonicalInteriorFirstJetRange
    (a b : DiracMatterSpatialCoordinates) :=
  Set.range (cauchySafeMatterCanonicalInteriorFirstJetToL2 a b)

private def cauchySafeMatterCanonicalInteriorSmoothTestZero
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorSmoothTest a b :=
  ⟨0, by simp⟩

local instance canonicalFirstJetRangeNonempty
    (a b : DiracMatterSpatialCoordinates) :
    Nonempty (CauchySafeMatterCanonicalInteriorFirstJetRange a b) :=
  ⟨⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
      (cauchySafeMatterCanonicalInteriorSmoothTestZero a b),
    ⟨cauchySafeMatterCanonicalInteriorSmoothTestZero a b, rfl⟩⟩⟩

/-- The unique canonical enumeration is selected inside the exact spatial
first-jet image of the existing interior smooth-test carrier. -/
def cauchySafeMatterCanonicalInteriorFirstJetDenseTest
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ) : CauchySafeMatterCanonicalInteriorSmoothTest a b :=
  Classical.choose
    ((TopologicalSpace.denseSeq
      (CauchySafeMatterCanonicalInteriorFirstJetRange a b) index).property)

theorem cauchySafeMatterCanonicalInteriorFirstJetDenseTest_jet
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ) :
    cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
        (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index) =
      (TopologicalSpace.denseSeq
        (CauchySafeMatterCanonicalInteriorFirstJetRange a b) index).1 :=
  Classical.choose_spec
    ((TopologicalSpace.denseSeq
      (CauchySafeMatterCanonicalInteriorFirstJetRange a b) index).property)

/-- Every interior smooth action test is approximated simultaneously in
value and in all three spatial derivatives. -/
theorem cauchySafeMatterCanonicalInteriorFirstJetDenseTest_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (fun index ↦
      (⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
          (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index),
        ⟨cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index,
          rfl⟩⟩ : CauchySafeMatterCanonicalInteriorFirstJetRange a b)) := by
  have functionEq : (fun index ↦
      (⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b
          (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index),
        ⟨cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index,
          rfl⟩⟩ : CauchySafeMatterCanonicalInteriorFirstJetRange a b)) =
      TopologicalSpace.denseSeq
        (CauchySafeMatterCanonicalInteriorFirstJetRange a b) := by
    funext index
    apply Subtype.ext
    exact cauchySafeMatterCanonicalInteriorFirstJetDenseTest_jet a b index
  rw [functionEq]
  exact TopologicalSpace.denseRange_denseSeq _

private def cauchySafeMatterCanonicalInteriorFirstJetRangeValue
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorFirstJetRange a b →
      CauchySafeMatterSpatialL2 a b :=
  fun jet ↦ jet.1.1

private theorem cauchySafeMatterCanonicalInteriorFirstJetRangeValue_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (cauchySafeMatterCanonicalInteriorFirstJetRangeValue a b) := by
  apply (cauchySafeMatterCanonicalInteriorL2DenseTest_denseRange a b).mono
  rintro _ ⟨index, rfl⟩
  let test : CauchySafeMatterCanonicalInteriorSmoothTest a b :=
    ⟨cauchySafeMatterCanonicalInteriorL2DenseTest a b index,
      cauchySafeMatterCanonicalInteriorL2DenseTest_zero_of_not_interior
        a b index⟩
  exact ⟨⟨cauchySafeMatterCanonicalInteriorFirstJetToL2 a b test,
    ⟨test, rfl⟩⟩, rfl⟩

/-- Authoritative canonical interior tests: the first-jet-dense sequence,
viewed in the original smooth compact carrier. -/
def cauchySafeMatterCanonicalInteriorDenseTest
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ) : CauchySafeMatterSmoothCompactTest :=
  (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index).1

theorem cauchySafeMatterCanonicalInteriorDenseTest_zero_of_not_interior
    (a b : DiracMatterSpatialCoordinates)
    (index : ℕ)
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    (cauchySafeMatterCanonicalInteriorDenseTest a b index).1 space = 0 :=
  (cauchySafeMatterCanonicalInteriorFirstJetDenseTest a b index).property
    space outside

/-- First-jet strengthening preserves the exact physical `L²` density
consumed by the existing finite action and Volterra actualization. -/
theorem cauchySafeMatterCanonicalInteriorDenseTest_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (fun index ↦
      cauchySafeMatterSmoothCompactTestToL2 a b
        (cauchySafeMatterCanonicalInteriorDenseTest a b index)) := by
  have denseComposition :=
    (cauchySafeMatterCanonicalInteriorFirstJetRangeValue_denseRange a b).comp
      (cauchySafeMatterCanonicalInteriorFirstJetDenseTest_denseRange a b)
      (continuous_fst.comp continuous_subtype_val)
  exact denseComposition

/-- Algebraic span of the canonical interior-supported dense tests. -/
abbrev CauchySafeMatterCanonicalInteriorTestSpan
    (a b : DiracMatterSpatialCoordinates) :=
  Submodule.span ℝ
    (Set.range (cauchySafeMatterCanonicalInteriorDenseTest a b))

/-- Canonical interior test span embedded in the physical spatial `L²`
carrier. -/
def cauchySafeMatterCanonicalInteriorTestSpanToL2
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterCanonicalInteriorTestSpan a b →ₗ[ℝ]
      CauchySafeMatterSpatialL2 a b :=
  (cauchySafeMatterSmoothCompactTestToL2 a b).comp
    (Submodule.subtype (CauchySafeMatterCanonicalInteriorTestSpan a b))

theorem cauchySafeMatterCanonicalInteriorTestSpanToL2_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (cauchySafeMatterCanonicalInteriorTestSpanToL2 a b) := by
  apply (cauchySafeMatterCanonicalInteriorDenseTest_denseRange a b).mono
  rintro _ ⟨index, rfl⟩
  refine ⟨⟨cauchySafeMatterCanonicalInteriorDenseTest a b index, ?_⟩, rfl⟩
  exact Submodule.subset_span (Set.mem_range_self index)

/-- Canonical time-independent spacetime extension of one interior-supported
dense test. -/
def cauchySafeMatterCanonicalInteriorDenseSpacetimeTest
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) : BasePoint → MatterCoordinateCarrier :=
  fun point ↦
    (cauchySafeMatterCanonicalInteriorDenseTest a b test).1
      ((EuclideanSpace.equiv (Fin 3) ℝ) (canonicalSpatialProjection point))

theorem cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_contDiff_one
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ) :
    ContDiff ℝ 1
      (cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test) := by
  exact ((cauchySafeMatterCanonicalInteriorDenseTest a b test).property.2.of_le
      (by norm_num)).comp
    ((EuclideanSpace.equiv (Fin 3) ℝ).toContinuousLinearEquiv.contDiff.comp
      canonicalSpatialProjection.contDiff)

@[simp] theorem cauchySafeMatterCanonicalInteriorDenseSpacetimeTest_slice
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    cauchySafeMatterCanonicalInteriorDenseSpacetimeTest a b test
        (diracMatterSpacetimeCoordinatePoint time space) =
      (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space := by
  simp only [cauchySafeMatterCanonicalInteriorDenseSpacetimeTest,
    diracMatterSpacetimeCoordinatePoint, canonicalSpatialProjection_slice]
  exact congrArg
    (cauchySafeMatterCanonicalInteriorDenseTest a b test).1
    ((EuclideanSpace.equiv (Fin 3) ℝ).apply_symm_apply space)

/-- Smooth real scalar test functions which vanish off the open spatial box.
This is the ambient carrier from which the finite Galerkin spaces are cut. -/
def cauchySafeMatterCanonicalInteriorScalarTestSubmodule
    (a b : DiracMatterSpatialCoordinates) :
    Submodule ℝ (DiracMatterSpatialCoordinates → ℝ) where
  carrier test :=
    HasCompactSupport test ∧ ContDiff ℝ ∞ test ∧
      ∀ space, ¬ DiracMatterSpatialBoxInterior a b space → test space = 0
  zero_mem' := ⟨HasCompactSupport.zero, contDiff_const, by simp⟩
  add_mem' := by
    intro first second firstMem secondMem
    exact ⟨firstMem.1.add secondMem.1, firstMem.2.1.add secondMem.2.1,
      fun space outside ↦ by rw [Pi.add_apply, firstMem.2.2 space outside,
        secondMem.2.2 space outside, add_zero]⟩
  smul_mem' := by
    intro parameter test testMem
    exact ⟨testMem.1.smul_left, testMem.2.1.const_smul parameter,
      fun space outside ↦ by rw [Pi.smul_apply, testMem.2.2 space outside,
        smul_zero]⟩

private def canonicalInteriorTestCoordinateCLM
    (coordinate : MatterCoordinateIndex) :
    MatterCoordinateCarrier →L[ℝ] ℂ :=
  (EuclideanSpace.proj coordinate).restrictScalars ℝ

/-- The real or imaginary scalar coordinate of one generated interior test. -/
def cauchySafeMatterCanonicalInteriorScalarGenerator
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (coordinate : MatterCoordinateIndex)
    (component : Fin 2) :
    cauchySafeMatterCanonicalInteriorScalarTestSubmodule a b := by
  let vectorTest := cauchySafeMatterCanonicalInteriorDenseTest a b test
  let complexCoordinate : DiracMatterSpatialCoordinates → ℂ :=
    canonicalInteriorTestCoordinateCLM coordinate ∘ vectorTest.1
  let scalarCoordinate : DiracMatterSpatialCoordinates → ℝ :=
    if component = 0 then Complex.re ∘ complexCoordinate
    else Complex.im ∘ complexCoordinate
  refine ⟨scalarCoordinate, ?_⟩
  change HasCompactSupport scalarCoordinate ∧ ContDiff ℝ ∞ scalarCoordinate ∧
    ∀ space, ¬ DiracMatterSpatialBoxInterior a b space →
      scalarCoordinate space = 0
  have vectorEventually := vectorTest.property.1
  rw [hasCompactSupport_iff_eventuallyEq] at vectorEventually ⊢
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [vectorEventually] with space vectorZero
    change vectorTest.1 space = 0 at vectorZero
    by_cases realPart : component = 0
    · rw [show scalarCoordinate = Complex.re ∘ complexCoordinate by
        simp [scalarCoordinate, realPart]]
      change (canonicalInteriorTestCoordinateCLM coordinate
        (vectorTest.1 space)).re = 0
      rw [vectorZero]
      rfl
    · rw [show scalarCoordinate = Complex.im ∘ complexCoordinate by
        simp [scalarCoordinate, realPart]]
      change (canonicalInteriorTestCoordinateCLM coordinate
        (vectorTest.1 space)).im = 0
      rw [vectorZero]
      rfl
  · by_cases realPart : component = 0
    · simp only [scalarCoordinate, if_pos realPart]
      exact Complex.reCLM.contDiff.comp
        ((canonicalInteriorTestCoordinateCLM coordinate).contDiff.comp
          vectorTest.property.2)
    · simp only [scalarCoordinate, if_neg realPart]
      exact Complex.imCLM.contDiff.comp
        ((canonicalInteriorTestCoordinateCLM coordinate).contDiff.comp
          vectorTest.property.2)
  · intro space outside
    have vectorZero :=
      cauchySafeMatterCanonicalInteriorDenseTest_zero_of_not_interior
        a b test space outside
    change vectorTest.1 space = 0 at vectorZero
    by_cases realPart : component = 0
    · rw [show scalarCoordinate = Complex.re ∘ complexCoordinate by
        simp [scalarCoordinate, realPart]]
      change (canonicalInteriorTestCoordinateCLM coordinate
        (vectorTest.1 space)).re = 0
      rw [vectorZero]
      rfl
    · rw [show scalarCoordinate = Complex.im ∘ complexCoordinate by
        simp [scalarCoordinate, realPart]]
      change (canonicalInteriorTestCoordinateCLM coordinate
        (vectorTest.1 space)).im = 0
      rw [vectorZero]
      rfl

@[simp] theorem cauchySafeMatterCanonicalInteriorScalarGenerator_zero
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (coordinate : MatterCoordinateIndex)
    (space : DiracMatterSpatialCoordinates) :
    (cauchySafeMatterCanonicalInteriorScalarGenerator
      a b test coordinate 0).1 space =
      ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1
        space coordinate).re := by
  rfl

@[simp] theorem cauchySafeMatterCanonicalInteriorScalarGenerator_one
    (a b : DiracMatterSpatialCoordinates)
    (test : ℕ)
    (coordinate : MatterCoordinateIndex)
    (space : DiracMatterSpatialCoordinates) :
    (cauchySafeMatterCanonicalInteriorScalarGenerator
      a b test coordinate 1).1 space =
      ((cauchySafeMatterCanonicalInteriorDenseTest a b test).1
        space coordinate).im := by
  rfl

/-- The scalar finite element space generated by the first `testCount`
interior vector tests, with all matter coordinates and real/imaginary parts
included before linear dependencies are removed. -/
def cauchySafeMatterCanonicalInteriorScalarPrefixSpace
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Submodule ℝ (cauchySafeMatterCanonicalInteriorScalarTestSubmodule a b) :=
  Submodule.span ℝ (Set.range fun index :
      Fin testCount × MatterCoordinateIndex × Fin 2 ↦
    cauchySafeMatterCanonicalInteriorScalarGenerator a b
      index.1 index.2.1 index.2.2)

/-- Increasing the test prefix only enlarges the generated scalar space. -/
theorem cauchySafeMatterCanonicalInteriorScalarPrefixSpace_mono
    (a b : DiracMatterSpatialCoordinates)
    {firstCount secondCount : ℕ}
    (countMonotone : firstCount ≤ secondCount) :
    cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b firstCount ≤
      cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b secondCount := by
  apply Submodule.span_mono
  rintro _ ⟨index, rfl⟩
  exact ⟨(Fin.castLE countMonotone index.1, index.2), rfl⟩

local instance canonicalInteriorScalarPrefixFiniteDimensional
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    FiniteDimensional ℝ
      (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

abbrev CauchySafeMatterCanonicalInteriorScalarPrefixBasisIndex
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :=
  Module.Basis.ofVectorSpaceIndex ℝ
    (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount)

local instance canonicalInteriorScalarPrefixBasisIndexFinite
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Finite
      (CauchySafeMatterCanonicalInteriorScalarPrefixBasisIndex
        a b testCount) :=
  Module.Finite.finite_basis
    (Module.Basis.ofVectorSpace ℝ
      (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount))

local instance canonicalInteriorScalarPrefixBasisIndexFintype
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Fintype
      (CauchySafeMatterCanonicalInteriorScalarPrefixBasisIndex
        a b testCount) :=
  Fintype.ofFinite _

def cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) : ℕ :=
  Fintype.card
    (CauchySafeMatterCanonicalInteriorScalarPrefixBasisIndex
      a b testCount)

/-- The redundancy-free finite scalar basis selected from the exact prefix
span.  Its index size is the actual rank, not the raw generator count. -/
def cauchySafeMatterCanonicalInteriorScalarPrefixBasis
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Module.Basis
      (Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount))
      ℝ
      (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount) :=
  (Module.Basis.ofVectorSpace ℝ
      (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount)).reindex
    (Fintype.equivFin
      (CauchySafeMatterCanonicalInteriorScalarPrefixBasisIndex
        a b testCount))

/-- The scalar functions supplied to the finite Galerkin action. -/
def cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) →
      DiracMatterSpatialCoordinates → ℝ :=
  fun mode ↦
    (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
      a b testCount mode).1.1

theorem cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_regular
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (mode : Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
      a b testCount)) :
    ContDiff ℝ 1
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount mode) :=
  ((cauchySafeMatterCanonicalInteriorScalarPrefixBasis
    a b testCount mode).1.2.2.1).of_le (by norm_num)

theorem cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_compact
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (mode : Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
      a b testCount)) :
    HasCompactSupport
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount mode) :=
  (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
    a b testCount mode).1.2.1

theorem cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_zeroOutside
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (mode : Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
      a b testCount))
    (space : DiracMatterSpatialCoordinates)
    (outside : ¬ DiracMatterSpatialBoxInterior a b space) :
    cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount mode space = 0 :=
  (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
    a b testCount mode).1.2.2.2 space outside

/-- Removing dependencies in the prefix span gives a genuinely linearly
independent family of scalar functions. -/
theorem cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_linearIndependent
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ) :
    LinearIndependent ℝ
      (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount) := by
  let inclusion :
      cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount →ₗ[ℝ]
        (DiracMatterSpatialCoordinates → ℝ) :=
    (Submodule.subtype
      (cauchySafeMatterCanonicalInteriorScalarTestSubmodule a b)).comp
      (Submodule.subtype
        (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount))
  have inclusionInjective : Function.Injective inclusion := by
    intro first second equalFunctions
    apply Subtype.ext
    apply Subtype.ext
    simpa only [inclusion, LinearMap.comp_apply,
      Submodule.subtype_apply] using equalFunctions
  have transported : LinearIndependent ℝ
      (inclusion ∘
        cauchySafeMatterCanonicalInteriorScalarPrefixBasis
          a b testCount) :=
    (inclusion.linearIndependent_iff_of_injOn
      inclusionInjective.injOn).2
      (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
        a b testCount).linearIndependent
  have familyEq :
      (inclusion ∘
        cauchySafeMatterCanonicalInteriorScalarPrefixBasis a b testCount) =
      cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
        a b testCount := by
    funext mode
    rfl
  rwa [familyEq] at transported

/-- Each scalar coordinate generator among the first `testCount` tests is a
literal member of the generated prefix space. -/
def cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : Fin testCount)
    (coordinate : MatterCoordinateIndex)
    (component : Fin 2) :
    cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount :=
  ⟨cauchySafeMatterCanonicalInteriorScalarGenerator a b
      test.1 coordinate component,
    Submodule.subset_span
      (Set.mem_range_self (test, (coordinate, component)))⟩

/-- The redundancy-free basis still reconstructs every raw scalar generator
in its prefix exactly. -/
theorem cauchySafeMatterCanonicalInteriorScalarGenerator_sum_repr
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : Fin testCount)
    (coordinate : MatterCoordinateIndex)
    (component : Fin 2)
    (space : DiracMatterSpatialCoordinates) :
    ∑ mode,
        (cauchySafeMatterCanonicalInteriorScalarPrefixBasis a b testCount).repr
            (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
              a b testCount test coordinate component) mode *
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount mode space =
      (cauchySafeMatterCanonicalInteriorScalarGenerator
        a b test.1 coordinate component).1 space := by
  have expansion :=
    (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
      a b testCount).sum_repr
      (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
        a b testCount test coordinate component)
  let inclusion :
      cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount →ₗ[ℝ]
        (DiracMatterSpatialCoordinates → ℝ) :=
    (Submodule.subtype
      (cauchySafeMatterCanonicalInteriorScalarTestSubmodule a b)).comp
      (Submodule.subtype
        (cauchySafeMatterCanonicalInteriorScalarPrefixSpace a b testCount))
  have functions :
      ∑ mode,
          (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
              a b testCount).repr
              (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
                a b testCount test coordinate component) mode •
            (cauchySafeMatterCanonicalInteriorScalarPrefixBasis
              a b testCount mode).1.1 =
        (cauchySafeMatterCanonicalInteriorScalarGenerator
          a b test.1 coordinate component).1 := by
    simpa only [map_sum, map_smul, inclusion, LinearMap.comp_apply,
      Submodule.subtype_apply,
      cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix] using
      congrArg inclusion expansion
  have evaluated := congrFun functions space
  simpa only [cauchySafeMatterCanonicalInteriorScalarGalerkinBasis,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using evaluated

/-- Canonical finite coefficient which reconstructs one generated vector test
from the redundancy-free real scalar basis. -/
def cauchySafeMatterCanonicalInteriorTestCoefficient
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : Fin testCount) :
    DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) :=
  WithLp.toLp 2 fun index ↦
    ((cauchySafeMatterCanonicalInteriorScalarPrefixBasis
        a b testCount).repr
      (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
        a b testCount test index.2 0) index.1 : ℂ) +
    Complex.I *
      ((cauchySafeMatterCanonicalInteriorScalarPrefixBasis
          a b testCount).repr
        (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
          a b testCount test index.2 1) index.1 : ℂ)

@[simp] theorem cauchySafeMatterCanonicalInteriorTestCoefficient_mode_apply
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : Fin testCount)
    (mode : Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
      a b testCount))
    (coordinate : MatterCoordinateIndex) :
    diracMatterGalerkinCoefficientMode
        (cauchySafeMatterCanonicalInteriorTestCoefficient
          a b testCount test) mode coordinate =
      ((cauchySafeMatterCanonicalInteriorScalarPrefixBasis
          a b testCount).repr
        (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
          a b testCount test coordinate 0) mode : ℂ) +
      Complex.I *
        ((cauchySafeMatterCanonicalInteriorScalarPrefixBasis
            a b testCount).repr
          (cauchySafeMatterCanonicalInteriorScalarGeneratorInPrefix
            a b testCount test coordinate 1) mode : ℂ) := by
  rfl

/-- Every generated interior vector test is represented exactly from its
entry prefix onward. -/
theorem cauchySafeMatterCanonicalInteriorTest_representation
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (test : Fin testCount)
    (space : DiracMatterSpatialCoordinates) :
    matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          (cauchySafeMatterCanonicalInteriorTestCoefficient
            a b testCount test)
          space) =
      (cauchySafeMatterCanonicalInteriorDenseTest a b test.1).1 space := by
  rw [diracMatterSpatialGalerkinSynthesis_coordinates]
  ext coordinate
  apply Complex.ext
  · simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply]
    change
      Complex.reCLM (∑ mode,
        cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount mode space •
          diracMatterGalerkinCoefficientMode
            (cauchySafeMatterCanonicalInteriorTestCoefficient
              a b testCount test) mode coordinate) =
        Complex.reCLM ((cauchySafeMatterCanonicalInteriorDenseTest
          a b test.1).1 space coordinate)
    rw [map_sum]
    simp only [
      cauchySafeMatterCanonicalInteriorTestCoefficient_mode_apply,
      Complex.reCLM_apply, Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, zero_mul, sub_zero, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero]
    simpa only [mul_comm,
      cauchySafeMatterCanonicalInteriorScalarGenerator_zero] using
      cauchySafeMatterCanonicalInteriorScalarGenerator_sum_repr
        a b testCount test coordinate 0 space
  · simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply]
    change
      Complex.imCLM (∑ mode,
        cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount mode space •
          diracMatterGalerkinCoefficientMode
            (cauchySafeMatterCanonicalInteriorTestCoefficient
              a b testCount test) mode coordinate) =
        Complex.imCLM ((cauchySafeMatterCanonicalInteriorDenseTest
          a b test.1).1 space coordinate)
    rw [map_sum]
    simp only [
      cauchySafeMatterCanonicalInteriorTestCoefficient_mode_apply,
      Complex.imCLM_apply, Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, zero_mul, one_mul, zero_add, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero]
    simpa only [mul_comm,
      cauchySafeMatterCanonicalInteriorScalarGenerator_one] using
      cauchySafeMatterCanonicalInteriorScalarGenerator_sum_repr
        a b testCount test coordinate 1 space

/-- The exact entry stage of the `test`-th canonical interior test. -/
def cauchySafeMatterCanonicalInteriorTestEntry (test : ℕ) : ℕ :=
  test + 1

/-- From its canonical entry stage onward, every generated interior test has
an exact coefficient in the finite action carrier. -/
theorem cauchySafeMatterCanonicalInteriorTest_eventualRepresentation
    (a b : DiracMatterSpatialCoordinates)
    (testCount test : ℕ)
    (entered :
      cauchySafeMatterCanonicalInteriorTestEntry test ≤ testCount) :
    ∃ coefficient : DiracMatterGalerkinCoefficient
        (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
          a b testCount),
      ∀ space,
        matterCoordinateEquiv
            (diracMatterSpatialGalerkinSynthesis
              (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount)
              coefficient
              space) =
          (cauchySafeMatterCanonicalInteriorDenseTest a b test).1 space := by
  let testIndex : Fin testCount :=
    ⟨test, lt_of_lt_of_le (Nat.lt_succ_self test) entered⟩
  refine ⟨cauchySafeMatterCanonicalInteriorTestCoefficient
      a b testCount testIndex, ?_⟩
  intro space
  simpa only [testIndex] using
    cauchySafeMatterCanonicalInteriorTest_representation
      a b testCount testIndex space

/-- The canonical scalar prefix basis is faithful for the complex
matter-coordinate coefficient carrier used by the finite action. -/
theorem cauchySafeMatterCanonicalInteriorScalarGalerkinSynthesis_faithful
    (a b : DiracMatterSpatialCoordinates)
    (testCount : ℕ)
    (coefficient : DiracMatterGalerkinCoefficient
      (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount))
    (coefficientNonzero : coefficient ≠ 0) :
    ∃ space,
      diracMatterSpatialGalerkinSynthesis
          (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount)
          coefficient space ≠ 0 := by
  by_contra noWitness
  push Not at noWitness
  apply coefficientNonzero
  ext index
  let coordinate := index.2
  let realCoefficient :
      Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) → ℝ := fun mode ↦
    (diracMatterGalerkinCoefficientMode coefficient mode coordinate).re
  let imaginaryCoefficient :
      Fin (cauchySafeMatterCanonicalInteriorScalarPrefixModeCount
        a b testCount) → ℝ := fun mode ↦
    (diracMatterGalerkinCoefficientMode coefficient mode coordinate).im
  have coordinateRelation : ∀ space,
      ∑ mode,
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount mode space •
            diracMatterGalerkinCoefficientMode coefficient mode coordinate =
        0 := by
    intro space
    have mapped := congrArg matterCoordinateEquiv (noWitness space)
    rw [diracMatterSpatialGalerkinSynthesis_coordinates] at mapped
    have underlying := congrArg WithLp.ofLp mapped
    have projected := congrFun underlying coordinate
    simpa only [map_zero, WithLp.ofLp_zero, WithLp.ofLp_sum, WithLp.ofLp_smul,
      Finset.sum_apply, Pi.smul_apply, Pi.zero_apply] using projected
  have realRelation :
      ∑ mode, realCoefficient mode •
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount mode = 0 := by
    funext space
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    have relation := coordinateRelation space
    have realRelationAt := congrArg Complex.re relation
    change Complex.reCLM
        (∑ mode,
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount mode space •
            diracMatterGalerkinCoefficientMode coefficient mode coordinate) =
      0 at realRelationAt
    rw [map_sum] at realRelationAt
    have normalForm :
        ∑ mode,
            cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount mode space * realCoefficient mode = 0 := by
      simpa only [realCoefficient, Complex.reCLM_apply, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, sub_zero] using realRelationAt
    calc
      _ = ∑ mode,
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount mode space * realCoefficient mode := by
        apply Finset.sum_congr rfl
        intro mode _
        exact mul_comm _ _
      _ = 0 := normalForm
  have imaginaryRelation :
      ∑ mode, imaginaryCoefficient mode •
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
            a b testCount mode = 0 := by
    funext space
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    have relation := coordinateRelation space
    have imaginaryRelationAt := congrArg Complex.im relation
    change Complex.imCLM
        (∑ mode,
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount mode space •
            diracMatterGalerkinCoefficientMode coefficient mode coordinate) =
      0 at imaginaryRelationAt
    rw [map_sum] at imaginaryRelationAt
    have normalForm :
        ∑ mode,
            cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
                a b testCount mode space * imaginaryCoefficient mode = 0 := by
      simpa only [imaginaryCoefficient, Complex.imCLM_apply,
        Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using imaginaryRelationAt
    calc
      _ = ∑ mode,
          cauchySafeMatterCanonicalInteriorScalarGalerkinBasis
              a b testCount mode space * imaginaryCoefficient mode := by
        apply Finset.sum_congr rfl
        intro mode _
        exact mul_comm _ _
      _ = 0 := normalForm
  have realZero := Fintype.linearIndependent_iff.mp
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_linearIndependent
      a b testCount) realCoefficient realRelation
  have imaginaryZero := Fintype.linearIndependent_iff.mp
    (cauchySafeMatterCanonicalInteriorScalarGalerkinBasis_linearIndependent
      a b testCount) imaginaryCoefficient imaginaryRelation
  change diracMatterGalerkinCoefficientMode coefficient index.1 index.2 = 0
  apply Complex.ext
  · exact realZero index.1
  · exact imaginaryZero index.1

end

end SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterCanonicalGalerkinBasis
