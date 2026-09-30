import H0mework.Physics.Dirac.DiracMatterSpatialEnergyBalance
import H0mework.Physics.Holonomic.HolonomicField
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Cauchy-safe spatial L² test carrier

Smooth compactly supported matter tests embed densely into the physical
spatial `L²` carrier on every fixed box.  This is the source-owned dense test
mouth consumed by generated weak-limit actualization.
-/

namespace SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterSpatialL2TestCarrier

open MeasureTheory Set
open StageNineDiracMatterSpatialEnergyBalance
open StageNineHolonomicField
open scoped ContDiff

noncomputable section

set_option autoImplicit false

/-- Matter fields on one fixed spatial box, completed in the physical
`L²` norm. -/
abbrev CauchySafeMatterSpatialL2
    (a b : DiracMatterSpatialCoordinates) :=
  Lp MatterCoordinateCarrier 2 (volume.restrict (Icc a b))

/-- Smooth compactly supported matter tests before `L²` completion. -/
def cauchySafeMatterSmoothCompactTestSubmodule :
    Submodule ℝ
      (DiracMatterSpatialCoordinates → MatterCoordinateCarrier) where
  carrier test := HasCompactSupport test ∧ ContDiff ℝ ∞ test
  zero_mem' := ⟨HasCompactSupport.zero, contDiff_const⟩
  add_mem' := by
    intro first second firstMem secondMem
    exact ⟨HasCompactSupport.add firstMem.1 secondMem.1,
      firstMem.2.add secondMem.2⟩
  smul_mem' := by
    intro parameter test testMem
    exact ⟨testMem.1.smul_left, testMem.2.const_smul parameter⟩

abbrev CauchySafeMatterSmoothCompactTest :=
  cauchySafeMatterSmoothCompactTestSubmodule

theorem cauchySafeMatterSmoothCompactTest_memLp
    (a b : DiracMatterSpatialCoordinates)
    (test : CauchySafeMatterSmoothCompactTest) :
    MemLp (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) 2
      (volume.restrict (Icc a b)) := by
  have testMem := test.property
  change HasCompactSupport
      (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) ∧
    ContDiff ℝ ∞
      (test : DiracMatterSpatialCoordinates → MatterCoordinateCarrier) at testMem
  exact testMem.2.continuous.memLp_of_hasCompactSupport testMem.1

/-- The generated smooth test carrier embeds linearly into the spatial
`L²` carrier. -/
def cauchySafeMatterSmoothCompactTestToL2
    (a b : DiracMatterSpatialCoordinates) :
    CauchySafeMatterSmoothCompactTest →ₗ[ℝ]
      CauchySafeMatterSpatialL2 a b where
  toFun test :=
    (cauchySafeMatterSmoothCompactTest_memLp a b test).toLp test
  map_add' first second := by
    simpa using MemLp.toLp_add
      (cauchySafeMatterSmoothCompactTest_memLp a b first)
      (cauchySafeMatterSmoothCompactTest_memLp a b second)
  map_smul' parameter test := by
    simpa using MemLp.toLp_const_smul parameter
      (cauchySafeMatterSmoothCompactTest_memLp a b test)

/-- Smooth compact tests are dense in the physical spatial `L²` carrier. -/
theorem cauchySafeMatterSmoothCompactTestToL2_denseRange
    (a b : DiracMatterSpatialCoordinates) :
    DenseRange (cauchySafeMatterSmoothCompactTestToL2 a b) := by
  apply (Lp.dense_hasCompactSupport_contDiff
    (F := MatterCoordinateCarrier)
    (μ := volume.restrict (Icc a b)) (p := 2) (by norm_num)).mono
  intro field fieldMem
  rcases fieldMem with ⟨representative, fieldEq, compact, smooth⟩
  let test : CauchySafeMatterSmoothCompactTest := by
    refine ⟨representative, ?_⟩
    change HasCompactSupport representative ∧ ContDiff ℝ ∞ representative
    exact ⟨compact, smooth⟩
  refine ⟨test, ?_⟩
  apply Lp.ext
  exact (cauchySafeMatterSmoothCompactTest_memLp a b test).coeFn_toLp.trans
    fieldEq.symm

end

end SaturationMonoid.PhysicsCore.StageNineCauchySafeMatterSpatialL2TestCarrier
