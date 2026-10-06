import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.GaussFullHamiltonian

/-! The actual weighted Yukawa operator consumes the original full occupation grade. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.GaussYukawaGrade
open SaturationMonoid.PhysicsCore
open DiracExteriorMatterAction DiracCliffordRepresentation StageNineDynamicBreakingVacuum
open StageNineDiracDualYukawaSpinJurisdiction
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussYukawaCoefficient GaussYukawaOperator GaussCoreHilbert GaussCoreDifferential
open GaussQuantumMultiplier GaussFockLabel GaussCoreLabel NativeHistoryGrade
open QuantizationCheck.Fermion
open scoped ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance labelFintype : Fintype Label := Fintype.ofFinite _
local instance : DecidableEq LowEnergy.Quantum.Index := Classical.decEq _

set_option backward.isDefEq.respectTransparency false in
theorem matrix_raises (phi : Scalar) (i j : Mode) :
    ((if i ∈ target then 1 else 0 : ℂ)-(if j ∈ target then 1 else 0 : ℂ)-1) * fullMatrix phi i j = 0 := by
  have hbase := yukawa_mother_grade diracGammaZero (scalarCoordinateEquiv.symm phi)
  have hmother : LowEnergy.MixedSymbol.degreeSix * LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi) =
      LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi) * LowEnergy.MixedSymbol.degreeSix +
        (1 : ℂ) • LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi) := by
    unfold LowEnergy.FullQuantum.yukawaHamiltonian
    change LowEnergy.MixedSymbol.degreeSix * ((Stage9C.Material.SpinPair.lapse : ℂ) •
      (diracMatrixMatterAction diracGammaZero * diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm phi))) = _
    rw [mul_smul_comm, hbase, smul_add, smul_mul_assoc]
    simp only [one_smul, Module.End.mul_eq_comp]
  have h := branches_grade _ 1 (matrix_grade _ 1 (by simpa only [Nat.cast_one] using hmother)) i j
  have he : fullMatrix phi = SourceRealScalarFock.branches (LowEnergy.Quantum.operatorMatrix
      (LowEnergy.FullQuantum.yukawaHamiltonian (scalarCoordinateEquiv.symm phi))) := rfl
  rw [he]
  simpa only [Nat.cast_one] using h

theorem raw_grade (phi : Scalar) :
    SourceFockRaising.grade target * LowEnergy.Fermion.quantize (fullMatrix phi) =
      LowEnergy.Fermion.quantize (fullMatrix phi) * SourceFockRaising.grade target +
        LowEnergy.Fermion.quantize (fullMatrix phi) :=
  by
    apply SourceFockRaising.quantize_raises_grade
    intro i j
    have h := matrix_raises phi i j
    by_cases hi : i ∈ target <;> by_cases hj : j ∈ target <;>
      simpa only [hi, hj, if_true, if_false] using h

def fiberGrade : FockFiber →L[ℂ] FockFiber := blockWeight (fun g => (g.2.val : ℂ))

theorem fiber_coordinates_grade (f : FockFiber) :
    fiberCoordinates (fiberGrade f) = SourceFockRaising.grade target (fiberCoordinates f) := by
  funext word
  rw [SourceFockRaising.grade_apply]
  rfl

theorem fiber_source_grade (phi : Scalar) (f : FockFiber) :
    fiberGrade (sourceMap phi f) = sourceMap phi (fiberGrade f) + sourceMap phi f := by
  apply fiberCoordinates.injective
  rw [fiber_coordinates_grade, map_add]
  have h : ∀ f, fiberCoordinates (sourceMap phi f) = LowEnergy.Fermion.quantize (fullMatrix phi) (fiberCoordinates f) :=
    fun _ => rfl
  rw [h, h, fiber_coordinates_grade]
  exact LinearMap.congr_fun (raw_grade phi) (fiberCoordinates f)

def gradeCore : QuantumTest →ₗ[ℂ] QuantumTest := (TestFunction.postcompCLM fiberGrade).toLinearMap
def grade : H →L[ℂ] H := ∑ g : Label, (g.2.val : ℂ) • projection g

theorem gradeCore_resolution (f : QuantumTest) : gradeCore f = ∑ g : Label, (g.2.val : ℂ) • project g f := by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change fiberGrade (f z) word = _
  simp [fiberGrade, blockWeight_apply, project_apply, fiberPiece_apply,
    WithLp.ofLp_sum, Finset.sum_apply, eq_comm]

theorem grade_core (f : QuantumTest) : grade (embed f) = embed (gradeCore f) := by
  rw [gradeCore_resolution]
  simp only [grade, sum_apply, smul_apply, map_sum, map_smul, embed_project]

theorem normalized_core_grade (f : QuantumTest) :
    gradeCore (GaussYukawaCoefficient.action f) =
      GaussYukawaCoefficient.action (gradeCore f) + GaussYukawaCoefficient.action f := by
  apply DFunLike.ext
  intro z
  exact fiber_source_grade (normalizedScalar z) (f z)

theorem bounded_raises : grade * bounded = bounded * grade + bounded := by
  apply ContinuousLinearMap.ext
  intro x
  change grade (bounded x) = bounded (grade x) + bounded x
  refine GaussBoundedMultiplier.core_dense.induction_on x
    (isClosed_eq (grade.continuous.comp bounded.continuous)
      ((bounded.continuous.comp grade.continuous).add bounded.continuous)) ?_
  intro v
  obtain ⟨f,rfl⟩ := coreEquiv.surjective v
  change grade (bounded (embed f)) = bounded (grade (embed f)) + bounded (embed f)
  rw [bounded_core, grade_core, grade_core, bounded_core, normalized_core_grade, map_add]

theorem core_ext (A B : H →L[ℂ] H) (h : ∀ f : QuantumTest, A (embed f)=B (embed f)) : A=B := by
  apply ContinuousLinearMap.ext
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_eq A.continuous B.continuous) ?_
  intro v
  obtain ⟨f,rfl⟩ := coreEquiv.surjective v
  exact h f

theorem inverse_blocks (g : Label) : projection g * GaussRadialDomain.inverseRadius =
    GaussRadialDomain.inverseRadius * projection g := by
  apply core_ext
  intro f
  change projection g (GaussRadialDomain.inverseRadius (embed f)) =
    GaussRadialDomain.inverseRadius (projection g (embed f))
  rw [GaussRadialDomain.inverse_core, ← embed_project, ← embed_project, GaussRadialDomain.inverse_core]
  exact congrArg embed (commutes_real g GaussRadialDomain.reciprocal
    (fun _ => GaussRadialDomain.reciprocal_smooth.contDiffAt) f)

theorem inverse_grade : grade * GaussRadialDomain.inverseRadius =
    GaussRadialDomain.inverseRadius * grade := by
  simp only [grade, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, inverse_blocks]

theorem closed_graph_grade (x : GaussRadialDomain.closedY.domain) :
    (grade (x : H), grade (GaussRadialDomain.closedY x)-GaussRadialDomain.closedY x) ∈
      GaussRadialDomain.closedY.graph := by
  have hx := GaussRadialDomain.closedY.mem_graph x
  rw [GaussRadialDomain.closedY_graph] at hx ⊢
  change bounded (x : H) = GaussRadialDomain.inverseRadius (GaussRadialDomain.closedY x) at hx
  change bounded (grade (x : H)) =
    GaussRadialDomain.inverseRadius (grade (GaussRadialDomain.closedY x)-GaussRadialDomain.closedY x)
  have hb := congrArg (fun A : H →L[ℂ] H => A (x : H)) bounded_raises
  change grade (bounded (x : H)) = bounded (grade (x : H)) + bounded (x : H) at hb
  have hs := congrArg (fun A : H →L[ℂ] H => A (GaussRadialDomain.closedY x)) inverse_grade
  change grade (GaussRadialDomain.inverseRadius (GaussRadialDomain.closedY x)) =
    GaussRadialDomain.inverseRadius (grade (GaussRadialDomain.closedY x)) at hs
  calc
    _ = grade (bounded (x : H))-bounded (x : H) := by rw [hb]; abel
    _ = _ := by rw [hx, hs, map_sub]

#print axioms matrix_raises
#print axioms fiber_source_grade
#print axioms grade_core
#print axioms bounded_raises
#print axioms inverse_blocks
#print axioms closed_graph_grade
end LowEnergy.GaussYukawaGrade
