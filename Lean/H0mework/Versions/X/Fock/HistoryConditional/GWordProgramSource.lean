import H0mework.Versions.X.Fock.HistoryConditional.WordOperatorConsumer
import H0mework.Versions.X.Fock.CopyGraph.Action

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordProgram

open SourceOwnedObservationHistory.SourceShift SourceSuccessorBoundary
open scoped InnerProductSpace
noncomputable section

theorem index_exact (program : Nat × Nat) (positive : 0 < program.1) (coordinate : Nat) :
    SourceCopyWordAffine.execute program coordinate + 1 = program.1 * (coordinate + 1) + program.2 := by
  have product : 0 < program.1 * (coordinate + 1) := Nat.mul_pos positive (Nat.succ_pos coordinate)
  exact Nat.sub_add_cancel (by omega)

theorem index_injective (program : Nat × Nat) (positive : 0 < program.1) :
    Function.Injective (SourceCopyWordAffine.execute program) := by
  intro left right same
  have source := congrArg (fun coordinate => coordinate + 1) same
  rw [index_exact program positive, index_exact program positive] at source
  exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left positive (Nat.add_right_cancel source))

theorem orthogonal (program : Nat × Nat) (positive : 0 < program.1) :
    OrthogonalFamily ℂ (fun _ : Nat => ℂ) (fun coordinate => place (SourceCopyWordAffine.execute program coordinate)) := by
  intro left right distinct a b
  change ⟪lp.single (E := fun _ : Nat => ℂ) 2 (SourceCopyWordAffine.execute program left) a,
    lp.single (E := fun _ : Nat => ℂ) 2 (SourceCopyWordAffine.execute program right) b⟫_ℂ = 0
  rw [lp.inner_single_left]
  have separate : SourceCopyWordAffine.execute program left ≠ SourceCopyWordAffine.execute program right :=
    fun same => distinct (index_injective program positive same)
  simp [lp.single_apply, separate]

def complexAction (program : Nat × Nat) : (Nat →₀ ℂ) →ₗ[ℂ] Nat →₀ ℂ :=
  Finsupp.lmapDomain ℂ ℂ (SourceCopyWordAffine.execute program)

def hilbertAction (program : Nat × Nat) (positive : 0 < program.1) : H →ₗᵢ[ℂ] H :=
  (orthogonal program positive).linearIsometry

def jointAction (program : Nat × Nat) (positive : 0 < program.1) : SourceMassCompletion.Joint →L[ℂ] SourceMassCompletion.Joint :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ H ℂ).symm.toContinuousLinearMap.comp
    (((hilbertAction program positive).toContinuousLinearMap.comp SourceMassCompletion.firstRead).prod SourceMassCompletion.massRead)

def action (program : Nat × Nat) (positive : 0 < program.1) : SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ SourceMassCompletion.Joint ℂ).symm.toContinuousLinearMap.comp
    (((jointAction program positive).comp SourceJointClockGraph.joint).prod
      ((program.1 : ℂ) • SourceJointClockGraph.clock +
        (program.2 : ℂ) • (SourceMassCompletion.massRead.comp SourceJointClockGraph.joint)))

theorem hilbert_single (program : Nat × Nat) (positive : 0 < program.1) (coordinate : Nat) (scalar : ℂ) :
    hilbertAction program positive (lp.single 2 coordinate scalar) =
      lp.single 2 (SourceCopyWordAffine.execute program coordinate) scalar :=
  (orthogonal program positive).linearIsometry_apply_single scalar

theorem hilbert_source (program : Nat × Nat) (positive : 0 < program.1) (source : Nat →₀ ℂ) :
    hilbertAction program positive (readWord source) = readWord (complexAction program source) := by
  change (hilbertAction program positive).toLinearMap (Finsupp.linearCombination ℂ basis source) =
    Finsupp.linearCombination ℂ basis (Finsupp.mapDomain (SourceCopyWordAffine.execute program) source)
  rw [Finsupp.apply_linearCombination, Finsupp.linearCombination_mapDomain]
  congr 1
  exact congrArg (Finsupp.linearCombination ℂ) (funext fun coordinate => hilbert_single program positive coordinate 1)

end
end SourceGWordProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
