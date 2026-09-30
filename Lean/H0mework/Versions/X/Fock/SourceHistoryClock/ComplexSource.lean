import H0mework.Versions.X.Fock.PrimeFieldJoint.TimeConsumer
import H0mework.Versions.X.Fock.PrimeField.ClockSplittingConsumer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceClockComplex

open SourceSuccessorBoundary
noncomputable section

def ofNative : (Nat →₀ ℤ) →ₗ[ℤ] Nat →₀ ℂ :=
  Finsupp.linearCombination ℤ fun index => Finsupp.single index (1 : ℂ)

def clock : (Nat →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ fun index => (SourceClockModel.rawClock index : ℂ)

theorem ofNative_single (index : Nat) (scalar : ℤ) :
    ofNative (Finsupp.single index scalar) = Finsupp.single index (scalar : ℂ) := by
  simp [ofNative]

theorem clock_single (index : Nat) (scalar : ℂ) :
    clock (Finsupp.single index scalar) = scalar * (SourceClockModel.rawClock index : ℂ) :=
  Finsupp.linearCombination_single _ _ _

theorem clock_native (word : Nat →₀ ℤ) :
    clock (ofNative word) = (SourceClockModel.clock word : ℂ) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero previous =>
      simp only [map_add, Int.cast_add, previous, ofNative_single, clock_single,
        SourceClockModel.clock_single, Int.cast_mul]
      simp only [SourceClockModel.rawClock, Int.cast_add]

theorem joint_native (word : Nat →₀ ℤ) :
    SourceMassCompletion.jointRead (ofNative word) = SourceMassCompletion.nativeRead word := by
  change (SourceMassCompletion.jointRead.restrictScalars ℤ)
    (Finsupp.linearCombination ℤ (fun index => Finsupp.single index (1 : ℂ)) word) = _
  rw [Finsupp.apply_linearCombination]
  rfl

theorem native_increment (index : Nat) :
    (SourceClockModel.rawClock (index + 1) : ℂ) = (SourceClockModel.rawClock index : ℂ) + 1 := by
  have actual := SourceClockModel.clock_push (Finsupp.single index 1)
  simp only [push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    SourceClockModel.clock_single, mass_single, one_mul] at actual
  have same : SourceClockModel.rawClock (index + 1) = SourceClockModel.rawClock index + 1 := by
    simpa only [SourceClockModel.rawClock] using actual
  simpa only [Int.cast_add, Int.cast_one] using congrArg (fun value : ℤ => (value : ℂ)) same

theorem clock_push (word : Nat →₀ ℂ) :
    clock (push ℂ word) = clock word + mass ℂ word := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero previous =>
      simp only [map_add, previous]
      have single : clock (push ℂ (Finsupp.single index scalar)) =
          clock (Finsupp.single index scalar) + mass ℂ (Finsupp.single index scalar) := by
        simp only [push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
          clock_single, native_increment, mass_single, mul_add, mul_one]
      rw [single]
      abel

theorem model_source (word : Nat →₀ ℤ) :
    clock (ofNative word) = (SourceClockModel.clockRead (SourceClockModel.projection word) : ℂ) := by
  rw [clock_native, SourceClockModel.clockRead_source]

theorem mass_native (word : Nat →₀ ℤ) :
    mass ℂ (ofNative word) = (SourceClockModel.massRead (SourceClockModel.projection word) : ℂ) := by
  rw [SourceClockModel.massRead_source]
  exact (SourceMassCompletion.massRead_source (ofNative word)).symm.trans
    ((congrArg SourceMassCompletion.massRead (joint_native word)).trans
      (SourceMassCompletion.massRead_native word))

end
end SourceClockComplex
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
