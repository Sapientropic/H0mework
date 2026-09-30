import H0mework.Versions.X.Fock.HistoryPolynomial.CopySource
import H0mework.Versions.X.Fock.SourceHistoryClock.ComplexSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceCopyGraph

open SourceCopyProgram SourceSuccessorBoundary
noncomputable section

def complexAction (depth : Nat) (index : Index depth) : (Nat →₀ ℂ) →ₗ[ℂ] Nat →₀ ℂ :=
  Finsupp.lmapDomain ℂ ℂ (indexAfter depth index)

theorem complex_single (depth : Nat) (index : Index depth) (coordinate : Nat) (scalar : ℂ) :
    complexAction depth index (Finsupp.single coordinate scalar) = Finsupp.single (indexAfter depth index coordinate) scalar :=
  Finsupp.mapDomain_single

theorem complex_native (depth : Nat) (index : Index depth) (word : Nat →₀ ℤ) :
    SourceClockComplex.ofNative (SourceCopyProgram.action depth index word) =
      complexAction depth index (SourceClockComplex.ofNative word) := by
  change Finsupp.linearCombination ℤ (fun coordinate => Finsupp.single coordinate (1 : ℂ))
      (Finsupp.mapDomain (indexAfter depth index) word) =
    ((complexAction depth index).restrictScalars ℤ)
      (Finsupp.linearCombination ℤ (fun coordinate => Finsupp.single coordinate (1 : ℂ)) word)
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  congr 1
  apply congrArg (Finsupp.linearCombination ℤ)
  funext coordinate
  exact (complex_single depth index coordinate 1).symm

theorem mass_copy (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    mass ℂ (complexAction depth index word) = mass ℂ word := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add coordinate scalar word _ _ previous =>
      simp only [map_add, complex_single, mass_single, previous]

theorem clock_index (depth : Nat) (index : Index depth) (coordinate : Nat) :
    (SourceClockModel.rawClock (indexAfter depth index coordinate) : ℂ) =
      (scale depth index : ℂ) * (SourceClockModel.rawClock coordinate : ℂ) := by
  simp only [SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one]
  have source := (index_exact depth index coordinate).trans (Nat.mul_comm (coordinate + 1) (scale depth index))
  exact_mod_cast source

theorem clock_copy (depth : Nat) (index : Index depth) (word : Nat →₀ ℂ) :
    SourceClockComplex.clock (complexAction depth index word) =
      (scale depth index : ℂ) * SourceClockComplex.clock word := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add coordinate scalar word _ _ previous =>
      simp only [map_add, complex_single, SourceClockComplex.clock_single, clock_index, previous]
      ring

end
end SourceCopyGraph
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
