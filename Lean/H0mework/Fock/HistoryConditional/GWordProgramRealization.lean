import H0mework.Fock.HistoryConditional.GWordProgramSource

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGWordProgram

open SourceSuccessorBoundary
noncomputable section

theorem complex_single (program : Nat × Nat) (coordinate : Nat) (scalar : ℂ) :
    complexAction program (Finsupp.single coordinate scalar) =
      Finsupp.single (SourceCopyWordAffine.execute program coordinate) scalar := Finsupp.mapDomain_single

theorem mass_word (program : Nat × Nat) (source : Nat →₀ ℂ) :
    mass ℂ (complexAction program source) = mass ℂ source := by
  induction source using Finsupp.induction with
  | zero => simp
  | @single_add coordinate scalar source _ _ previous =>
      simp only [map_add, complex_single, mass_single, previous]

theorem clock_index (program : Nat × Nat) (positive : 0 < program.1) (coordinate : Nat) :
    (SourceClockModel.rawClock (SourceCopyWordAffine.execute program coordinate) : ℂ) =
      (program.1 : ℂ) * (SourceClockModel.rawClock coordinate : ℂ) + (program.2 : ℂ) := by
  simp only [SourceClockModel.rawClock, Int.cast_add, Int.cast_natCast, Int.cast_one]
  exact_mod_cast index_exact program positive coordinate

theorem clock_word (program : Nat × Nat) (positive : 0 < program.1) (source : Nat →₀ ℂ) :
    SourceClockComplex.clock (complexAction program source) =
      (program.1 : ℂ) * SourceClockComplex.clock source + (program.2 : ℂ) * mass ℂ source := by
  induction source using Finsupp.induction with
  | zero => simp
  | @single_add coordinate scalar source _ _ previous =>
      simp only [map_add, complex_single, SourceClockComplex.clock_single, clock_index program positive, mass_single, previous]
      ring

theorem action_source (program : Nat × Nat) (positive : 0 < program.1) (source : Nat →₀ ℂ) :
    action program positive (SourceJointClockGraph.read source) =
      SourceJointClockGraph.read (complexAction program source) := by
  change WithLp.toLp 2 (WithLp.toLp 2 (hilbertAction program positive (readWord source), mass ℂ source),
    (program.1 : ℂ) * SourceClockComplex.clock source + (program.2 : ℂ) * mass ℂ source) = _
  rw [hilbert_source, SourceJointClockGraph.read_apply, SourceMassCompletion.jointRead_apply, clock_word program positive, mass_word]

theorem complex_native (program : Nat × Nat) (source : Nat →₀ ℤ) :
    SourceClockComplex.ofNative ((Finsupp.lmapDomain ℤ ℤ (SourceCopyWordAffine.execute program)) source) =
      complexAction program (SourceClockComplex.ofNative source) := by
  change Finsupp.linearCombination ℤ (fun coordinate => Finsupp.single coordinate (1 : ℂ))
      (Finsupp.mapDomain (SourceCopyWordAffine.execute program) source) =
    ((complexAction program).restrictScalars ℤ)
      (Finsupp.linearCombination ℤ (fun coordinate => Finsupp.single coordinate (1 : ℂ)) source)
  rw [Finsupp.linearCombination_mapDomain, Finsupp.apply_linearCombination]
  congr 1
  apply congrArg (Finsupp.linearCombination ℤ)
  funext coordinate
  exact (complex_single program coordinate 1).symm

end
end SourceGWordProgram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
