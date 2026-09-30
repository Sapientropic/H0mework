import H0mework.Versions.X.NavierStokes.SourceAction.ReceiptSpacetime

set_option autoImplicit false
open scoped ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeGeneratedSpacetime

open Set MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientWholeContinuousMildSerrinUniqueness
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartWholeContinuousMildSerrin
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointPositiveTimeH1Reentry
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime
open NativeReceiptTimeProfile NativeReceiptSpacetime NativePositiveTimeMoments NativeSpacetimeControl

noncomputable section

variable {nu : Viscosity} {Seed : Type} [WholeRestartPhysicalSeed nu Seed] {seed : Seed}

theorem generated_positive_spacetime_control (replay : GeneratedWholeRestartCanonicalReplay seed)
    (delta : ℝ) (positive : 0 < delta) (before : delta < wholeRestartDuration seed)
    (modes : Finset IntegerWavevector) :
    let receipt := generatedWholeRestartWholeContinuousMildSerrinReceipt replay
    let support : Set Spacetime := Icc delta (wholeRestartDuration seed) ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field receipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField receipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField receipt modes) support := by
  let window := positiveWindow replay delta positive before
  exact ⟨field_contDiffOn window, vorticityField_contDiffOn window, correctionField_contDiffOn window modes⟩

def nextPositiveWindow (current : GeneratedWholeRestartCurrent nu) (delta : ℝ)
    (positive : 0 < delta) (before : delta < wholeRestartDuration current.contact) : Window current.nextReceipt :=
  positiveWindow (generatedWholeRestartCanonicalReplay current.contact) delta positive before

def successorWindow (current : GeneratedWholeRestartCurrent nu) : Window current.next.nextReceipt :=
  regularWindow (generatedWholeRestartCanonicalReplay current.next.contact) (next_contact_momentRegular current)

def cofinalNextWindow (initial : GeneratedWholeRestartCurrent nu) :
    Window (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).nextReceipt :=
  regularWindow (generatedWholeRestartCanonicalReplay (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact)
    (cofinal_reentry_contact_momentRegular initial)

theorem next_positive_spacetime_control (current : GeneratedWholeRestartCurrent nu) (delta : ℝ)
    (positive : 0 < delta) (before : delta < wholeRestartDuration current.contact) (modes : Finset IntegerWavevector) :
    let support : Set Spacetime := Icc delta (wholeRestartDuration current.contact) ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field current.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField current.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField current.nextReceipt modes) support :=
  generated_positive_spacetime_control (generatedWholeRestartCanonicalReplay current.contact) delta positive before modes

theorem successor_spacetime_control (current : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    let support : Set Spacetime := Icc (0 : ℝ) (wholeRestartDuration current.next.contact) ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field current.next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField current.next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField current.next.nextReceipt modes) support :=
  ⟨field_contDiffOn (successorWindow current), vorticityField_contDiffOn (successorWindow current),
    correctionField_contDiffOn (successorWindow current) modes⟩

theorem cofinal_next_spacetime_control (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector) :
    let next := generatedPositiveTimeH1NextCurrentOfNativeTemporalCofinalOccurrence initial
      (nativeTemporalCofinalVisitAuthority initial).toLedgerReadout.occurrence
    let support : Set Spacetime := Icc (0 : ℝ) (wholeRestartDuration next.contact) ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField next.nextReceipt modes) support := by
  dsimp only
  rw [nativeTemporalCofinalVisitAuthority_positiveTimeH1NextCurrent]
  exact ⟨field_contDiffOn (cofinalNextWindow initial), vorticityField_contDiffOn (cofinalNextWindow initial),
    correctionField_contDiffOn (cofinalNextWindow initial) modes⟩

theorem macro_step_spacetime_control {initial next : GeneratedWholeRestartCurrent nu}
    (step : GeneratedWholeRestartEndpointMacroStep nu initial next) (modes : Finset IntegerWavevector) :
    let support : Set Spacetime := Icc (0 : ℝ) (wholeRestartDuration next.contact) ×ˢ univ
    ContDiffOn ℝ (↑(⊤ : ℕ∞)) (field next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (vorticityField next.nextReceipt) support ∧
      ContDiffOn ℝ (↑(⊤ : ℕ∞)) (correctionField next.nextReceipt modes) support := by
  let window := regularWindow (generatedWholeRestartCanonicalReplay next.contact) (macro_next_contact_momentRegular step)
  exact ⟨field_contDiffOn window, vorticityField_contDiffOn window, correctionField_contDiffOn window modes⟩

theorem cofinal_next_all_order_Lp (initial : GeneratedWholeRestartCurrent nu) (modes : Finset IntegerWavevector)
    (order : ℕ) (exponent : ℝ≥0∞) {domain : Set Spacetime} (compact : IsCompact domain)
    (contained : domain ⊆ Icc (0 : ℝ) (wholeRestartDuration
      (sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial).contact) ×ˢ univ) :
    let next := sourceGeneratedNativeTemporalPositiveTimeH1NextCurrent initial
    let support : Set Spacetime := Icc (0 : ℝ) (wholeRestartDuration next.contact) ×ˢ univ
    ∀ observation ∈ ({field next.nextReceipt, vorticityField next.nextReceipt, correctionField next.nextReceipt modes} :
        Set (Spacetime → PhysicalSpace)),
      ∃ budget : ℝ, 0 ≤ budget ∧
        MemLp (iteratedFDerivWithin ℝ order observation support) exponent (volume.restrict domain) ∧
        eLpNorm (iteratedFDerivWithin ℝ order observation support) exponent (volume.restrict domain) ≤
          ENNReal.ofReal budget * volume domain ^ (1 / exponent.toReal) := by
  dsimp only
  intro observation member
  simp only [mem_insert_iff, mem_singleton_iff] at member
  rcases member with rfl | rfl | rfl
  · exact field_frechet_Lp (cofinalNextWindow initial) order exponent compact contained
  · exact vorticityField_frechet_Lp (cofinalNextWindow initial) order exponent compact contained
  · exact correctionField_frechet_Lp (cofinalNextWindow initial) modes order exponent compact contained

end
end SaturationMonoid.NavierStokes.NativeGeneratedSpacetime
