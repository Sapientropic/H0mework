import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Facts
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ElectronicSource.Continuous

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1ElectronicSource
noncomputable section
open CPS1ElectronicEvolution
open SaturationMonoid.PhysicsCore
open YangMills.FullPairing Stage10.ChargedPreparation
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

theorem execution_safe
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed : List CPS1Recycling.RawMaterial) (scanFeed : List CPS1Reinitiation.RawMaterial)
    (bodyFeed : List CPS1Reinitiation.Handover.RawMaterial) (depth : Nat)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind)
    (current : Σ frame : CPS1Recycling.Frame, Source.Occurrence frame)
    (actual : Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
      oldActions bathActions bathFeed actions feed = some current) :
    GoodStock current.2.current.stock ∧ NoGuardStock current.2.current.stock := by
  unfold Source.execution at actual
  cases generated : CPS1EnzymeBath.Source.generatedExecution edits water additional path
      recycleFeed scanFeed bodyFeed depth oldActions bathActions bathFeed with
  | none => simp [generated] at actual
  | some previous =>
    simp only [generated] at actual
    have same := Option.some.inj actual
    cases same
    exact generated_stage_safe previous.1 previous.2 actions feed

theorem current_continuous_fields (frame : CPS1Recycling.Frame) (stock : Stock frame)
    (generated : GoodStock stock) (state : State frame) (member : Species.quantum state ∈ stock) :
    Orthonormal ℂ (Consumer.occupiedFields state) ∧
      slaterDual (Consumer.occupiedFields state) (slater (Consumer.occupiedFields state)) = 1 ∧
      state.hamiltonian.IsHermitian :=
  ⟨Consumer.source_fields state (generated state member),
    Consumer.source_slater state (generated state member),source_hamiltonian_hermitian state⟩

theorem actual_native_response (frame : CPS1Recycling.Frame) (state : State frame) (x : Point)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) :
    (∑ index : ElectronIndex state.geometry × Bool,
      Stage9DEF.State.vectorEvaluation (Stage10.Runtime.tick.answer point)
        (Stage9DEF.Compatibility.responseMatrix
          (pairedMother
            (Native.weightedPreparation (ContinuousCharge.weights (Consumer.occupiedFields state) x index))
            (chargeMother.comp
              (Native.weightedPreparation (ContinuousCharge.weights (Consumer.occupiedFields state) x index)))))) =
      -Native.density (ContinuousCharge.weights (Consumer.occupiedFields state) x) :=
  Native.generated_complete_response (ContinuousCharge.weights (Consumer.occupiedFields state) x) point

theorem actual_native_current (frame : CPS1Recycling.Frame) (state : State frame) (x : Point)
    (point : ProofFreeRicherAnholonomicSource.BasePoint) :
    Native.current (ContinuousCharge.weights (Consumer.occupiedFields state) x) point =
      (4 * (Stage9C.Material.SpinPair.spinScale : ℂ)) *
        Native.charge (ContinuousCharge.weights (Consumer.occupiedFields state) x) point :=
  Native.complete_current (ContinuousCharge.weights (Consumer.occupiedFields state) x) point

theorem actual_electronic_source
    (edits : Target.Edits) (water additional : Nat) (path : CPS1Recycling.SplitSite)
    (recycleFeed recycleExtra : List CPS1Recycling.RawMaterial)
    (recyclingRaw : recycleFeed.Perm (CPS1Recycling.freshFuel ++ recycleExtra))
    (scanFeed scanExtra : List CPS1Reinitiation.RawMaterial)
    (scanningRaw : scanFeed.Perm (CPS1Reinitiation.rawFuel 151 ++ scanExtra))
    (bodyFeed bodyExtra : List CPS1Reinitiation.Handover.RawMaterial)
    (bodyRaw : bodyFeed.Perm
      (CPS1Reinitiation.Handover.rawFuel CPS1ResourceExecution.Program.originalPeptide.2 ++ bodyExtra))
    (depth : Nat) (generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid edits water additional)
    (oldActions : List CPS1AtomicDynamics.Source.RawAction)
    (bathActions : List CPS1EnzymeBath.Source.RawAction) (bathFeed : List CPS1EnzymeBath.Primary.TemplateKind)
    (actions : List Source.RawAction) (feed : List CPS1EnzymeBath.Primary.TemplateKind) :
    ∃ (frame : CPS1Recycling.Frame) (previous : CPS1EnzymeBath.Source.Occurrence frame)
      (current : Source.Occurrence frame),
      CPS1EnzymeBath.Source.generatedExecution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed = some ⟨frame,previous⟩ ∧
      Source.execution edits water additional path recycleFeed scanFeed bodyFeed depth
        oldActions bathActions bathFeed actions feed = some ⟨frame,current⟩ ∧
      current.previous = previous ∧ GoodStock current.current.stock ∧ NoGuardStock current.current.stock := by
  rcases Actual.actual_execution_source edits water additional path recycleFeed recycleExtra recyclingRaw
    scanFeed scanExtra scanningRaw bodyFeed bodyExtra bodyRaw depth generated oldActions bathActions bathFeed
    actions feed with ⟨frame,previous,current,prior,actual,same,next⟩
  have safe := execution_safe edits water additional path recycleFeed scanFeed bodyFeed depth
    oldActions bathActions bathFeed actions feed ⟨frame,current⟩ actual
  exact ⟨frame,previous,current,prior,actual,same,safe.1,safe.2⟩

end
end CPS1ElectronicSource
