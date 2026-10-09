import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.Rows
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1EnzymeBath.Partner
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1BiologicalUpdate.SourceGenome

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics

def registeredEdits : Target.Edits := ⟨true,true,true⟩
def registeredWater : Nat := 1
def registeredAdditional : Nat := 0
def registeredPath : CPS1Recycling.SplitSite := .first
def registeredRecycleFeed := CPS1Recycling.freshFuel
def registeredScanFeed := CPS1Reinitiation.rawFuel 151
def registeredBodyFeed := CPS1Reinitiation.Handover.rawFuel Program.originalPeptide.2
def registeredDepth : Nat := 0
def registeredFrame := CPS1Recycling.Source.frame registeredEdits registeredWater registeredAdditional

def sourceShapeJoint : CPS1EnzymeBath.Joint.State registeredFrame :=
  CPS1EnzymeBath.Joint.attach registeredFrame
    (CPS1EnzymeBath.Joint.fromBody registeredFrame ⟨CPS1LocalChemicalExecution.Chain.initial registeredFrame,[],0⟩)
    .carbamoylPhosphate

def sourceParticles := CPS1EnzymeBath.Joint.particles registeredFrame sourceShapeJoint
def sourceShapeGeometry : CPS1ElectronicSource.Geometry registeredFrame :=
  ⟨{sourceShapeJoint with rows := registrationRows sourceParticles},registrationNodes sourceParticles⟩
def registeredCaptureBudget : ℝ := max 0 (CPS1ElectronicSource.capturePrice sourceShapeGeometry) + 1
def registeredOldActions : List CPS1AtomicDynamics.Source.RawAction := []
def registeredBathActions : List CPS1EnzymeBath.Source.RawAction :=
  registrationBathActions sourceParticles ++ [.deposit registeredCaptureBudget]

def registeredSourceExecution :=
  CPS1Deformation.Source.execution registeredEdits registeredWater registeredAdditional registeredPath
    registeredRecycleFeed registeredScanFeed registeredBodyFeed registeredDepth
    registeredOldActions registeredBathActions [] [] [] [] [] [] [] [] [] [] []

theorem registered_edit_credit :
    CPS1EditingChemicalJoin.EditingStock.paid registeredEdits registeredWater registeredAdditional = 1 := by
  decide +kernel

theorem registered_atomic_source :
    ∃ (frame : CPS1Recycling.Frame) (next : CPS1AtomicSource.Current.Occurrence frame)
      (surplus : CPS1AtomicSource.Current.Stock frame),
      CPS1AtomicSource.Current.execution registeredEdits registeredWater registeredAdditional registeredPath
        registeredRecycleFeed registeredScanFeed registeredBodyFeed registeredDepth = some ⟨frame,next⟩ ∧
      next.source = some (CPS1LocalChemicalExecution.Chain.initial frame) ∧
      next.current.fired = [.atomize (CPS1LocalChemicalExecution.Chain.initial frame)] ∧
      next.current.remaining = [] ∧ next.current.missing = none ∧
      next.current.stock.Perm (.atomic (CPS1LocalChemicalExecution.Chain.initial frame) :: surplus) := by
  have generated : 0 < CPS1EditingChemicalJoin.EditingStock.paid registeredEdits registeredWater registeredAdditional := by
    rw [registered_edit_credit]
    decide
  obtain ⟨frame,next,surplus,actual,selected,fired,remaining,cut,inventory,_⟩ :=
    CPS1AtomicSource.Contract.actual_atomic_complete registeredEdits registeredWater registeredAdditional registeredPath
      registeredRecycleFeed [] (by simp only [registeredRecycleFeed,List.append_nil]; rfl)
      registeredScanFeed [] (by simp only [registeredScanFeed,List.append_nil]; rfl)
      registeredBodyFeed [] (by simp only [registeredBodyFeed,List.append_nil]; rfl)
      registeredDepth generated
  exact ⟨frame,next,surplus,actual,selected,fired,remaining,cut,inventory⟩

theorem registered_source_nonempty : registeredSourceExecution.isSome := by
  obtain ⟨frame,atomic,surplus,actual,_⟩ := registered_atomic_source
  simp only [registeredSourceExecution,CPS1Deformation.Source.execution,
    CPS1MolecularFrame.Source.execution,CPS1Following.Source.execution,
    CPS1QuantumNuclear.Source.execution,CPS1ElectronicSource.Source.execution,
    CPS1EnzymeBath.Source.generatedExecution,CPS1EnzymeBath.Source.execution,
    CPS1AtomicDynamics.Source.execution,actual]
  rfl

def registeredProgramme :=
  CPS1ReactiveSourceEntry.programmeFromSource registeredEdits registeredWater registeredAdditional registeredPath
    registeredRecycleFeed registeredScanFeed registeredBodyFeed registeredDepth
    registeredOldActions registeredBathActions [] [] [] [] [] [] [] [] [] [] []
    [] [] [] 0 (([],[]),[]) 0

theorem registered_programme_nonempty : registeredProgramme.isSome := by
  have existsSource := Option.isSome_iff_exists.mp registered_source_nonempty
  obtain ⟨source,actual⟩ := existsSource
  unfold registeredProgramme
  rw [CPS1ReactiveSourceEntry.programme_from_source_stored_exact]
  change (registeredSourceExecution.map _).isSome
  rw [actual]
  rfl

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
