import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.ActualNativePreparedBinding
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeResumablePhysics

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeAdoptionProbe
noncomputable section
open CPS1ResourceExecution CPS1AtomicDynamics CPS1ElectronicSource CPS1SameEventFunction CPS1PhosphorylExchange
open NativePaidEvent NativeAmmoniaDynamics NativeCPContinuationProbe NativePrepareNextProbe NativePrepareBinding
open NativeResumableProbe

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}
  {source : Common before step raw} {current : NativeCurrent source}
  {paid : SourceGeneratedPaidReturn source current} {continuation : CPNativeContinuation paid}

theorem state_fields_supported (state : PostState current) :
    Submodule.span ℂ (Set.range (CPS1ElectronicEvolution.fields (rawField current) state.rawC)) ≤
      Submodule.span ℂ (Set.range (rawField current)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨slot,rfl⟩
  unfold CPS1ElectronicEvolution.fields
  exact Submodule.sum_mem _ (fun index _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨index,rfl⟩))

theorem state_fields_orthonormal (state : PostState current) :
    Orthonormal ℂ (CPS1ElectronicEvolution.fields (rawField current) state.rawC) := by
  rw [post_fields]
  exact CPS1ElectronicEvolution.occupied_fields _ (basis_orthonormal current) _ state.gram

/-- The complete field is adopted with its stored coefficients and source span.
No occupation is regenerated from a joint descriptor. -/
structure NativeMolecular (current : NativeCurrent source) where
  state : PostState current
  coefficients : Matrix (RawIndex current) (Electron source.nodes) ℂ
  coefficientsActual : coefficients = state.rawC
  fields : Electron source.nodes → SpinSpace
  fieldsActual : fields = CPS1ElectronicEvolution.fields (rawField current) coefficients
  represented : fields = CPS1ElectronicEvolution.fields (basis current) state.occupied
  orthonormal : Orthonormal ℂ fields
  primitiveOrigin : RawIndex current → FieldOrigin cursor source.nodes
  primitiveActual : primitiveOrigin = rawOrigin current
  sourceSpan : Submodule.span ℂ (Set.range (basis current)) = Submodule.span ℂ (Set.range (rawField current))
  supported : Submodule.span ℂ (Set.range fields) ≤ Submodule.span ℂ (Set.range (rawField current))

def molecular_at (state : PostState current) : NativeMolecular current :=
  ⟨state,state.rawC,rfl,CPS1ElectronicEvolution.fields (rawField current) state.rawC,rfl,
    post_fields state,state_fields_orthonormal state,rawOrigin current,rfl,
    complete_source_span current,state_fields_supported state⟩

def NativeMolecular.density (molecular : NativeMolecular current) :=
  molecular.coefficients * molecular.coefficients.conjTranspose

def NativeMolecular.hamiltonian (molecular : NativeMolecular current) :=
  fullFockAt current molecular.state.pose molecular.state.occupied

structure NativeActive (current : NativeCurrent source) where
  molecular : NativeMolecular current
  origin : NativeOriginFace molecular.state

def NativeActive.state (active : NativeActive current) : PostState current := active.molecular.state

def active_at (state : PostState current) : NativeActive current :=
  ⟨molecular_at state,native_origin_face state⟩

variable (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)

def prepared_molecular : NativeMolecular current :=
  ⟨returned.occurrence.physical,returned.occurrence.physical.rawC,rfl,
    CPS1ElectronicEvolution.fields (rawField current) returned.occurrence.physical.rawC,rfl,
    germ.fieldsActual,state_fields_orthonormal returned.occurrence.physical,
    germ.primitiveOrigin,germ.primitiveActual,complete_source_span current,
    state_fields_supported returned.occurrence.physical⟩

def prepared_active : NativeActive current :=
  ⟨prepared_molecular returned germ,native_origin_face returned.occurrence.physical⟩

theorem prepared_active_state : (prepared_active returned germ).state = returned.occurrence.physical := rfl

theorem prepared_primitive_origin : (prepared_active returned germ).molecular.primitiveOrigin = germ.primitiveOrigin := rfl

theorem prepared_nuclear_origin : (prepared_active returned germ).origin.nuclearOrigin = germ.nuclearOrigin :=
  (prepared_active returned germ).origin.originActual.trans germ.originActual.symm

inductive Species (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)
  | prior (old : NativePrepareNextProbe.Species returned.occurrence)
  | molecular (state : NativeMolecular current)
  | active (state : NativeActive current)
  | spentMolecular
  | spentActive
  | spentPulse (before : PostState current)

noncomputable instance : DecidableEq (Species returned germ) := Classical.decEq _

inductive Event (returned : NativePrepareNext paid continuation) (germ : NativeOriginGerm returned.occurrence)
  | molecularAdopt
  | activeAdopt
  | pulse (active : NativeActive current)

def pulse_active (active : NativeActive current) : NativeActive current :=
  active_at (advanceNative active.state).next

def reactants : Event returned germ → List (Species returned germ)
  | .molecularAdopt => [.prior .prepared]
  | .activeAdopt => [.molecular (prepared_molecular returned germ)]
  | .pulse active => [.active active]

def products : Event returned germ → List (Species returned germ)
  | .molecularAdopt => [.molecular (prepared_molecular returned germ),.spentMolecular]
  | .activeAdopt => [.active (prepared_active returned germ),.spentActive]
  | .pulse active => [.active (pulse_active active),.spentPulse active.state]

abbrev Execution := Inventory.Execution (Species returned germ) (Event returned germ)

def initialStock : List (Species returned germ) := returned.next.stock.map Species.prior

def residualStock : List (Species returned germ) :=
  current.remaining.map (fun material => .prior (.remaining material))

def molecularStock : List (Species returned germ) :=
  .molecular (prepared_molecular returned germ) :: .spentMolecular :: residualStock returned germ

def activeStock : List (Species returned germ) :=
  .active (prepared_active returned germ) :: .spentActive :: .spentMolecular :: residualStock returned germ

def compileAdoptions : List CPS1Deformation.Source.RawAction → List (Event returned germ)
  | .old .adopt :: rest => .molecularAdopt :: compileAdoptions rest
  | .adopt :: rest => .activeAdopt :: compileAdoptions rest
  | _ => []

def runAdoptions : Execution returned germ :=
  Inventory.execute (reactants returned germ) (products returned germ)
    (compileAdoptions returned germ returned.next.pending) (initialStock returned germ)

theorem initial_stock_exact : initialStock returned germ = .prior .prepared :: residualStock returned germ := by
  rw [initialStock,returned.next_exact]
  simp only [preparedStock,List.map_cons,List.map_map,Function.comp_def,residualStock]

theorem fire_molecular : Inventory.fire (reactants returned germ) (products returned germ)
    (Event.molecularAdopt : Event returned germ) (initialStock returned germ) = .ok (molecularStock returned germ) := by
  classical
  rw [initial_stock_exact]
  simp [Inventory.fire,Inventory.consume,reactants,products,molecularStock]

theorem fire_active : Inventory.fire (reactants returned germ) (products returned germ)
    (Event.activeAdopt : Event returned germ) (molecularStock returned germ) = .ok (activeStock returned germ) := by
  classical
  simp [Inventory.fire,Inventory.consume,reactants,products,molecularStock,activeStock]

theorem adoption_execution_exact : runAdoptions returned germ =
    ⟨[.molecularAdopt,.activeAdopt],[],activeStock returned germ,none⟩ := by
  have second : Inventory.execute (reactants returned germ) (products returned germ)
      [Event.activeAdopt] (molecularStock returned germ) =
        ⟨[.activeAdopt],[],activeStock returned germ,none⟩ := by
    rw [Inventory.execute_cons,fire_active]
  have selected : compileAdoptions returned germ returned.next.pending = [.molecularAdopt,.activeAdopt] := by
    rw [returned.next_exact]
    rfl
  rw [runAdoptions,selected,Inventory.execute_cons,fire_molecular]
  dsimp only
  rw [second]

def Species.live? : Species returned germ → Option (CPS1ReactiveField.LiveMaterial frame)
  | .prior (.remaining material) => some material
  | _ => none

def Species.physical? : Species returned germ → Option (PostState current)
  | .prior .evolved | .prior .prepared => some returned.occurrence.physical
  | .molecular value => some value.state
  | .active value => some value.state
  | _ => none

theorem residual_live : (residualStock returned germ).filterMap (Species.live? returned germ) = current.remaining := by
  have actual (materials : List (CPS1ReactiveField.LiveMaterial frame)) :
      (materials.map (fun material => (Species.prior (.remaining material) : Species returned germ))).filterMap
        (Species.live? returned germ) = materials := by
    induction materials with
    | nil => rfl
    | cons material rest ih =>
      simpa only [List.map_cons,List.filterMap_cons,Species.live?] using congrArg (material :: ·) ih
  exact actual _

theorem residual_physical : (residualStock returned germ).filterMap (Species.physical? returned germ) = [] := by
  simp only [residualStock,List.filterMap_map,Function.comp_def,Species.physical?,List.filterMap_none]

theorem active_remaining : (activeStock returned germ).filterMap (Species.live? returned germ) = current.remaining := by
  simp only [activeStock,List.filterMap_cons,Species.live?,residual_live]

theorem active_physical : (activeStock returned germ).filterMap (Species.physical? returned germ) =
    [returned.occurrence.physical] := by
  simp only [activeStock,List.filterMap_cons,Species.physical?,prepared_active_state,residual_physical]

theorem molecular_no_replay : Inventory.fire (reactants returned germ) (products returned germ)
    (Event.molecularAdopt : Event returned germ) (activeStock returned germ) = .error (.prior .prepared) := by
  classical
  simp [Inventory.fire,Inventory.consume,reactants,activeStock,residualStock]

end
end CPS1MaterialIncidence.NativeAdoptionProbe
