import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration.ExchangeRaw
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1PhosphorylExchange.ReadControls

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
noncomputable section
open CPS1ResourceExecution CPS1LiveEditing CPS1BiologicalUpdate CPS1SameEventFunction CPS1PhosphorylExchange
attribute [local irreducible] registeredFrame registeredBefore registeredWhole registeredResponse

noncomputable def emptyExchangeRaw : CPS1PhosphorylExchange.Raw := ⟨firstFuel,[],0,0⟩

noncomputable def exchangeRawFromRepair {body : Body}
    (repair : LocalRepairDisposition body) (response : WholeRaw) : CPS1PhosphorylExchange.Raw := by
  classical
  exact match repair with
  | .residual _ _ => emptyExchangeRaw
  | .repaired receipt =>
    match actual : Classical.fromCursor receipt.nextBody.current.2 response.particles with
    | .sourceResidual _ => emptyExchangeRaw
    | .mechanicalResidual _ _ => emptyExchangeRaw
    | .responded before step =>
      if unit : ∀ node ∈ step.next.nodes, node.row.inertia = 1 then
        source_exchange_raw before step actual unit
      else emptyExchangeRaw

private theorem exchange_raw_selected {body : Body} (receipt : LocalRepairReceipt body)
    (response : WholeRaw) (before : Classical.Current receipt.nextBody.current.2 response.particles)
    (step : Classical.NativeStep before response.particles.time)
    (actual : Classical.fromCursor receipt.nextBody.current.2 response.particles = .responded before step)
    (unit : ∀ node ∈ step.next.nodes, node.row.inertia = 1) :
    exchangeRawFromRepair (.repaired receipt) response = source_exchange_raw before step actual unit := by
  unfold exchangeRawFromRepair
  dsimp only
  split
  · rename_i failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i other failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i actualBefore actualStep found
    have same := Classical.Disposition.responded.inj (found.symm.trans actual)
    rcases same with ⟨beforeSame,stepSame⟩
    subst actualBefore
    cases stepSame
    split
    · rfl
    · rename_i denied
      exact False.elim (denied unit)

noncomputable def registeredExchange : CPS1PhosphorylExchange.Raw :=
  exchangeRawFromRepair (repairWhole registeredWhole registeredSupply) registeredResponse

attribute [local irreducible] registeredExchange

private theorem stored_exchange_actual {body : Body} (receipt : LocalRepairReceipt body)
    {responseRaw : WholeRaw} {raw : CPS1PhosphorylExchange.Raw}
    (whole : WholeResponse (.repaired receipt) responseRaw)
    (before : Classical.Current receipt.nextBody.current.2 responseRaw.particles)
    (step : Classical.NativeStep before responseRaw.particles.time)
    (actual : whole.particles = .responded before step)
    (source : Common before step raw) (admitted : admit before step raw = .ok source)
    (next : NativeCurrent source) (exchanged : firstElectronicExchange source = .ok next) :
    fromWhole (.repaired receipt) whole raw = .responded whole before step actual source next := by
  unfold fromWhole
  dsimp only
  split
  · rename_i failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i other failure found
    have impossible := found.symm.trans actual
    cases impossible
  · rename_i actualBefore actualStep found
    have same := Classical.Disposition.responded.inj (found.symm.trans actual)
    rcases same with ⟨beforeSame,stepSame⟩
    subst actualBefore
    cases stepSame
    split
    · rename_i failure found
      have impossible := found.symm.trans admitted
      cases impossible
    · rename_i actualSource found
      have same := Except.ok.inj (found.symm.trans admitted)
      subst actualSource
      split
      · rename_i failure found
        have impossible := found.symm.trans exchanged
        cases impossible
      · rename_i actualNext found
        have same := Except.ok.inj (found.symm.trans exchanged)
        subst actualNext
        rfl

theorem registered_exchange_actual
    (receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩))
    (selected : repairWhole registeredWhole registeredSupply = .repaired receipt) :
    ∃ before : Classical.Current receipt.nextBody.current.2 registeredResponse.particles,
      ∃ step : Classical.NativeStep before registeredResponse.particles.time,
      ∃ actual : (wholeResponse (.repaired receipt) registeredResponse).particles = .responded before step,
      ∃ source : Common before step registeredExchange, ∃ next : NativeCurrent source,
        admit before step registeredExchange = .ok source ∧ firstElectronicExchange source = .ok next ∧
        fromWhole (.repaired receipt) (wholeResponse (.repaired receipt) registeredResponse) registeredExchange =
          .responded (wholeResponse (.repaired receipt) registeredResponse) before step actual source next := by
  obtain ⟨before,step,actual,unit⟩ := registered_response_actual receipt selected
  have cursorActual : Classical.fromCursor receipt.nextBody.current.2 registeredResponse.particles = .responded before step :=
    (wholeResponse (.repaired receipt) registeredResponse).particlesActual.symm.trans actual
  have raw : registeredExchange = source_exchange_raw before step cursorActual unit := by
    unfold registeredExchange
    rw [selected]
    exact exchange_raw_selected receipt registeredResponse before step cursorActual unit
  have generated := source_exchange_actual before step cursorActual unit
  rw [← raw] at generated
  obtain ⟨source,admitted,next,exchanged⟩ := generated
  exact ⟨before,step,actual,source,next,admitted,exchanged,
    stored_exchange_actual receipt _ before step actual source admitted next exchanged⟩

noncomputable def registeredNativeInput : RegisteredNativeInput where
  edits := registeredEdits
  water := registeredWater
  additional := registeredAdditional
  path := registeredPath
  recycleFeed := registeredRecycleFeed
  scanFeed := registeredScanFeed
  bodyFeed := registeredBodyFeed
  depth := registeredDepth
  oldActions := registeredOldActions
  bathActions := registeredBathActions
  bathFeed := []
  electronicActions := []
  electronicFeed := []
  nuclearActions := []
  nuclearFeed := []
  followingActions := []
  followingFeed := []
  molecularActions := []
  molecularFeed := []
  deformationActions := []
  deformationFeed := []
  actions := []
  feed := []
  raw := []
  firstDepth := 0
  input := (([],[]),[])
  secondDepth := 0
  updateWater := 2
  updateRaw := registeredTranslationRaw
  updatePath := .first
  recycleEvents := []
  recycleRaw := []
  physical := noPhysicalSupply
  newDepth := 0
  supply := registeredSupply
  response := registeredResponse
  exchange := registeredExchange

theorem registered_input_programme :
    CPS1ReactiveSourceEntry.programmeFromSource registeredNativeInput.edits registeredNativeInput.water
      registeredNativeInput.additional registeredNativeInput.path registeredNativeInput.recycleFeed
      registeredNativeInput.scanFeed registeredNativeInput.bodyFeed registeredNativeInput.depth
      registeredNativeInput.oldActions registeredNativeInput.bathActions registeredNativeInput.bathFeed
      registeredNativeInput.electronicActions registeredNativeInput.electronicFeed registeredNativeInput.nuclearActions
      registeredNativeInput.nuclearFeed registeredNativeInput.followingActions registeredNativeInput.followingFeed
      registeredNativeInput.molecularActions registeredNativeInput.molecularFeed registeredNativeInput.deformationActions
      registeredNativeInput.deformationFeed registeredNativeInput.actions registeredNativeInput.feed registeredNativeInput.raw
      registeredNativeInput.firstDepth registeredNativeInput.input registeredNativeInput.secondDepth =
        some ⟨registeredFrame,registeredProgrammeData⟩ := by
  exact registered_programme_actual

theorem registered_input_exchange_positive :
    ∃ receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩),
      repairWhole registeredWhole registeredNativeInput.supply = .repaired receipt ∧
      ∃ before : Classical.Current receipt.nextBody.current.2 registeredNativeInput.response.particles,
      ∃ step : Classical.NativeStep before registeredNativeInput.response.particles.time,
      ∃ actual : (wholeResponse (.repaired receipt) registeredNativeInput.response).particles = .responded before step,
      ∃ source : Common before step registeredNativeInput.exchange, ∃ next : NativeCurrent source,
        fromWhole (.repaired receipt) (wholeResponse (.repaired receipt) registeredNativeInput.response) registeredNativeInput.exchange =
          .responded (wholeResponse (.repaired receipt) registeredNativeInput.response) before step actual source next := by
  obtain ⟨receipt,repaired⟩ := registered_repair_selected
  obtain ⟨before,step,actual,source,next,_admitted,_exchanged,positive⟩ := registered_exchange_actual receipt repaired
  exact ⟨receipt,repaired,before,step,actual,source,next,positive⟩

theorem registered_exchange_missing_atp
    (receipt : LocalRepairReceipt (initialBody ⟨registeredFrame,registeredBefore⟩))
    (before : Classical.Current receipt.nextBody.current.2 registeredNativeInput.response.particles)
    (step : Classical.NativeStep before registeredNativeInput.response.particles.time) :
    admit before step {registeredNativeInput.exchange with fuel := [.atp,.bicarbonate]} = .error .missingATP :=
  missing_atp_is_retained before step _ (by decide +kernel)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.NativeRegistration
