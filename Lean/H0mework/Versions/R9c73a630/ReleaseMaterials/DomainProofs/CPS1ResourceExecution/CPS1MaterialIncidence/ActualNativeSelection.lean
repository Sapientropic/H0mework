import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.NativeIncidence

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open CPS1SameEventFunction CPS1BiologicalUpdate
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw}
  {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time}
  {raw : CPS1PhosphorylExchange.Raw}

theorem native_incidence_channel_nuclear_selection (source : Common before step raw)
    (current : NativeCurrent source) :
    ∃ centre leaving attacking,
      nuclearSector? source current.channel.phosphorus = some centre ∧
      nuclearSector? source current.channel.leavingOxygen = some leaving ∧
      nuclearSector? source current.channel.attackingOxygen = some attacking := by
  have selected := current.channelActual
  simp only [channel?,Bind.bind,Option.bind_eq_some_iff,Pure.pure,Option.some.injEq] at selected
  obtain ⟨atp,_,bct,_,p,pSelected,leave,leaveSelected,attack,attackSelected,same⟩ := selected
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == atp && source == .atp && atom.address.atom == "28"
      | _ => false)).map Prod.snd = some p at pSelected
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == atp && source == .atp && atom.address.atom == "25"
      | _ => false)).map Prod.snd = some leave at leaveSelected
  change ((source.atoms.zipIdx).find? (fun entry => match entry.1.origin with
      | .fuel slot source atom => slot == bct && source == .bicarbonate && atom.address.atom == "O2"
      | _ => false)).map Prod.snd = some attack at attackSelected
  have pBound : p < source.atoms.length := by
    obtain ⟨entry,selected,actual⟩ := Option.map_eq_some_iff.mp pSelected
    rw [← actual]
    exact List.snd_lt_of_mem_zipIdx (List.mem_of_find?_eq_some selected)
  have leaveBound : leave < source.atoms.length := by
    obtain ⟨entry,selected,actual⟩ := Option.map_eq_some_iff.mp leaveSelected
    rw [← actual]
    exact List.snd_lt_of_mem_zipIdx (List.mem_of_find?_eq_some selected)
  have attackBound : attack < source.atoms.length := by
    obtain ⟨entry,selected,actual⟩ := Option.map_eq_some_iff.mp attackSelected
    rw [← actual]
    exact List.snd_lt_of_mem_zipIdx (List.mem_of_find?_eq_some selected)
  rw [← same]
  refine ⟨⟨p,pBound⟩,⟨leave,leaveBound⟩,⟨attack,attackBound⟩,?_,?_,?_⟩
  · simp [nuclearSector?,pBound]
  · simp [nuclearSector?,leaveBound]
  · simp [nuclearSector?,attackBound]

end
end CPS1MaterialIncidence
