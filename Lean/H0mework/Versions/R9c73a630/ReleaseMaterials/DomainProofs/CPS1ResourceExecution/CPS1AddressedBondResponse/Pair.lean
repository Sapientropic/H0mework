import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1AddressedTransfer.Contract

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CPS1AddressedBondResponse
noncomputable section
open CPS1Deformation CPS1AddressedTransfer
variable {frame : CPS1Recycling.Frame}

def bridgeOxygen : CPS1EnzymeBath.Primary.Atom :=
  ⟨25,.O,0,false,"CHI_UNSPECIFIED",0,.source 25⟩

def bridgeBond : CPS1EnzymeBath.Primary.Bond :=
  ⟨25,28,1,false,"STEREONONE",0,false⟩

theorem bridge_oxygen_template : bridgeOxygen ∈ CPS1EnzymeBath.Primary.atp.atoms := by decide

theorem bridge_bond_template : bridgeBond ∈ CPS1EnzymeBath.Primary.atp.bonds :=
  phosphate_bridge_source

structure BridgeSite (source : CPS1ElectronicSource.State frame) where
  phosphate : Site source
  oxygenAtomSlot : Nat
  oxygenNuclear : CPS1MolecularFrame.NuclearIndex source

def selectBridge? (source : CPS1ElectronicSource.State frame) : Option (BridgeSite source) := do
  let phosphate ← selectSite? source
  let oxygen ← (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
    (fun row => row.1.origin == .bath phosphate.component bridgeOxygen)
  let nuclear ← (List.finRange source.geometry.nuclei.length).find? (fun index =>
    (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus oxygen.2 &&
      (CPS1MolecularFrame.nucleus source index).particle.source == oxygen.1.descriptor)
  pure ⟨phosphate,oxygen.2,nuclear⟩

theorem selected_bridge_source (source : CPS1ElectronicSource.State frame) (site : BridgeSite source)
    (actual : selectBridge? source = some site) :
    selectSite? source = some site.phosphate ∧
      ∃ atom : CPS1EnzymeBath.Joint.Atom,
        (atom,site.oxygenAtomSlot) ∈ (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx ∧
        atom.origin = .bath site.phosphate.component bridgeOxygen ∧
        (CPS1MolecularFrame.nucleus source site.oxygenNuclear).particle.address = .nucleus site.oxygenAtomSlot ∧
        (CPS1MolecularFrame.nucleus source site.oxygenNuclear).particle.source = atom.descriptor := by
  unfold selectBridge? at actual
  cases phosphateFound : selectSite? source with
  | none => simp [phosphateFound] at actual
  | some phosphate =>
    simp only [phosphateFound] at actual
    change ((CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
      (fun row => row.1.origin == .bath phosphate.component bridgeOxygen)).bind (fun oxygen =>
      ((List.finRange source.geometry.nuclei.length).find? (fun index =>
        (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus oxygen.2 &&
          (CPS1MolecularFrame.nucleus source index).particle.source == oxygen.1.descriptor)).bind
        (fun nuclear => some (⟨phosphate,oxygen.2,nuclear⟩ : BridgeSite source))) = some site at actual
    cases oxygenFound : (CPS1EnzymeBath.Joint.atoms frame source.geometry.originJoint).zipIdx.find?
        (fun row => row.1.origin == .bath phosphate.component bridgeOxygen) with
    | none => simp [oxygenFound] at actual
    | some oxygen =>
      rw [oxygenFound] at actual
      change ((List.finRange source.geometry.nuclei.length).find? (fun index =>
        (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus oxygen.2 &&
          (CPS1MolecularFrame.nucleus source index).particle.source == oxygen.1.descriptor)).bind
        (fun nuclear => some (⟨phosphate,oxygen.2,nuclear⟩ : BridgeSite source)) = some site at actual
      cases nuclearFound : (List.finRange source.geometry.nuclei.length).find? (fun index =>
          (CPS1MolecularFrame.nucleus source index).particle.address == .nucleus oxygen.2 &&
            (CPS1MolecularFrame.nucleus source index).particle.source == oxygen.1.descriptor) with
      | none => simp [nuclearFound] at actual
      | some nuclear =>
        rw [nuclearFound] at actual
        change some (⟨phosphate,oxygen.2,nuclear⟩ : BridgeSite source) = some site at actual
        cases Option.some.inj actual
        have origin : oxygen.1.origin = .bath phosphate.component bridgeOxygen := by
          simpa only [beq_iff_eq] using List.find?_some oxygenFound
        have coordinates : (CPS1MolecularFrame.nucleus source nuclear).particle.address = .nucleus oxygen.2 ∧
            (CPS1MolecularFrame.nucleus source nuclear).particle.source = oxygen.1.descriptor := by
          simpa only [Bool.and_eq_true,beq_iff_eq] using List.find?_some nuclearFound
        exact ⟨rfl,oxygen.1,List.mem_of_find?_eq_some oxygenFound,origin,coordinates⟩

theorem selected_bridge_bond (source : CPS1ElectronicSource.State frame) (site : BridgeSite source)
    (actual : selectBridge? source = some site) :
    (⟨.bath site.phosphate.component bridgeBond,
      .bath site.phosphate.component.occurrence 25,.bath site.phosphate.component.occurrence 28⟩ :
      CPS1EnzymeBath.Joint.Bond) ∈ CPS1EnzymeBath.Joint.bonds frame source.geometry.originJoint := by
  have phosphate := (selected_bridge_source source site actual).1
  obtain ⟨component,kind,_⟩ := selected_site_source source site.phosphate phosphate
  apply List.mem_append.mpr
  right
  apply List.mem_flatMap.mpr
  refine ⟨site.phosphate.component,component,?_⟩
  apply List.mem_map.mpr
  refine ⟨bridgeBond,?_,rfl⟩
  simpa only [kind,CPS1EnzymeBath.Primary.template] using bridge_bond_template

theorem selected_bridge_distinct_slots (source : CPS1ElectronicSource.State frame) (site : BridgeSite source)
    (actual : selectBridge? source = some site) : site.phosphate.atomSlot ≠ site.oxygenAtomSlot := by
  obtain ⟨phosphateSelected,oxygen,oxygenMember,oxygenOrigin,_,_⟩ := selected_bridge_source source site actual
  obtain ⟨_,_,phosphate,phosphateMember,phosphateOrigin,_,_⟩ :=
    selected_site_source source site.phosphate phosphateSelected
  intro same
  have first := List.mk_mem_zipIdx_iff_getElem?.mp phosphateMember
  have second := List.mk_mem_zipIdx_iff_getElem?.mp oxygenMember
  rw [same] at first
  have atomSame : phosphate = oxygen := Option.some.inj (first.symm.trans second)
  have originSame := congrArg CPS1EnzymeBath.Joint.Atom.origin atomSame
  rw [phosphateOrigin,oxygenOrigin] at originSame
  have templateSame : phosphateAtom = bridgeOxygen := CPS1EnzymeBath.Joint.AtomOrigin.bath.inj originSame |>.2
  have impossible : phosphateAtom ≠ bridgeOxygen := by decide
  exact impossible templateSame

theorem selected_bridge_distinct_nuclei (source : CPS1ElectronicSource.State frame) (site : BridgeSite source)
    (actual : selectBridge? source = some site) : site.phosphate.nuclear ≠ site.oxygenNuclear := by
  obtain ⟨phosphateSelected,_,_,_,oxygenAddress,_⟩ := selected_bridge_source source site actual
  obtain ⟨_,_,_,_,_,phosphateAddress,_⟩ := selected_site_source source site.phosphate phosphateSelected
  intro same
  rw [same,oxygenAddress] at phosphateAddress
  exact selected_bridge_distinct_slots source site actual
    (CPS1AtomicDynamics.Charged.Address.nucleus.inj phosphateAddress).symm

end
end CPS1AddressedBondResponse
