import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CarbamoylSource

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence.NativeCarbamoyl
noncomputable section
open CPS1AtomicSource CPS1AtomicDynamics CPS1SameEventFunction CPS1PhosphorylExchange
open NativeProducts NativeSubstitution

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : Classical.Raw} {before : Classical.Current cursor priorRaw}
  {step : Classical.NativeStep before priorRaw.time} {raw : CPS1PhosphorylExchange.Raw}

def protonCredit (source : Common before step raw) (bct : Nat) : SourceBond cursor :=
  ⟨.fuel bct .bicarbonate attackingDescriptor,originalHydrogen source,"SING",false,"N"⟩

theorem bond_after_retains (bonds : List (SourceBond cursor)) (action : SourceBondAction cursor)
    (bond : SourceBond cursor) (held : bond ∈ bonds) (different : bond ≠ action.debit) :
    bond ∈ bondAfter bonds action :=
  List.mem_append_left _ ((List.mem_erase_of_ne different).mpr held)

theorem source_proton_transfer (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) :
    Nonempty (TokenStep material.event.after (protonToken source material.products.bicarbonate)) := by
  let bct := material.products.bicarbonate
  have nitrogenBond := ammonia_bond_held source
  have nitrogenVertices := source_bond_vertices source _ nitrogenBond
  have oxygenHeld : AtomOrigin.fuel bct .bicarbonate attackingDescriptor ∈ vertices source :=
    material.event.safe.2.1
  have safe : (protonToken source bct).safe source := by
    refine ⟨oxygenHeld,nitrogenVertices.1,?_,?_,?_⟩
    · simp [protonToken,ammoniaNitrogen]
    · intro bond held
      have same : bond = nitrogenHydrogen source := by simpa [protonToken,ChargedToken.debits] using held
      subst bond
      exact ⟨nitrogenBond,nitrogenVertices⟩
    · intro bond held
      have same : bond = protonCredit source bct := by simpa [protonToken,ChargedToken.credits,protonCredit] using held
      subst bond
      refine ⟨oxygenHeld,nitrogenVertices.2,?_⟩
      simp [protonCredit,originalHydrogen]
  have oxygenAtomHeld : (⟨.fuel bct .bicarbonate attackingDescriptor,attackingDescriptor⟩ : Atom cursor) ∈ source.atoms := by
    have indexed : (FuelKind.bicarbonate,bct) ∈ raw.fuel.zipIdx :=
      source_fuel_occurrence source bct .bicarbonate attackingDescriptor oxygenHeld
    exact fuel_atom_held source bct .bicarbonate attackingDescriptor indexed (by decide +kernel)
  have initial : electronInventory source (sourceGraph source) (.fuel bct .bicarbonate attackingDescriptor) = 9 := by
    have generated := initial_source_atom_electrons source _ oxygenAtomHeld
    exact generated.trans (by
      change (Charged.atomicNumber attackingDescriptor.source.element : ℤ)-attackingDescriptor.source.charge = 9
      decide +kernel)
  have paid : 1 ≤ electronInventory source material.event.after.graph (protonToken source bct).chargeDonor := by
    change 1 ≤ electronInventory source material.event.after.graph (.fuel bct .bicarbonate attackingDescriptor)
    rw [substitution_electrons,initial]
    norm_num [bct,carbamateToken,ChargedToken.delta,Finsupp.single_apply,ammoniaNitrogen]
    simp
  have unused : ∀ bond ∈ (protonToken source bct).debits, bond ∉ material.event.after.spent := by
    intro bond held
    have same : bond = nitrogenHydrogen source := by simpa [protonToken,ChargedToken.debits] using held
    subst bond
    rw [substitution_spent]
    simp [nitrogenHydrogen,sourceDebit,atpDebit,DescriptorBond.lift,carbamateDebit,ammoniaNitrogen]
  have debitPaid : ∀ bond ∈ (protonToken source bct).debits, 1 ≤ material.event.after.graph.incidence bond := by
    intro bond held
    have same : bond = nitrogenHydrogen source := by simpa [protonToken,ChargedToken.debits] using held
    subst bond
    rw [substitution_normal]
    apply inventory_paid
    apply bond_after_retains
    · exact List.mem_append_left _ ((List.mem_erase_of_ne (by
        simp [nitrogenHydrogen,sourceDebit,atpDebit,DescriptorBond.lift,ammoniaNitrogen])).mpr nitrogenBond)
    · simp [nitrogenHydrogen,carbamateDebit,ammoniaNitrogen]
  have absent : ∀ bond ∈ substitutionBonds source material, ¬ SamePair bond (protonCredit source bct) := by
    intro bond held
    rcases substitution_support source current material bond held with original | first | second
    · exact source_cross_absent source _ (by simp [sourcePart,protonCredit,originalHydrogen]) bond original
    · subst bond
      simp [SamePair,sourceCredit,protonCredit,originalHydrogen]
    · subst bond
      simp [SamePair,carbamateCredit,protonCredit,ammoniaNitrogen,originalHydrogen,
        ammoniaHydrogen,nitrogenDescriptor,ammoniaGraph]
  have free := pair_free material.event.after.graph _ (substitution_normal source current material) _ absent
  refine ⟨⟨safe,material.ready,paid,unused,debitPaid,?_,?_⟩⟩
  · intro bond held
    have same : bond = protonCredit source bct := by simpa [protonToken,ChargedToken.credits,protonCredit] using held
    subst bond
    exact free.1
  · intro bond held
    have same : bond = protonCredit source bct := by simpa [protonToken,ChargedToken.credits,protonCredit] using held
    subst bond
    exact free.2

theorem source_oxygen_deprotonation (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current)
    (sites : CarbamoylSites source current material)
    (first : TokenStep material.event.after (protonToken source material.products.bicarbonate)) :
    Nonempty (TokenStep first.after (deprotonateToken material.products.bicarbonate)) := by
  let bct := material.products.bicarbonate
  have originalBond : oxygenHydrogen (cursor := cursor) bct ∈ source.bonds :=
    fuel_bond_held source bct .bicarbonate
      ⟨carbamateOxygen,bicarbonateHydrogen,"SING",false,"N"⟩ sites.bicarbonateIndexed (by decide +kernel)
  have vertices := source_bond_vertices source _ originalBond
  have safe : (deprotonateToken (cursor := cursor) bct).safe source := by
    refine ⟨vertices.2,vertices.1,?_,?_,?_⟩
    · simp [deprotonateToken,carbamateOxygen,bicarbonateHydrogen,bicarbonateGraph]
    · intro bond held
      have same : bond = oxygenHydrogen bct := by simpa [deprotonateToken,ChargedToken.debits] using held
      subst bond
      exact ⟨originalBond,vertices⟩
    · simp [deprotonateToken,ChargedToken.credits]
  have atomHeld := fuel_atom_held source bct .bicarbonate bicarbonateHydrogen sites.bicarbonateIndexed (by decide +kernel)
  have initial : electronInventory source (sourceGraph source) (.fuel bct .bicarbonate bicarbonateHydrogen) = 1 := by
    have generated := initial_source_atom_electrons source _ atomHeld
    exact generated.trans (by
      change (Charged.atomicNumber bicarbonateHydrogen.source.element : ℤ)-bicarbonateHydrogen.source.charge = 1
      decide +kernel)
  have paid : 1 ≤ electronInventory source first.after.graph (deprotonateToken bct).chargeDonor := by
    change 1 ≤ electronInventory source
      (material.event.after.record (protonToken source bct)).graph (.fuel bct .bicarbonate bicarbonateHydrogen)
    rw [record_electrons,substitution_electrons,initial]
    norm_num [bct,protonToken,carbamateToken,ChargedToken.delta,Finsupp.single_apply,ammoniaNitrogen,
      attackingDescriptor,bicarbonateHydrogen,carbonDescriptor,bicarbonateGraph]
    simp
  have unused : ∀ bond ∈ (deprotonateToken (cursor := cursor) bct).debits, bond ∉ first.after.spent := by
    intro bond held
    have same : bond = oxygenHydrogen bct := by simpa [deprotonateToken,ChargedToken.debits] using held
    subst bond
    rw [TokenStep.after,charged_record_spent,substitution_spent]
    simp [protonToken,ChargedToken.debits,oxygenHydrogen,sourceDebit,atpDebit,DescriptorBond.lift,
      carbamateDebit,nitrogenHydrogen,ammoniaNitrogen,carbamateOxygen,carbonDescriptor,bicarbonateGraph]
  have normal := first.normal_after _ (substitution_normal source current material)
    ⟨nitrogenHydrogen source,some (protonCredit source bct)⟩ rfl
  have debitPaid : ∀ bond ∈ (deprotonateToken (cursor := cursor) bct).debits, 1 ≤ first.after.graph.incidence bond := by
    intro bond held
    have same : bond = oxygenHydrogen bct := by simpa [deprotonateToken,ChargedToken.debits] using held
    subst bond
    rw [normal]
    apply inventory_paid
    apply bond_after_retains
    · apply bond_after_retains
      · exact List.mem_append_left _ ((List.mem_erase_of_ne (by
          simp [oxygenHydrogen,sourceDebit,atpDebit,DescriptorBond.lift])).mpr originalBond)
      · simp [oxygenHydrogen,carbamateDebit,carbamateOxygen,carbonDescriptor,bicarbonateGraph]
    · simp [oxygenHydrogen,nitrogenHydrogen,ammoniaNitrogen]
  exact ⟨⟨safe,first.ready_after,paid,unused,debitPaid,
    by simp [deprotonateToken,ChargedToken.credits],by simp [deprotonateToken,ChargedToken.credits]⟩⟩

theorem source_second_phosphorylation (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) (sites : CarbamoylSites source current material)
    (first : TokenStep material.event.after (protonToken source material.products.bicarbonate))
    (second : TokenStep first.after (deprotonateToken material.products.bicarbonate)) :
    Nonempty (TokenStep second.after (phosphorylationToken sites.atp material.products.bicarbonate)) := by
  let bct := material.products.bicarbonate
  have originalBond : sourceDebit (cursor := cursor) sites.atp ∈ source.bonds :=
    fuel_bond_held source sites.atp .atp atpDebit sites.indexed (by decide +kernel)
  have vertices := source_bond_vertices source _ originalBond
  have oxygenAtomHeld := fuel_atom_held source bct .bicarbonate carbamateOxygen sites.bicarbonateIndexed (by decide +kernel)
  have oxygenHeld : AtomOrigin.fuel bct .bicarbonate carbamateOxygen ∈ CPS1MaterialIncidence.vertices source :=
    List.mem_map_of_mem oxygenAtomHeld
  have safe : (phosphorylationToken (cursor := cursor) sites.atp bct).safe source := by
    refine ⟨oxygenHeld,vertices.1,?_,?_,?_⟩
    · simp [phosphorylationToken]
    · intro bond held
      have same : bond = sourceDebit sites.atp := by simpa [phosphorylationToken,ChargedToken.debits] using held
      subst bond
      exact ⟨originalBond,vertices⟩
    · intro bond held
      have same : bond = phosphorylationCredit sites.atp bct := by
        simpa [phosphorylationToken,ChargedToken.credits] using held
      subst bond
      refine ⟨vertices.2,oxygenHeld,?_⟩
      simp [phosphorylationCredit]
  have initial : electronInventory source (sourceGraph source) (.fuel bct .bicarbonate carbamateOxygen) = 8 := by
    have generated := initial_source_atom_electrons source _ oxygenAtomHeld
    exact generated.trans (by
      change (Charged.atomicNumber carbamateOxygen.source.element : ℤ)-carbamateOxygen.source.charge = 8
      decide +kernel)
  have paid : 1 ≤ electronInventory source second.after.graph (phosphorylationToken sites.atp bct).chargeDonor := by
    change 1 ≤ electronInventory source
      ((material.event.after.record (protonToken source bct)).record (deprotonateToken bct)).graph
      (.fuel bct .bicarbonate carbamateOxygen)
    rw [record_electrons,record_electrons,substitution_electrons,initial]
    norm_num [bct,protonToken,deprotonateToken,carbamateToken,ChargedToken.delta,Finsupp.single_apply,ammoniaNitrogen,
      attackingDescriptor,bicarbonateHydrogen,carbamateOxygen,carbonDescriptor,bicarbonateGraph]
    simp
  have notFirst : sourceDebit (cursor := cursor) sites.atp ≠ sourceDebit material.products.atp := by
    intro same
    have left := congrArg SourceBond.left same
    exact sites.fresh (AtomOrigin.fuel.inj left).1
  have unused : ∀ bond ∈ (phosphorylationToken (cursor := cursor) sites.atp bct).debits, bond ∉ second.after.spent := by
    intro bond held
    have same : bond = sourceDebit sites.atp := by simpa [phosphorylationToken,ChargedToken.debits] using held
    subst bond
    rw [TokenStep.after,charged_record_spent,TokenStep.after,charged_record_spent,substitution_spent]
    simp [protonToken,deprotonateToken,ChargedToken.debits,sites.fresh,
      sourceDebit,atpDebit,DescriptorBond.lift,carbamateDebit,nitrogenHydrogen,oxygenHydrogen,ammoniaNitrogen]
  have firstNormal := first.normal_after _ (substitution_normal source current material)
    ⟨nitrogenHydrogen source,some (protonCredit source bct)⟩ rfl
  have secondNormal := second.normal_after _ firstNormal ⟨oxygenHydrogen bct,none⟩ rfl
  have debitPaid : ∀ bond ∈ (phosphorylationToken (cursor := cursor) sites.atp bct).debits,
      1 ≤ second.after.graph.incidence bond := by
    intro bond held
    have same : bond = sourceDebit sites.atp := by simpa [phosphorylationToken,ChargedToken.debits] using held
    subst bond
    rw [secondNormal]
    apply inventory_paid
    apply bond_after_retains
    · apply bond_after_retains
      · apply bond_after_retains
        · exact List.mem_append_left _ ((List.mem_erase_of_ne notFirst).mpr originalBond)
        · simp [sourceDebit,atpDebit,DescriptorBond.lift,carbamateDebit]
      · simp [sourceDebit,atpDebit,DescriptorBond.lift,nitrogenHydrogen,ammoniaNitrogen]
    · simp [sourceDebit,atpDebit,DescriptorBond.lift,oxygenHydrogen]
  have absent : ∀ bond ∈ bondAfter (bondAfter (substitutionBonds source material)
      ⟨nitrogenHydrogen source,some (protonCredit source bct)⟩) ⟨oxygenHydrogen bct,none⟩,
      ¬ SamePair bond (phosphorylationCredit sites.atp bct) := by
    intro bond held
    rcases bond_after_support _ _ bond held with previous | impossible
    · rcases bond_after_support _ _ bond previous with initial | proton
      · rcases substitution_support source current material bond initial with original | firstCredit | carbonCredit
        · exact source_cross_absent source _ (by simp [sourcePart,phosphorylationCredit]) bond original
        · subst bond
          simp [SamePair,sourceCredit,phosphorylationCredit,attackingDescriptor,carbamateOxygen,bicarbonateGraph]
        · subst bond
          simp [SamePair,carbamateCredit,phosphorylationCredit,ammoniaNitrogen]
      · have same : bond = protonCredit source bct := List.mem_singleton.mp proton
        subst bond
        simp [SamePair,protonCredit,phosphorylationCredit,originalHydrogen]
    · simp at impossible
  have free := pair_free second.after.graph _ secondNormal _ absent
  refine ⟨⟨safe,second.ready_after,paid,unused,debitPaid,?_,?_⟩⟩
  · intro bond held
    have same : bond = phosphorylationCredit sites.atp bct := by
      simpa [phosphorylationToken,ChargedToken.credits] using held
    subst bond
    exact free.1
  · intro bond held
    have same : bond = phosphorylationCredit sites.atp bct := by
      simpa [phosphorylationToken,ChargedToken.credits] using held
    subst bond
    exact free.2

structure CarbamoylSerial (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) where
  sites : CarbamoylSites source current material
  proton : TokenStep material.event.after (protonToken source material.products.bicarbonate)
  deprotonate : TokenStep proton.after (deprotonateToken material.products.bicarbonate)
  phosphorylate : TokenStep deprotonate.after (phosphorylationToken sites.atp material.products.bicarbonate)

theorem source_carbamoyl_serial (source : Common before step raw) (current : NativeCurrent source)
    (material : NativeAmmoniaSubstitution source current) : Nonempty (CarbamoylSerial source current material) := by
  obtain ⟨sites⟩ := source_carbamoyl_sites source current material
  obtain ⟨proton⟩ := source_proton_transfer source current material
  obtain ⟨deprotonate⟩ := source_oxygen_deprotonation source current material sites proton
  obtain ⟨phosphorylate⟩ := source_second_phosphorylation source current material sites proton deprotonate
  exact ⟨⟨sites,proton,deprotonate,phosphorylate⟩⟩

def CarbamoylSerial.after {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    ChargedState source current := serial.phosphorylate.after

theorem CarbamoylSerial.proton_actual {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    stepCharged? source current material.event.after (protonInstruction source material.products.bicarbonate) =
      .ok (serial.proton.charged _ (proton_prepared source material.products.bicarbonate)) :=
  serial.proton.charged_checked _ _

theorem CarbamoylSerial.deprotonate_actual {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    stepCharged? source current serial.proton.after (deprotonateInstruction material.products.bicarbonate) =
      .ok (serial.deprotonate.charged _ (deprotonate_prepared source material.products.bicarbonate serial.sites.bicarbonateIndexed)) :=
  serial.deprotonate.charged_checked _ _

theorem CarbamoylSerial.phosphorylate_actual {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    tokenStep? serial.deprotonate.after (phosphorylationToken serial.sites.atp material.products.bicarbonate) =
      .ok serial.phosphorylate := serial.phosphorylate.checked

def CarbamoylSerial.bonds {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    List (SourceBond cursor) :=
  bondAfter (bondAfter (bondAfter (substitutionBonds source material)
    ⟨nitrogenHydrogen source,some (protonCredit source material.products.bicarbonate)⟩)
    ⟨oxygenHydrogen material.products.bicarbonate,none⟩)
    ⟨sourceDebit serial.sites.atp,some (phosphorylationCredit serial.sites.atp material.products.bicarbonate)⟩

theorem CarbamoylSerial.incidence {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    serial.after.graph.incidence = bondInventory serial.bonds := by
  have first := serial.proton.normal_after _ (substitution_normal source current material)
    ⟨nitrogenHydrogen source,some (protonCredit source material.products.bicarbonate)⟩ rfl
  have second := serial.deprotonate.normal_after _ first ⟨oxygenHydrogen material.products.bicarbonate,none⟩ rfl
  exact serial.phosphorylate.normal_after _ second _ rfl

theorem CarbamoylSerial.paid {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    serial.after.paid = material.event.after.paid ++ [protonToken source material.products.bicarbonate,
      deprotonateToken material.products.bicarbonate,phosphorylationToken serial.sites.atp material.products.bicarbonate] := by
  simp only [CarbamoylSerial.after,TokenStep.after,ChargedState.record,List.append_assoc,List.cons_append,List.nil_append]

theorem CarbamoylSerial.spent {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    serial.after.spent = material.event.after.spent ++ [nitrogenHydrogen source,
      oxygenHydrogen material.products.bicarbonate,sourceDebit serial.sites.atp] := by
  rw [ChargedState.spent,serial.paid,List.flatMap_append]
  simp only [List.flatMap_cons,List.flatMap_nil,protonToken,deprotonateToken,phosphorylationToken,
    ChargedToken.debits,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.append_nil]
  rfl

theorem CarbamoylSerial.whole {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    serial.after.whole.1 = material.event.after.whole.1 ∧ serial.after.whole.1 = current := ⟨rfl,rfl⟩

theorem CarbamoylSerial.ready {source : Common before step raw} {current : NativeCurrent source}
    {material : NativeAmmoniaSubstitution source current} (serial : CarbamoylSerial source current material) :
    electronReady source serial.after.graph := serial.phosphorylate.ready_after

end
end CPS1MaterialIncidence.NativeCarbamoyl
