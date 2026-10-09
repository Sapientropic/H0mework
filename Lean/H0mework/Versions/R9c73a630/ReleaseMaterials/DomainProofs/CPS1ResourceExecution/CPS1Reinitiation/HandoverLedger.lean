import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.Handover

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1Reinitiation.HandoverLedger
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

inductive Channel
  | currency (currency : Accounting.Currency)
  | abce1 | trna | trnaRole (role : CPS1Recycling.Trna)
  | subunit (subunit : CPS1InitiationTermination.Accounting.Subunit)
  | oldFactor (factor : CPS1Recycling.Factor)
  | recruitmentFactor (factor : RecruitmentFactor)
  | rna (read : RegisteredRna → Nat)
  | residue (aa : AA)
  | oldMessageCoordinate

def measure (frame : CPS1Recycling.Frame) : Channel → Species frame → Nat
  | .currency currency => Accounting.currencyCount frame currency
  | .abce1 => Accounting.oldFactorCount frame .abce1
  | .trna => Accounting.trnaCount frame
  | .trnaRole role => Accounting.trnaRoleCount frame role
  | .subunit subunit => Accounting.subunitCount frame subunit
  | .oldFactor factor => Accounting.oldFactorCount frame factor
  | .recruitmentFactor factor => Accounting.recruitmentFactorCount frame factor
  | .rna read => Accounting.rnaCount frame read
  | .residue aa => Accounting.residueCount frame aa
  | .oldMessageCoordinate => fun species => match species with
      | .retained .messageCoordinate => 1 | _ => 0

def total (frame : CPS1Recycling.Frame) (channel : Channel) (stock : Stock frame) : Nat :=
  (stock.map (measure frame channel)).sum

theorem last_extend (peptide : Peptide) (aa : AA) : (peptide.extend aa).last = aa := by
  unfold Peptide.last Peptide.extend Peptide.word
  exact List.getLast_append_singleton (peptide.1 :: peptide.2)

theorem native_elongator_role_balance (reaction : CPS1ResourceExecution.Reaction) (aa : AA) :
    ((reaction.reactants).map (Accounting.oldTrnaRoleCount (.elongator aa))).sum =
      ((reaction.products).map (Accounting.oldTrnaRoleCount (.elongator aa))).sum := by
  cases reaction <;>
    simp [CPS1ResourceExecution.Reaction.reactants,CPS1ResourceExecution.Reaction.products,
      Accounting.oldTrnaRoleCount,factorStock,last_extend]
  all_goals simp [Peptide.last,Peptide.word]
  all_goals first | rfl | omega

theorem native_balance (frame : CPS1Recycling.Frame) (reaction : CPS1ResourceExecution.Reaction)
    (channel : Channel) :
    total frame channel ((Handover.Reaction.native reaction).reactants frame) =
      total frame channel ((Handover.Reaction.native reaction).products frame) := by
  simp only [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
    NativeDictionary.nativeReactants,NativeDictionary.nativeProducts,NativeDictionary.embedded,
    List.map_map,Function.comp_def]
  cases channel with
  | currency currency =>
    cases currency with
    | adenylate =>
      change moiety adenylate reaction.reactants = moiety adenylate reaction.products
      exact (productive_moieties_preserved reaction).1
    | guanylate =>
      change moiety guanylate reaction.reactants = moiety guanylate reaction.products
      exact (productive_moieties_preserved reaction).2.1
    | phosphate =>
      change moiety phosphateGroups reaction.reactants = moiety phosphateGroups reaction.products
      exact (productive_moieties_preserved reaction).2.2.1
  | trna =>
    change moiety CPS1ResourceExecution.trnaCount reaction.reactants =
      moiety CPS1ResourceExecution.trnaCount reaction.products
    exact (productive_moieties_preserved reaction).2.2.2.1
  | trnaRole role =>
    cases role with
    | initiator =>
      change moiety CPS1InitiationTermination.Accounting.initiatorCount reaction.reactants =
        moiety CPS1InitiationTermination.Accounting.initiatorCount reaction.products
      exact CPS1InitiationTermination.Accounting.reaction_initiator_balance reaction
    | elongator aa =>
      change (reaction.reactants.map (Accounting.oldTrnaRoleCount (.elongator aa))).sum =
        (reaction.products.map (Accounting.oldTrnaRoleCount (.elongator aa))).sum
      exact native_elongator_role_balance reaction aa
  | subunit subunit =>
    cases subunit <;>
      change moiety (CPS1InitiationTermination.Accounting.subunitCount _) reaction.reactants =
        moiety (CPS1InitiationTermination.Accounting.subunitCount _) reaction.products
    all_goals exact CPS1InitiationTermination.Accounting.reaction_subunit_balance reaction _
  | oldFactor factor =>
    cases factor with
    | old actor =>
      change moiety (CPS1InitiationTermination.Accounting.actorCount actor) reaction.reactants =
        moiety (CPS1InitiationTermination.Accounting.actorCount actor) reaction.products
      exact CPS1InitiationTermination.Accounting.reaction_actor_balance reaction actor
    | abce1 => simp [Accounting.oldFactorCount,CPS1Recycling.actorCount]
    | eIF3j => simp [Accounting.oldFactorCount,CPS1Recycling.actorCount]
  | residue aa =>
    change moiety (CPS1ResourceExecution.residueCount aa) reaction.reactants =
      moiety (CPS1ResourceExecution.residueCount aa) reaction.products
    exact (productive_moieties_preserved reaction).2.2.2.2 aa
  | abce1 => simp [Accounting.oldFactorCount,CPS1Recycling.actorCount]
  | recruitmentFactor factor =>
    simp [Accounting.recruitmentFactorCount]
  | rna read => simp [Accounting.rnaCount]
  | oldMessageCoordinate => simp

theorem reaction_balance (frame : CPS1Recycling.Frame) (reaction : Handover.Reaction) (channel : Channel) :
    total frame channel (reaction.reactants frame) = total frame channel (reaction.products frame) := by
  cases reaction with
  | native reaction => exact native_balance frame reaction channel
  | dischargeRemaining path rna address =>
    cases channel with
    | currency currency =>
      cases path <;> cases currency <;>
        simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,NativeDictionary.embedded,
          Accounting.currencyCount,CPS1Recycling.SplitSite.after,CPS1Recycling.humanHybrid,Handover.dischargedSites,
          CPS1Recycling.siteMeasure,CPS1Recycling.nucleotideAdenylate,CPS1Recycling.nucleotidePhosphate,
          CPS1Recycling.adenylate,CPS1Recycling.guanylate,CPS1Recycling.phosphate,
          CPS1ResourceExecution.adenylate,CPS1ResourceExecution.guanylate,phosphateGroups]
    | trnaRole role =>
      cases role <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,NativeDictionary.embedded,
        Accounting.trnaRoleCount,Accounting.retainedTrnaRoleCount,Accounting.oldTrnaRoleCount,
        CPS1InitiationTermination.Accounting.initiatorCount]
    | subunit subunit =>
      cases subunit <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,NativeDictionary.embedded,
        Accounting.subunitCount,CPS1Recycling.smallCount,CPS1Recycling.largeCount,
        CPS1InitiationTermination.Accounting.subunitCount]
    | oldFactor factor =>
      cases factor with
      | old actor => cases actor <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
          NativeDictionary.embedded,Accounting.oldFactorCount,CPS1Recycling.actorCount,
          CPS1InitiationTermination.Accounting.actorCount]
      | _ => simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
          NativeDictionary.embedded,Accounting.oldFactorCount,CPS1Recycling.actorCount]
    | _ => simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,NativeDictionary.embedded,
        Accounting.oldFactorCount,Accounting.trnaCount,Accounting.recruitmentFactorCount,Accounting.rnaCount,
        Accounting.residueCount,CPS1Recycling.actorCount,CPS1Recycling.trnaCount,
        CPS1Recycling.residueCount,CPS1ResourceExecution.trnaCount,CPS1ResourceExecution.residueCount]
  | transferTo5B rna address =>
    cases channel with
    | currency currency =>
      cases currency <;>
        simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,NativeDictionary.embedded,
          Accounting.currencyCount,Handover.dischargedSites,CPS1Recycling.siteMeasure,
          CPS1Recycling.nucleotideAdenylate,CPS1Recycling.nucleotidePhosphate,
          CPS1Recycling.adenylate,CPS1Recycling.guanylate,CPS1Recycling.phosphate,
          CPS1ResourceExecution.adenylate,CPS1ResourceExecution.guanylate,phosphateGroups]
    | oldFactor factor =>
      cases factor with
      | old actor => cases actor <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
          NativeDictionary.embedded,Accounting.oldFactorCount,CPS1Recycling.actorCount,
          CPS1InitiationTermination.Accounting.actorCount]
      | _ => simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
          NativeDictionary.embedded,Accounting.oldFactorCount,CPS1Recycling.actorCount]
    | recruitmentFactor factor =>
      cases factor <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
        NativeDictionary.embedded,Accounting.recruitmentFactorCount]
    | trnaRole role =>
      cases role <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
        NativeDictionary.embedded,Accounting.trnaRoleCount,Accounting.retainedTrnaRoleCount,
        Accounting.oldTrnaRoleCount,CPS1InitiationTermination.Accounting.initiatorCount]
    | subunit subunit =>
      cases subunit <;> simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
        NativeDictionary.embedded,Accounting.subunitCount,CPS1Recycling.smallCount,CPS1Recycling.largeCount,
        CPS1InitiationTermination.Accounting.subunitCount]
    | _ => simp [total,measure,Handover.Reaction.reactants,Handover.Reaction.products,
        NativeDictionary.embedded,Accounting.oldFactorCount,Accounting.trnaCount,Accounting.rnaCount,
        Accounting.residueCount,CPS1Recycling.actorCount,CPS1Recycling.trnaCount,CPS1Recycling.residueCount,
        CPS1ResourceExecution.trnaCount,CPS1ResourceExecution.residueCount]

theorem execution_conservation (frame : CPS1Recycling.Frame) (program : List Handover.Reaction)
    (stock : Stock frame) (channel : Channel) :
    total frame channel stock = total frame channel (Handover.execute frame program stock).stock :=
  Inventory.execution_measure_preserved _ _ _ _ _ (fun reaction _ => reaction_balance frame reaction channel)

theorem execution_site_effect (frame : CPS1Recycling.Frame) (program : List Handover.Reaction)
    (stock : Stock frame) (read : CPS1Recycling.Sites → Nat) :
    Inventory.value (fun species => (Accounting.sitesCount frame read species : ℚ)) stock =
      Inventory.value (fun species => (Accounting.sitesCount frame read species : ℚ))
        (Handover.execute frame program stock).stock +
      Inventory.affinity (fun species => (Accounting.sitesCount frame read species : ℚ))
        (Handover.Reaction.reactants frame) (Handover.Reaction.products frame)
        (Handover.execute frame program stock).fired := Inventory.execution_potential _ _ _ _ _

theorem execution_inventory_balance (frame : CPS1Recycling.Frame) (program : List Handover.Reaction)
    (stock : Stock frame) (species : Species frame) :
    stock.count species + (Inventory.credit (Handover.Reaction.products frame)
      (Handover.execute frame program stock).fired).count species =
    (Handover.execute frame program stock).stock.count species +
      (Inventory.debit (Handover.Reaction.reactants frame) (Handover.execute frame program stock).fired).count species :=
  Inventory.execution_balance _ _ _ _ _

theorem execution_potential (frame : CPS1Recycling.Frame) (program : List Handover.Reaction)
    (stock : Stock frame) (μ : Species frame → ℚ) :
    Inventory.value μ stock = Inventory.value μ (Handover.execute frame program stock).stock +
      Inventory.affinity μ (Handover.Reaction.reactants frame) (Handover.Reaction.products frame)
        (Handover.execute frame program stock).fired := Inventory.execution_potential _ _ _ _ _

theorem execution_cut (frame : CPS1Recycling.Frame) (program : List Handover.Reaction)
    (stock : Stock frame) (missing : Species frame) (cut : (Handover.execute frame program stock).missing = some missing) :
    ∃ reaction rest, (Handover.execute frame program stock).remaining = reaction :: rest ∧
      (Handover.execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ _ cut

structure CycleContract : Prop where
  scanExecution : type_of% CPS1Reinitiation.Source.execution_from_actual_stock
  scanComplete : type_of% CPS1Reinitiation.Source.native_complete
  scanReadout : type_of% CPS1Reinitiation.Source.paid48_and_both_message_identities
  scanConservation : type_of% Accounting.execution_conservation
  scanInventory : type_of% CPS1Reinitiation.run_balance
  scanPotential : type_of% CPS1Reinitiation.run_potential
  scanCut : type_of% CPS1Reinitiation.run_cut
  sourceProgram : type_of% Handover.Source.source_program
  bodyRawFuel : type_of% Handover.Source.raw_source_fuel_generated
  bodyExecution : type_of% Handover.Source.execution_from_actual_stock
  bodyComplete : type_of% Handover.Source.native_complete
  bodyReadout : type_of% Handover.Source.released_editor_next_postTC_and_both_RNAs
  reactionBalance : type_of% reaction_balance
  conservation : type_of% execution_conservation
  siteEffect : type_of% execution_site_effect
  inventory : type_of% execution_inventory_balance
  potential : type_of% execution_potential
  cut : type_of% execution_cut

theorem sourceGeneratedCycle : CycleContract :=
  ⟨CPS1Reinitiation.Source.execution_from_actual_stock,CPS1Reinitiation.Source.native_complete,
    CPS1Reinitiation.Source.paid48_and_both_message_identities,Accounting.execution_conservation,
    CPS1Reinitiation.run_balance,CPS1Reinitiation.run_potential,CPS1Reinitiation.run_cut,
    Handover.Source.source_program,Handover.Source.raw_source_fuel_generated,Handover.Source.execution_from_actual_stock,
    Handover.Source.native_complete,Handover.Source.released_editor_next_postTC_and_both_RNAs,
    reaction_balance,execution_conservation,execution_site_effect,execution_inventory_balance,execution_potential,execution_cut⟩

end CPS1Reinitiation.HandoverLedger
