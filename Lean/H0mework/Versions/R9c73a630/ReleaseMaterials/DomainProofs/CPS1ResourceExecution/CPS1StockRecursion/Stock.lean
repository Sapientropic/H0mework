import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Reinitiation.HandoverLedger

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1StockRecursion
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025

def terminalTrna (tail : List AA) : CPS1Recycling.Trna :=
  match tail with
  | [] => .initiator
  | _ :: _ => .elongator (Peptide.last (.M,tail))

theorem terminal_trna_actual (tail : List AA) :
    CPS1Recycling.postSpecies (terminalTrna tail) =
      CPS1InitiationTermination.NativeComplete.terminalComplex tail := by
  cases tail <;> rfl

def currencyWaste (tail : List AA) : CPS1ResourceExecution.Stock :=
  tail.flatMap (fun _ => [.gdp,.phosphate,.proton,.gdp,.phosphate,.proton])

def freeTrnas (tail : List AA) : CPS1ResourceExecution.Stock :=
  match tail with
  | [] => []
  | _ :: _ => .initiatorTRNA :: (tail.map CPS1ResourceExecution.Species.tRNA).erase
      (.tRNA (Peptide.last (.M,tail)))

theorem elongation_returns_exact_trnas (chain : Peptide) (tail : List AA) :
    (CPS1EndogenousTranslation.elongationWaste chain tail ++
      [CPS1ResourceExecution.Species.tRNA (CPS1ResourceExecution.Program.advancePeptide chain tail).last]).Perm
      (tail.map CPS1ResourceExecution.Species.tRNA ++ [CPS1ResourceExecution.Species.tRNA chain.last] ++ currencyWaste tail) := by
  induction tail generalizing chain with
  | nil => rfl
  | cons aa rest ih =>
    change ((CPS1EndogenousTranslation.elongationWaste (chain.extend aa) rest ++
      CPS1EndogenousTranslation.cycleWaste chain) ++
        [CPS1ResourceExecution.Species.tRNA
          (CPS1ResourceExecution.Program.advancePeptide (chain.extend aa) rest).last]).Perm _
    apply List.perm_iff_count.mpr
    intro species
    have later := (ih (chain.extend aa)).count_eq species
    simp only [List.count_append,List.count_cons,List.count_nil,
      CPS1Reinitiation.HandoverLedger.last_extend] at later
    simp only [
      CPS1EndogenousTranslation.cycleWaste,currencyWaste,List.flatMap_cons,List.map_cons,
      List.count_append,List.count_cons,List.count_nil] at later ⊢
    omega

theorem free_trnas_partition (tail : List AA) :
    (CPS1InitiationTermination.NativeComplete.elongationWasteWithInitiator tail).Perm
      (freeTrnas tail ++ currencyWaste tail) := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    have later := elongation_returns_exact_trnas (.M,[aa]) rest
    rw [CPS1InitiationTermination.NativeComplete.advance_exact] at later
    have headlast : Peptide.last (AA.M,[aa]) = aa := rfl
    apply List.perm_iff_count.mpr
    intro species
    have counted := later.count_eq species
    have lastmem : CPS1ResourceExecution.Species.tRNA (Peptide.last (.M,aa::rest)) ∈
        (aa::rest).map CPS1ResourceExecution.Species.tRNA := by
      apply List.mem_map.mpr
      refine ⟨Peptide.last (.M,aa::rest),?_,rfl⟩
      have equal : Peptide.last (.M,aa::rest) = (aa::rest).getLast (by simp) := by
        simp [Peptide.last,Peptide.word,List.getLast_cons]
      rw [equal]
      exact List.getLast_mem _
    have erase := (List.perm_cons_erase lastmem).count_eq species
    simp only [List.count_cons,List.map_cons] at erase
    simp only [CPS1InitiationTermination.NativeComplete.elongationWasteWithInitiator,
      CPS1InitiationTermination.NativeComplete.firstCycleWaste,freeTrnas,currencyWaste,
      List.flatMap_cons,List.count_append,List.count_cons,List.count_nil,headlast,List.map_cons] at counted ⊢
    omega

theorem after_return_trnas (tail : List AA) :
    (freeTrnas tail ++ [CPS1Recycling.returnedTrna (terminalTrna tail)]).Perm
      (.initiatorTRNA :: tail.map CPS1ResourceExecution.Species.tRNA) := by
  cases tail with
  | nil => rfl
  | cons aa rest =>
    have lastmem : CPS1ResourceExecution.Species.tRNA (Peptide.last (.M,aa::rest)) ∈
        (aa::rest).map CPS1ResourceExecution.Species.tRNA := by
      apply List.mem_map.mpr
      refine ⟨Peptide.last (.M,aa::rest),?_,rfl⟩
      have equal : Peptide.last (.M,aa::rest) = (aa::rest).getLast (by simp) := by
        simp [Peptide.last,Peptide.word,List.getLast_cons]
      rw [equal]
      exact List.getLast_mem _
    apply List.perm_iff_count.mpr
    intro species
    have counted := (List.perm_cons_erase lastmem).count_eq species
    simp only [List.count_cons] at counted
    simp only [freeTrnas,terminalTrna,CPS1Recycling.returnedTrna,List.count_append,List.count_cons,List.count_nil]
    omega

namespace Dictionary
abbrev Stock (frame : CPS1Recycling.Frame) := CPS1Reinitiation.Stock frame

def atpAdp : CPS1Recycling.Sites := ⟨.atp,.adp⟩

inductive Reaction
  | exchangeFirst | exchangeSecond
  | bind (trna : CPS1Recycling.Trna)
  | split (trna : CPS1Recycling.Trna) (path : CPS1Recycling.SplitSite)
  | returnTrna (trna : CPS1Recycling.Trna) (sites : CPS1Recycling.Sites)
  | dischargeRna (sites : CPS1Recycling.Sites)
  | chargeInitiator | capture (sites : CPS1Recycling.Sites)
  | scan (primitive : CPS1Reinitiation.Primitive)
  | body (reaction : CPS1Reinitiation.Handover.Reaction)
  deriving DecidableEq

def retained (frame : CPS1Recycling.Frame) (species : CPS1Recycling.Species frame) :
    CPS1Reinitiation.Species frame := .retained species

def old (frame : CPS1Recycling.Frame) (species : CPS1ResourceExecution.Species) :
    CPS1Reinitiation.Species frame := .retained (.old species)

def Reaction.reactants (frame : CPS1Recycling.Frame) : Reaction → Stock frame
  | .exchangeFirst => [.retained (.abce1 CPS1Reinitiation.Handover.dischargedSites),old frame .atp]
  | .exchangeSecond => [.retained (.abce1 atpAdp),old frame .atp]
  | .bind trna => [old frame (CPS1Recycling.postSpecies trna),.rna Molecules.mrna,
      .retained (.abce1 CPS1Recycling.doubleATP)]
  | .split trna path => (CPS1Recycling.splitPrimitive trna path).reactants frame |>.map (retained frame)
  | .returnTrna trna sites => (CPS1Recycling.Primitive.removeTrna trna sites).reactants frame |>.map (retained frame)
  | .dischargeRna sites => (CPS1Recycling.Primitive.removeMessage sites).reactants frame |>.map (retained frame)
  | .chargeInitiator => CPS1Recycling.Primitive.chargeNextInitiator.reactants frame |>.map (retained frame)
  | .capture sites => (CPS1Recycling.Primitive.captureNext sites).reactants frame |>.map (retained frame)
  | .scan primitive => primitive.reactants frame
  | .body reaction => reaction.reactants frame

/-- The genesis frame stays fixed. This dictionary threads the separately paired editor RNA;
discharge returns its actual RNA rather than minting another genomic coordinate. -/
def Reaction.products (frame : CPS1Recycling.Frame) : Reaction → Stock frame
  | .exchangeFirst => [.retained (.abce1 atpAdp),.retained .adp]
  | .exchangeSecond => [.retained (.abce1 CPS1Recycling.doubleATP),.retained .adp]
  | .bind trna => [.retained (.preSplit trna CPS1Recycling.doubleATP)]
  | .split trna path => (CPS1Recycling.splitPrimitive trna path).products frame |>.map (retained frame)
  | .returnTrna trna sites => (CPS1Recycling.Primitive.removeTrna trna sites).products frame |>.map (retained frame)
  | .dischargeRna sites => [.retained (.primedSmall sites),.rna Molecules.mrna]
  | .chargeInitiator => CPS1Recycling.Primitive.chargeNextInitiator.products frame |>.map (retained frame)
  | .capture sites => (CPS1Recycling.Primitive.captureNext sites).products frame |>.map (retained frame)
  | .scan primitive => primitive.products frame
  | .body reaction => reaction.products frame

abbrev Execution (frame : CPS1Recycling.Frame) := Inventory.Execution (CPS1Reinitiation.Species frame) Reaction

def execute (frame : CPS1Recycling.Frame) (program : List Reaction) (stock : Stock frame) : Execution frame :=
  Inventory.execute (Reaction.reactants frame) (Reaction.products frame) program stock

def recycleProgram (tail : List AA) (path : CPS1Recycling.SplitSite) : List Reaction :=
  let trna := terminalTrna tail
  [.exchangeFirst,.exchangeSecond,.bind trna,.split trna path,.returnTrna trna path.after,
    .dischargeRna path.after,.chargeInitiator,.capture path.after]

def program (tail : List AA) (path : CPS1Recycling.SplitSite) : List Reaction :=
  recycleProgram tail path ++ (CPS1Reinitiation.scanProgram path.after Molecules.mrna).map Reaction.scan ++
    (CPS1Reinitiation.Handover.fullProgram path Molecules.mrna 151 tail).map Reaction.body

inductive RawMaterial | aminoAcid (aa : AA) | atp | gtp | water
  deriving DecidableEq, Repr

def RawMaterial.species (frame : CPS1Recycling.Frame) : RawMaterial → CPS1Reinitiation.Species frame
  | .aminoAcid aa => old frame (.freeAA aa)
  | .atp => old frame .atp
  | .gtp => old frame .gtp
  | .water => old frame .water

def bodyRawFuel (tail : List AA) : List RawMaterial :=
  [.gtp,.water,.water] ++ tail.flatMap (fun aa => [.aminoAcid aa,.atp]) ++
    tail.flatMap (fun _ => [.gtp,.water,.gtp,.water]) ++ [.gtp,.water,.water]

def rawFuel (tail : List AA) : List RawMaterial :=
  [.atp,.atp,.water,.aminoAcid .M,.atp,.gtp] ++
    List.replicate 151 .atp ++ List.replicate 152 .water ++ bodyRawFuel tail

namespace Accounting

abbrev Channel := CPS1Reinitiation.HandoverLedger.Channel

/-- Bound recycling compounds carry the paired editor RNA; the coarse postTC is not another RNA. -/
def currentRna (frame : CPS1Recycling.Frame) (read : RegisteredRna → Nat) :
    CPS1Reinitiation.Species frame → Nat
  | .rna rna | .scanning _ rna _ | .recognized _ rna _ | .committed _ rna _ => read rna
  | .retained (.preSplit _ _) | .retained (.boundSmall _ _) | .retained (.smallWithMessage _) =>
      read Molecules.mrna
  | _ => 0

def measure (frame : CPS1Recycling.Frame) : Channel → CPS1Reinitiation.Species frame → Nat
  | .rna read => currentRna frame read
  | channel => CPS1Reinitiation.HandoverLedger.measure frame channel

def total (frame : CPS1Recycling.Frame) (channel : Channel) (stock : Stock frame) : Nat :=
  (stock.map (measure frame channel)).sum

theorem scan_balance (frame : CPS1Recycling.Frame) (primitive : CPS1Reinitiation.Primitive)
    (channel : Channel) :
    total frame channel ((Reaction.scan primitive).reactants frame) =
      total frame channel ((Reaction.scan primitive).products frame) := by
  cases channel with
  | currency currency =>
    exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.currency currency)
  | abce1 =>
    exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.oldFactor .abce1)
  | trna => exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive .trna
  | trnaRole role => exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.trnaRole role)
  | subunit subunit => exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.subunit subunit)
  | oldFactor factor => exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.oldFactor factor)
  | recruitmentFactor factor =>
    exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.recruitmentFactor factor)
  | residue aa => exact CPS1Reinitiation.Accounting.primitive_conservation frame primitive (.residue aa)
  | rna read =>
    cases primitive <;> simp [total,measure,currentRna,Reaction.reactants,Reaction.products,
      CPS1Reinitiation.Primitive.reactants,CPS1Reinitiation.Primitive.products]
    all_goals split <;> simp_all [currentRna]
  | oldMessageCoordinate =>
    cases primitive <;> simp [total,measure,CPS1Reinitiation.HandoverLedger.measure,
      Reaction.reactants,Reaction.products,CPS1Reinitiation.Primitive.reactants,CPS1Reinitiation.Primitive.products]
    all_goals split <;> simp_all

theorem body_balance (frame : CPS1Recycling.Frame) (reaction : CPS1Reinitiation.Handover.Reaction)
    (channel : Channel) :
    total frame channel ((Reaction.body reaction).reactants frame) =
      total frame channel ((Reaction.body reaction).products frame) := by
  cases channel with
  | rna read =>
    cases reaction <;> simp [total,measure,currentRna,Reaction.reactants,Reaction.products,
      CPS1Reinitiation.Handover.Reaction.reactants,CPS1Reinitiation.Handover.Reaction.products,
      CPS1Reinitiation.NativeDictionary.nativeReactants,CPS1Reinitiation.NativeDictionary.nativeProducts,
      CPS1Reinitiation.NativeDictionary.embedded,List.map_map,Function.comp_def]
  | currency currency => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.currency currency)
  | abce1 => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction .abce1
  | trna => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction .trna
  | trnaRole role => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.trnaRole role)
  | subunit subunit => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.subunit subunit)
  | oldFactor factor => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.oldFactor factor)
  | recruitmentFactor factor =>
    exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.recruitmentFactor factor)
  | residue aa => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction (.residue aa)
  | oldMessageCoordinate => exact CPS1Reinitiation.HandoverLedger.reaction_balance frame reaction .oldMessageCoordinate

theorem reaction_balance (frame : CPS1Recycling.Frame) (reaction : Reaction) (channel : Channel) :
    total frame channel (reaction.reactants frame) = total frame channel (reaction.products frame) := by
  cases reaction with
  | scan primitive => exact scan_balance frame primitive channel
  | body reaction => exact body_balance frame reaction channel
  | _ =>
    cases channel
    all_goals try cases ‹CPS1Reinitiation.Accounting.Currency›
    all_goals try cases ‹CPS1Recycling.Trna›
    all_goals try cases ‹CPS1Recycling.Trna›
    all_goals try cases ‹CPS1InitiationTermination.Accounting.Subunit›
    all_goals try cases ‹CPS1Recycling.Factor›
    all_goals try cases ‹Actor›
    all_goals try cases ‹CPS1Recycling.SplitSite›
    all_goals
      simp [total,measure,currentRna,Reaction.reactants,Reaction.products,retained,old,
        CPS1Reinitiation.HandoverLedger.measure,CPS1Reinitiation.Handover.dischargedSites,atpAdp,
        CPS1Recycling.splitPrimitive,CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,
        CPS1ResourceExecution.Reaction.reactants,CPS1ResourceExecution.Reaction.products,
        CPS1Recycling.doubleATP,CPS1Recycling.humanHybrid,
        CPS1Recycling.postSpecies,CPS1Recycling.returnedTrna,
        CPS1Reinitiation.Accounting.currencyCount,CPS1Reinitiation.Accounting.oldFactorCount,
        CPS1Reinitiation.Accounting.trnaCount,CPS1Reinitiation.Accounting.trnaRoleCount,
        CPS1Reinitiation.Accounting.retainedTrnaRoleCount,CPS1Reinitiation.Accounting.oldTrnaRoleCount,
        CPS1Reinitiation.Accounting.subunitCount,CPS1Reinitiation.Accounting.recruitmentFactorCount,
        CPS1Reinitiation.Accounting.residueCount,
        CPS1Recycling.adenylate,CPS1Recycling.guanylate,CPS1Recycling.phosphate,
        CPS1Recycling.nucleotideAdenylate,CPS1Recycling.nucleotidePhosphate,CPS1Recycling.siteMeasure,
        CPS1Recycling.actorCount,CPS1Recycling.trnaCount,CPS1Recycling.smallCount,CPS1Recycling.largeCount,
        CPS1Recycling.residueCount,CPS1ResourceExecution.adenylate,CPS1ResourceExecution.guanylate,
        CPS1ResourceExecution.phosphateGroups,CPS1ResourceExecution.trnaCount,CPS1ResourceExecution.residueCount,
        CPS1InitiationTermination.Accounting.actorCount,CPS1InitiationTermination.Accounting.initiatorCount,
        CPS1InitiationTermination.Accounting.subunitCount]

def siteEffect (read : CPS1Recycling.Sites → Nat) : Reaction → ℚ
  | .exchangeFirst => (read CPS1Reinitiation.Handover.dischargedSites : ℚ) - read atpAdp
  | .exchangeSecond => (read atpAdp : ℚ) - read CPS1Recycling.doubleATP
  | .split _ path => (read CPS1Recycling.doubleATP : ℚ) - read path.after
  | .body (.dischargeRemaining path _ _) =>
      (read path.after : ℚ) - read CPS1Reinitiation.Handover.dischargedSites
  | _ => 0

theorem reaction_site_effect (frame : CPS1Recycling.Frame) (reaction : Reaction)
    (read : CPS1Recycling.Sites → Nat) :
    Inventory.reactionAffinity
      (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ))
      (Reaction.reactants frame) (Reaction.products frame) reaction = siteEffect read reaction := by
  cases reaction
  all_goals try cases ‹CPS1Recycling.SplitSite›
  all_goals try cases ‹CPS1Reinitiation.Primitive›
  all_goals try cases ‹CPS1Reinitiation.Handover.Reaction›
  all_goals
    simp [Inventory.reactionAffinity,Inventory.value,siteEffect,Reaction.reactants,Reaction.products,retained,old,
      CPS1Recycling.splitPrimitive,CPS1Recycling.Primitive.reactants,CPS1Recycling.Primitive.products,
      CPS1Recycling.SplitSite.after,
      CPS1ResourceExecution.Reaction.reactants,CPS1ResourceExecution.Reaction.products,
      CPS1Reinitiation.Primitive.reactants,CPS1Reinitiation.Primitive.products,
      CPS1Reinitiation.Handover.Reaction.reactants,CPS1Reinitiation.Handover.Reaction.products,
      CPS1Reinitiation.NativeDictionary.nativeReactants,CPS1Reinitiation.NativeDictionary.nativeProducts,
      CPS1Reinitiation.NativeDictionary.embedded,CPS1Reinitiation.Accounting.sitesCount,
      CPS1Reinitiation.Accounting.retainedSites,List.map_map,Function.comp_def]
  all_goals split <;> simp_all

theorem execution_conservation (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (channel : Channel) :
    total frame channel stock = total frame channel (execute frame program stock).stock :=
  Inventory.execution_measure_preserved _ _ _ _ _ (fun reaction _ => reaction_balance frame reaction channel)

theorem execution_site_effect (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (read : CPS1Recycling.Sites → Nat) :
    Inventory.value (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ)) stock =
      Inventory.value (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ))
        (execute frame program stock).stock +
      Inventory.affinity (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ))
        (Reaction.reactants frame) (Reaction.products frame) (execute frame program stock).fired :=
  Inventory.execution_potential _ _ _ _ _

theorem execution_site_effect_computed (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (read : CPS1Recycling.Sites → Nat) :
    Inventory.value (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ)) stock =
      Inventory.value (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ))
        (execute frame program stock).stock +
      ((execute frame program stock).fired.map (siteEffect read)).sum := by
  have same : Inventory.reactionAffinity
      (fun species => (CPS1Reinitiation.Accounting.sitesCount frame read species : ℚ))
      (Reaction.reactants frame) (Reaction.products frame) = siteEffect read :=
    funext (fun reaction => reaction_site_effect frame reaction read)
  simpa only [Inventory.affinity,same] using execution_site_effect frame program stock read

theorem execution_inventory_balance (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (species : CPS1Reinitiation.Species frame) :
    stock.count species + (Inventory.credit (Reaction.products frame)
      (execute frame program stock).fired).count species =
    (execute frame program stock).stock.count species +
      (Inventory.debit (Reaction.reactants frame) (execute frame program stock).fired).count species :=
  Inventory.execution_balance _ _ _ _ _

theorem execution_potential (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (μ : CPS1Reinitiation.Species frame → ℚ) :
    Inventory.value μ stock = Inventory.value μ (execute frame program stock).stock +
      Inventory.affinity μ (Reaction.reactants frame) (Reaction.products frame)
        (execute frame program stock).fired := Inventory.execution_potential _ _ _ _ _

theorem execution_cut (frame : CPS1Recycling.Frame) (program : List Reaction)
    (stock : Stock frame) (missing : CPS1Reinitiation.Species frame)
    (cut : (execute frame program stock).missing = some missing) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      (execute frame program stock).stock.count missing < (reaction.reactants frame).count missing :=
  Inventory.execution_cut _ _ _ _ _ cut

end Accounting
end Dictionary

namespace Native
open Dictionary

def actors (frame : CPS1Recycling.Frame) : Dictionary.Stock frame :=
  (factorStock [.metRS,.eIF1,.eIF1A,.eIF2,.eIF3,.eIF5,.eIF5B,.eRF3]).map (old frame)

def recruitment (frame : CPS1Recycling.Frame) : Dictionary.Stock frame :=
  [.factor .eIF4A,.factor .eIF4B,.factor .eIF4E,.factor .eIF4G]

def reusable (frame : CPS1Recycling.Frame) (tail : List AA) : Dictionary.Stock frame :=
  [old frame (CPS1InitiationTermination.NativeComplete.terminalComplex tail),.rna Molecules.mrna,
    .retained (.abce1 CPS1Reinitiation.Handover.dischargedSites),.retained .eIF3j] ++
    actors frame ++ recruitment frame ++ (freeTrnas tail).map (old frame)

end Native
end CPS1StockRecursion
