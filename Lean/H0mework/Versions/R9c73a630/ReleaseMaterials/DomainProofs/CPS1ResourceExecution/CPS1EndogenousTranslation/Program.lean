import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Deamination.ContinuedCoding
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1ResourceExecution.Consumer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CPS1EndogenousTranslation
open CPS1ResourceExecution
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
open CPS1Deamination.ContinuedCoding CPS1Deamination.CodingReadout

/-- This decoder starts from the actual DNA's coding readout. The printed protein is not an input. -/
def peptideFromCoding? (dna : Bases) : Option Peptide := do
  let coding ← Coding.coding? dna
  let labels ← Coding.translate Coding.code coding
  Program.peptideOfLabels? labels

def continuedPeptide (edits : Target.Edits) (water additional : Nat) : Option Peptide := do
  let labels ← continuedStopChain edits water additional
  Program.peptideOfLabels? labels

def continuedPlan (edits : Target.Edits) (water additional : Nat) : Option Program.Plan :=
  (continuedPeptide edits water additional).map Program.compile

open Lean Elab Term
private def aaExpr (aa : AA) : Expr :=
  mkConst (match aa with
    | .A => ``AA.A | .C => ``AA.C | .D => ``AA.D | .E => ``AA.E | .F => ``AA.F
    | .G => ``AA.G | .H => ``AA.H | .I => ``AA.I | .K => ``AA.K | .L => ``AA.L
    | .M => ``AA.M | .N => ``AA.N | .P => ``AA.P | .Q => ``AA.Q | .R => ``AA.R
    | .S => ``AA.S | .T => ``AA.T | .V => ``AA.V | .W => ``AA.W | .Y => ``AA.Y)

elab "endogenousSourcePeptide%" paid:ident : term => do
  let isPaid := paid.getId == `true
  unless isPaid || paid.getId == `false do
    throwError "Expected literal true or false"
  let some peptide := continuedPeptide ⟨false,true,false⟩ 0 (if isPaid then 1 else 0)
    | throwError "Actual DNA did not generate a complete nonempty endogenous peptide"
  Meta.mkAppM ``Prod.mk #[aaExpr peptide.1,
    ← Meta.mkListLit (mkConst ``AA) (peptide.2.map aaExpr)]

/-- Both carriers are reified from the actual deamination execution, not the printed sequence. -/
def correctedPeptide : Peptide := endogenousSourcePeptide% true
def uncorrectedPeptide : Peptide := endogenousSourcePeptide% false

theorem actual_peptide_generated (edits : Target.Edits) (water additional : Nat) :
    continuedPeptide edits water additional =
      some (if paidEighth edits (water+additional) then correctedPeptide else uncorrectedPeptide) := by
  unfold continuedPeptide
  have labels := continued_stop_all_capacities edits water additional
  change (do
    let labels ← continuedStopChain edits water additional
    Program.peptideOfLabels? labels) = _
  rw [labels]
  by_cases paid : paidEighth edits (water+additional) = true
  · simp only [paid, if_true]
    decide +kernel
  · have unpaid : paidEighth edits (water+additional) = false := by
      cases value : paidEighth edits (water+additional) <;> simp_all
    simp only [unpaid, Bool.false_eq_true, if_false]
    decide +kernel

theorem actual_plan_generated (edits : Target.Edits) (water additional : Nat) :
    continuedPlan edits water additional = some
      (Program.compile (if paidEighth edits (water+additional) then correctedPeptide else uncorrectedPeptide)) := by
  rw [continuedPlan, actual_peptide_generated]
  rfl

theorem endogenous_lengths :
    correctedPeptide.word.length = 1500 ∧ uncorrectedPeptide.word.length = 334 ∧
    (Program.compile correctedPeptide).charges.length = 1500 ∧
    (Program.compile correctedPeptide).elongationCore.length = 4497 ∧
    (Program.compile uncorrectedPeptide).charges.length = 334 ∧
    (Program.compile uncorrectedPeptide).elongationCore.length = 999 := by
  decide +kernel

theorem printed_reference_recognized :
    correctedPeptide.word.map Program.aaLabel = Source.referenceProtein ∧
    uncorrectedPeptide.word.map Program.aaLabel = Source.referenceProtein.take 334 := by
  decide +kernel

/-- The original interpreter handles arbitrary raw stock. Missing resources retain its real cut. -/
theorem actual_plan_resources (edits : Target.Edits) (water additional : Nat) :
    ResourceContract (Program.compile
      (if paidEighth edits (water+additional) then correctedPeptide else uncorrectedPeptide)) :=
  resourceContract _

/-- A permutation of raw reactants pays the existing consume function, including multiplicity. -/
theorem consume_available (required remainder stock : Stock)
    (inventory : stock.Perm (required ++ remainder)) :
    ∃ next, consume required stock = .ok next ∧ next.Perm remainder := by
  induction required generalizing stock with
  | nil => exact ⟨stock, rfl, inventory⟩
  | cons a required inductionHypothesis =>
      have present : a ∈ stock := inventory.mem_iff.mpr (by simp)
      have residual : (stock.erase a).Perm (required ++ remainder) := by
        have erased := inventory.erase a
        simpa using erased
      rcases inductionHypothesis (stock.erase a) residual with ⟨next,paid,aligned⟩
      exact ⟨next, by simp only [consume, if_pos present]; exact paid, aligned⟩

theorem fire_available (reaction : Reaction) (remainder stock : Stock)
    (inventory : stock.Perm (reaction.reactants ++ remainder)) :
    ∃ next, fire reaction stock = .ok next ∧ next.Perm (reaction.products ++ remainder) :=
  Inventory.fire_available Reaction.reactants Reaction.products reaction remainder stock inventory

/-- Productive elongation fuel contains one charged tRNA and two GTP/water pairs per new residue. -/
def elongationFuel (tail : List AA) : Stock :=
  tail.flatMap (fun aa => [.aaTRNA aa,.gtp,.water,.gtp,.water])

def cycleWaste (chain : Peptide) : Stock :=
  [.gdp,.phosphate,.proton,.tRNA chain.last,.gdp,.phosphate,.proton]

theorem native_cycle (chain : Peptide) (aa : AA) (surplus stock : Stock)
    (inventory : stock.Perm (.peptidyl chain ::
      [.aaTRNA aa,.gtp,.water,.gtp,.water] ++ surplus)) :
    ∃ delivered transferred moved,
      fire (.deliver chain aa) stock = .ok delivered ∧
      fire (.transfer chain aa) delivered = .ok transferred ∧
      fire (.translocate (Peptide.extend chain aa)) transferred = .ok moved ∧
      moved.Perm (.peptidyl (Peptide.extend chain aa) :: cycleWaste chain ++ surplus) := by
  rcases fire_available (.deliver chain aa) ([.gtp,.water] ++ surplus) stock inventory with
    ⟨delivered,first,deliveredInventory⟩
  rcases fire_available (.transfer chain aa)
      ([.gdp,.phosphate,.proton,.gtp,.water] ++ surplus) delivered deliveredInventory with
    ⟨transferred,second,transferredInventory⟩
  have translocationInventory : transferred.Perm
      ((Reaction.translocate (Peptide.extend chain aa)).reactants ++
        [.tRNA chain.last,.gdp,.phosphate,.proton] ++ surplus) := by
    apply transferredInventory.trans
    apply List.perm_iff_count.mpr
    intro species
    simp only [Reaction.products,Reaction.reactants,List.count_cons,List.count_append,
      List.count_nil,List.append_assoc]
    omega
  rcases fire_available (.translocate (Peptide.extend chain aa))
      ([.tRNA chain.last,.gdp,.phosphate,.proton] ++ surplus) transferred translocationInventory with
    ⟨moved,third,movedInventory⟩
  exact ⟨delivered,transferred,moved,first,second,third,movedInventory⟩

def elongationWaste (chain : Peptide) (tail : List AA) : Stock :=
  List.rec (motive := fun _ => Peptide → Stock) (fun _ => [])
    (fun aa _ recur current =>
      recur (Peptide.extend current aa) ++ cycleWaste current) tail chain

/-- Actual native execution reaches the attached chain from lower raw fuel plus an explicit loaded boundary. -/
theorem native_elongation_complete (chain : Peptide) (tail : List AA) (surplus stock : Stock)
    (inventory : stock.Perm (.peptidyl chain :: elongationFuel tail ++ surplus)) :
    let result := execute (Program.compileElongation chain tail) stock
    result.fired = Program.compileElongation chain tail ∧ result.remaining = [] ∧
    result.missing = none ∧ result.stock.Perm
      (.peptidyl (Program.advancePeptide chain tail) :: elongationWaste chain tail ++ surplus) := by
  induction tail generalizing chain stock surplus with
  | nil =>
      change [] = [] ∧ [] = [] ∧ (none : Option Species) = none ∧
        stock.Perm (.peptidyl chain :: surplus)
      exact ⟨rfl,rfl,rfl,by simpa [elongationFuel] using inventory⟩
  | cons aa tail inductionHypothesis =>
      rcases native_cycle chain aa (elongationFuel tail ++ surplus) stock inventory with
        ⟨delivered,transferred,moved,first,second,third,movedInventory⟩
      have nextInventory : moved.Perm
          (.peptidyl (Peptide.extend chain aa) :: elongationFuel tail ++
            (cycleWaste chain ++ surplus)) := by
        apply movedInventory.trans
        exact (List.perm_append_comm_assoc (cycleWaste chain) (elongationFuel tail) surplus).cons _
      have continued := inductionHypothesis (Peptide.extend chain aa)
        (cycleWaste chain ++ surplus) moved nextInventory
      rcases continued with ⟨fired,remaining,missing,finalInventory⟩
      have expansion : Program.compileElongation chain (aa :: tail) =
          .deliver chain aa :: .transfer chain aa :: .translocate (Peptide.extend chain aa) ::
            Program.compileElongation (Peptide.extend chain aa) tail := rfl
      rw [expansion]
      simp only [CPS1Deamination.ExecutionReadout.execute_cons,first,second,third]
      refine ⟨by rw [fired],remaining,missing,?_⟩
      change (execute (Program.compileElongation (Peptide.extend chain aa) tail) moved).stock.Perm
        (.peptidyl (Program.advancePeptide (Peptide.extend chain aa) tail) ::
          (elongationWaste (Peptide.extend chain aa) tail ++ cycleWaste chain) ++ surplus)
      simpa only [List.cons_append,List.append_assoc] using finalInventory

def chargingFuel (word : List AA) : Stock := word.flatMap (fun aa => (Reaction.charge aa).reactants)
def chargingProducts (word : List AA) : Stock :=
  word.reverse.flatMap (fun aa => (Reaction.charge aa).products)

/-- Charging consumes raw amino acid, matching free tRNA, and ATP per source residue. -/
theorem native_charging_complete (word : List AA) (surplus stock : Stock)
    (inventory : stock.Perm (chargingFuel word ++ surplus)) :
    let result := execute (word.map Reaction.charge) stock
    result.fired = word.map Reaction.charge ∧ result.remaining = [] ∧
    result.missing = none ∧ result.stock.Perm (chargingProducts word ++ surplus) := by
  induction word generalizing surplus stock with
  | nil => exact ⟨rfl,rfl,rfl,by simpa [chargingFuel,chargingProducts,execute] using inventory⟩
  | cons aa tail inductionHypothesis =>
      have firstInventory : stock.Perm
          ((Reaction.charge aa).reactants ++ (chargingFuel tail ++ surplus)) := by
        simpa only [chargingFuel,List.flatMap_cons,List.append_assoc] using inventory
      rcases fire_available (.charge aa) (chargingFuel tail ++ surplus) stock firstInventory with
        ⟨next,paid,nextInventory⟩
      have nextFuel : next.Perm (chargingFuel tail ++ ((Reaction.charge aa).products ++ surplus)) :=
        nextInventory.trans (List.perm_append_comm_assoc _ _ _)
      rcases inductionHypothesis ((Reaction.charge aa).products ++ surplus) next nextFuel with
        ⟨fired,remaining,missing,finalInventory⟩
      simp only [List.map_cons,CPS1Deamination.ExecutionReadout.execute_cons,paid]
      refine ⟨by rw [fired],remaining,missing,?_⟩
      simpa only [chargingProducts,List.reverse_cons,List.flatMap_append,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.append_assoc] using finalInventory

/-- These are raw fuel requirements calculated from the generated chain, never clinical inventory. -/
def loadedElongationFuel (peptide : Peptide) : Stock :=
  .peptidyl (peptide.1,[]) :: elongationFuel peptide.2

def selectedPeptide (edits : Target.Edits) (water additional : Nat) : Peptide :=
  if paidEighth edits (water+additional) then correctedPeptide else uncorrectedPeptide

/-- Both actual resource invocations read the newly generated plan itself. -/
def actualCharging (edits : Target.Edits) (water additional : Nat) (stock : Stock) : Option Execution :=
  (continuedPlan edits water additional).map (fun plan => execute plan.charges stock)

def actualElongation (edits : Target.Edits) (water additional : Nat) (stock : Stock) : Option Execution :=
  (continuedPlan edits water additional).map (fun plan => execute plan.elongationCore stock)

theorem source_charging_native (edits : Target.Edits) (water additional : Nat) :
    let peptide := selectedPeptide edits water additional
    ∃ result, actualCharging edits water additional (chargingFuel peptide.word) = some result ∧
      result.fired = (Program.compile peptide).charges ∧ result.remaining = [] ∧
      result.missing = none ∧ result.stock.Perm (chargingProducts peptide.word) := by
  let peptide := selectedPeptide edits water additional
  refine ⟨execute (Program.compile peptide).charges (chargingFuel peptide.word),?_,?_⟩
  · rw [actualCharging,actual_plan_generated]
    rfl
  · simpa only [Program.compile,List.append_nil] using
      native_charging_complete peptide.word [] (chargingFuel peptide.word) (by simp)

theorem source_elongation_native (edits : Target.Edits) (water additional : Nat) :
    let peptide := selectedPeptide edits water additional
    ∃ result, actualElongation edits water additional (loadedElongationFuel peptide) = some result ∧
      result.fired = (Program.compile peptide).elongationCore ∧ result.remaining = [] ∧
      result.missing = none ∧ ∃ attached,
        attached.word = peptide.word ∧
        result.stock.Perm (.peptidyl attached :: elongationWaste (peptide.1,[]) peptide.2) := by
  let peptide := selectedPeptide edits water additional
  refine ⟨execute (Program.compile peptide).elongationCore (loadedElongationFuel peptide),?_,?_⟩
  · rw [actualElongation,actual_plan_generated]
    rfl
  · have completed := native_elongation_complete (peptide.1,[]) peptide.2 []
      (loadedElongationFuel peptide) (by simp only [loadedElongationFuel,List.append_nil]; exact List.Perm.refl _)
    rcases completed with ⟨fired,remaining,missing,finalInventory⟩
    exact ⟨fired,remaining,missing,Program.advancePeptide (peptide.1,[]) peptide.2,
      Program.compile_final_attached_word peptide,by simpa only [Program.compile,peptide,List.append_nil] using finalInventory⟩

/-- Actual DNA selects a shorter program until the intended second guide action is paid. -/
theorem actual_cut_program_control :
    continuedPlan ⟨true,true,true⟩ 1 0 = some (Program.compile uncorrectedPeptide) ∧
    continuedPlan ⟨true,true,true⟩ 1 1 = some (Program.compile correctedPeptide) ∧
    continuedPlan ⟨true,false,false⟩ 100 100 = some (Program.compile uncorrectedPeptide) ∧
    continuedPlan ⟨false,true,false⟩ 0 1 = some (Program.compile correctedPeptide) := by
  constructor
  · rw [actual_plan_generated]
    exact rfl
  constructor
  · rw [actual_plan_generated]
    exact rfl
  constructor
  · rw [actual_plan_generated]
    exact rfl
  · rw [actual_plan_generated]
    exact rfl

/-- Loaded initiation and termination remain declared boundaries on the generated plan. -/
theorem actual_plan_boundaries (edits : Target.Edits) (water additional : Nat) :
    let peptide := selectedPeptide edits water additional
    (Program.compile peptide).loadedInitiatorBoundary.required = [.aaTRNA peptide.1] ∧
    (Program.compile peptide).loadedInitiatorBoundary.loaded = [.peptidyl (peptide.1,[])] ∧
    (Program.compile peptide).terminationBoundary.required = [.peptidyl peptide] :=
  Program.compile_boundaries _

structure EndogenousTranslationContract : Prop where
  generatedPeptide : type_of% actual_peptide_generated
  generatedPlan : type_of% actual_plan_generated
  lengths : type_of% endogenous_lengths
  printedRecognition : type_of% printed_reference_recognized
  resources : type_of% actual_plan_resources
  chargingNative : type_of% source_charging_native
  elongationNative : type_of% source_elongation_native
  boundaries : type_of% actual_plan_boundaries

theorem sourceGeneratedEndogenousTranslation : EndogenousTranslationContract :=
  ⟨actual_peptide_generated,actual_plan_generated,endogenous_lengths,
    printed_reference_recognized,actual_plan_resources,source_charging_native,
    source_elongation_native,actual_plan_boundaries⟩

end CPS1EndogenousTranslation
