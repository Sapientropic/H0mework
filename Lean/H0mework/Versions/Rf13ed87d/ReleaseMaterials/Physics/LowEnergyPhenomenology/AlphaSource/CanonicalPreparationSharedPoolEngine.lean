import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSharedPoolArena

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSharedPool
open PreparationVacuumDAGCoefficient PreparationVacuumEngineSource PreparationVacuumCanonicalMoyal
open scoped BigOperators

abbrev RawAngle := Fin 3 → ℕ
abbrev RawAngular := List (RawAngle × ℕ)
abbrev RawSeries := List RawAngular
abbrev AngularAction := RawArena → RawAngular × RawArena
abbrev SeriesAction := RawArena → RawSeries × RawArena

def angleZero : RawAngle := fun _=>0
def angleUnit (axis : Fin 3) : RawAngle := fun j=>if j=axis then 1 else 0

def angularLookup (key : RawAngle) (rows : RawAngular) : ℕ := by
  classical
  exact (rows.find? (fun row=>row.1=key)).map Prod.snd |>.getD 0

def angularInsert (key : RawAngle) (value : ℕ) (rows : RawAngular) : RawAngular := by
  classical
  exact List.rec (motive:=fun _=>RawAngular) [(key,value)]
    (fun head tail next=>if head.1=key then (key,value)::tail else head::next) rows

def angularNonzero (rows : RawAngular) : RawAngular := rows.filter (fun row=>row.2≠0)

def angularConstant (id : ℕ) : RawAngular := if id=0 then [] else [(angleZero,id)]

def angularAdd (polynomials : List RawAngular) : AngularAction := fun state=>
  let result:=(polynomials.flatten).foldl (fun (out : RawAngular × RawArena) row=>
    let added:=rawAdd [angularLookup row.1 out.1,row.2] out.2
    (angularInsert row.1 added.1 out.1,added.2)) ([],state)
  (angularNonzero result.1,result.2)

def angularScale (coefficient : NormalizedCoefficient) (polynomial : RawAngular) : AngularAction := fun state=>
  polynomial.foldl (fun (out : RawAngular × RawArena) row=>
    let tested:=rawScale coefficient row.2 out.2
    if tested.1=0 then (out.1,tested.2) else
      let value:=rawScale coefficient row.2 tested.2
      (out.1++[(row.1,value.1)],value.2)) ([],state)

def angularShift (polynomial : RawAngular) (shift : RawAngle) : RawAngular :=
  polynomial.map (fun row=>(row.1+shift,row.2))

def angularSequence (actions : List AngularAction) : RawArena → List RawAngular × RawArena :=
  List.rec (motive:=fun _=>RawArena → List RawAngular × RawArena)
    (fun state=>([],state)) (fun action _ rest state=>
      let one:=action state
      let next:=rest one.2
      (one.1::next.1,next.2)) actions

def rawMoment (key : RawAngle) : ℚ :=
  if ∀ j,Even (key j) then
    (∏ j : Fin 3,((key j-1).doubleFactorial : ℚ))/
      (((∑ j : Fin 3,key j)+1).doubleFactorial : ℚ)/((∑ j : Fin 3,key j)+2)
  else 0

def angularAverage (polynomial : RawAngular) : RawAction := fun state=>
  let rows:=polynomial.filter (fun row=>∀ j,Even (row.1 j))
  let scaled:=rawSequence (rows.map (fun row=>rawScale (polynomialCoefficient (MvPolynomial.C (rawMoment row.1))) row.2)) state
  rawAdd scaled.1 scaled.2

-- The source factory allocates both lower degrees before applying the depth cut.
def originalSource (depth : ℕ) (slot : Fin 13) : SeriesAction := fun state=>
  let principal:=if slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9) then
    rawScalar (principalCoefficient slot) state else (0,state)
  let first:=rawAtom (.source 1 (Fin.castSucc slot)) false principal.2
  let lower:=rawAtom (.source 0 (Fin.castSucc slot)) false first.2
  let lower:=if slot=0 then
    let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    rawAdd [lower.1,extra.1] extra.2 else lower
  let terms:=[angularConstant principal.1,[(angleZero,first.1)],[(angleZero,lower.1)]]
  (terms.take (depth+1)++List.replicate (depth-2) [],lower.2)

def originalTrace (depth : ℕ) : SeriesAction := fun state=>
  let four:=originalSource depth 4 state
  let five:=originalSource depth 5 four.2
  let six:=originalSource depth 6 five.2
  angularSequence ((List.range (depth+1)).map (fun k=>
    angularAdd [four.1.getD k [],five.1.getD k [],six.1.getD k []])) six.2

structure RawSetup where
  depth : ℕ
  jclocks : Fin 4 → RawSeries
  ellclock : RawSeries

-- Lookup is finite data: absent higher coefficients are Arena.zero.
abbrev RawClocks := List ((ℕ × Fin 4) × ℕ)

def clockLookup (clocks : RawClocks) (level : ℕ) (axis : Fin 4) : ℕ :=
  ((clocks.find? (fun row=>row.1=(level,axis))).map Prod.snd).getD 0

def clockInsert (clocks : RawClocks) (level : ℕ) (axis : Fin 4) (id : ℕ) : RawClocks :=
  ((level,axis),id)::clocks.filter (fun row=>row.1≠(level,axis))

def originalSetup (depth : ℕ) (clocks : RawClocks) (state : RawArena) : RawSetup × RawArena :=
  let js:=fun a : Fin 4=>(List.range (depth+1)).map (fun k=>angularConstant (clockLookup clocks k a))
  let ell:=angularSequence ((List.range (depth+1)).map (fun k=>angularAdd
    [ (js 0).getD k [], angularShift ((js 1).getD k []) (angleUnit 0),
      angularShift ((js 2).getD k []) (angleUnit 1),angularShift ((js 3).getD k []) (angleUnit 2)])) state
  (⟨depth,js,ell.1⟩,ell.2)


-- These are exactly the memo scopes of Arena and Engine.setup: Moyal survives
-- setup, while R/J/word caches are reset after the new clock setup is built.
abbrev SeriesKey := List (List ((ℕ × ℕ × ℕ) × ℕ))
def seriesEntryWord (entry : (ℕ × ℕ × ℕ) × ℕ) : List ℕ :=
  [entry.1.1,entry.1.2.1,entry.1.2.2,entry.2]

def seriesKey (series : RawSeries) : SeriesKey :=
  series.map (fun polynomial=>(polynomial.map (fun row=>((row.1 0,row.1 1,row.1 2),row.2))).mergeSort
    (fun a b=>decide (List.Lex (· < ·) (seriesEntryWord a) (seriesEntryWord b) ∨ seriesEntryWord a=seriesEntryWord b)))

structure RawRuntime where
  arena : RawArena
  moyalMemo : List ((ℕ × ℕ × ℕ) × ℕ) := []
  rMemo : List (SeriesKey × RawSeries) := []
  jMemo : List ((Fin 4 × SeriesKey) × RawSeries) := []
  wordMemo : List ((List Token × SeriesKey) × RawSeries) := []

abbrev RuntimeAction (α : Type) := RawRuntime → α × RawRuntime

def memoLookup {κ α : Type} [DecidableEq κ] (key : κ) (entries : List (κ × α)) : Option α :=
  (entries.find? (fun entry=>entry.1=key)).map Prod.snd

def runArena (action : RawAction) : RuntimeAction ℕ := fun runtime=>
  let result:=action runtime.arena
  (result.1,{runtime with arena:=result.2})

def runAngular (action : AngularAction) : RuntimeAction RawAngular := fun runtime=>
  let result:=action runtime.arena
  (result.1,{runtime with arena:=result.2})

def runtimeSequence {α : Type} (actions : List (RuntimeAction α)) : RuntimeAction (List α) :=
  List.rec (motive:=fun _=>RuntimeAction (List α)) (fun runtime=>([],runtime))
    (fun action _ rest runtime=>let first:=action runtime;let next:=rest first.2;(first.1::next.1,next.2)) actions

def cacheMoyalResult (key : ℕ × ℕ × ℕ) (result : ℕ × RawRuntime) : ℕ × RawRuntime :=
  (result.1,{result.2 with moyalMemo:=(key,result.1)::result.2.moyalMemo})

def memoPair (r left right : ℕ) : RuntimeAction ℕ := fun runtime=>
  match memoLookup (r,left,right) runtime.moyalMemo with
  | some id=>(id,runtime)
  | none=>cacheMoyalResult (r,left,right)
      (if left=0 ∨ right=0 then (0,runtime) else runArena (rawPair r left right) runtime)

def memoMoyal (r left right : ℕ) : RuntimeAction ℕ := fun runtime=>
  match memoLookup (r,left,right) runtime.moyalMemo with
  | some id=>(id,runtime)
  | none=>
    let result:=if r=0 then runArena (rawMultiply left right) runtime else
      if left=0 ∨ right=0 then (0,runtime) else
        let ls:=rawRows runtime.arena left
        let rs:=rawRows runtime.arena right
        if ls.length > 1 ∨ rs.length > 1 then
          let actions:=ls.flatMap (fun a=>rs.map (fun b=>fun current=>
            let one:=runArena (rawPoly [a]) current
            let two:=runArena (rawPoly [b]) one.2
            memoPair r one.1 two.1 two.2))
          let expanded:=runtimeSequence actions runtime
          runArena (rawAdd expanded.1) expanded.2
        else runArena (rawPair r left right) runtime
    cacheMoyalResult (r,left,right) result

def memoJordan (r left right : ℕ) : RuntimeAction ℕ := fun runtime=>
  let one:=memoMoyal r left right runtime
  let two:=memoMoyal r right left one.2
  let added:=runArena (rawAdd [one.1,two.1]) two.2
  runArena (rawScale (polynomialCoefficient (MvPolynomial.C (1/2))) added.1) added.2

def runtimeWeighted (r : ℕ) (left right : RawAngular) : RuntimeAction RawAngular := fun runtime=>
  let pairs:=left.flatMap (fun a=>right.map (fun b=>(a,b)))
  let result:=pairs.foldl (fun (out : RawAngular × RawRuntime) pair=>
    let key:=pair.1.1+pair.2.1
    let product:=memoJordan r pair.1.2 pair.2.2 out.2
    let added:=runArena (rawAdd [angularLookup key out.1,product.1]) product.2
    (angularInsert key added.1 out.1,added.2)) ([],runtime)
  (angularNonzero result.1,result.2)

def runtimeSetup (depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) : RawSetup × RawRuntime :=
  let result:=originalSetup depth clocks runtime.arena
  (result.1,{runtime with arena:=result.2,rMemo:=[],jMemo:=[],wordMemo:=[]})

def originalJS (setup : RawSetup) (axis : Fin 4) (input : RawSeries) : RuntimeAction RawSeries := fun runtime=>by
  classical
  let key:=(axis,seriesKey input)
  exact match memoLookup key runtime.jMemo with
  | some result=>(result,runtime)
  | none=>
    let result:=runtimeSequence ((List.range (setup.depth+1)).map (fun k=>fun current=>
      let summands:=(List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).map (fun j=>
        runtimeWeighted (k-i-j) ((setup.jclocks axis).getD i []) (input.getD j [])))
      let generated:=runtimeSequence summands current
      runAngular (angularAdd generated.1) generated.2)) runtime
    (result.1,{result.2 with jMemo:=(key,result.1)::result.2.jMemo})

def originalResolvent (setup : RawSetup) (input : RawSeries) : RuntimeAction RawSeries := fun runtime=>
  let key:=seriesKey input
  match memoLookup key runtime.rMemo with
  | some result=>(result,runtime)
  | none=>
    let result:=(List.range (setup.depth+1)).foldl (fun (out : RawSeries × RawRuntime) k=>
      let lower:=(List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).filterMap (fun j=>
        if i=0 ∧ k-i-j=0 then none else
          some (runtimeWeighted (k-i-j) (setup.ellclock.getD i []) (out.1.getD j []))))
      let generated:=runtimeSequence lower out.2
      let summed:=runAngular (angularAdd generated.1) generated.2
      let negated:=runAngular (angularScale (polynomialCoefficient (-1)) summed.1) summed.2
      let residual:=runAngular (angularAdd [input.getD k [],negated.1]) negated.2
      let answer:=runAngular (angularScale (inversePoleCoefficient 0) residual.1) residual.2
      (out.1++[answer.1],answer.2)) ([],runtime)
    (result.1,{result.2 with rMemo:=(key,result.1)::result.2.rMemo})

def originalWord (setup : RawSetup) (tokens : List Token) (input : RawSeries) : RuntimeAction RawSeries := fun runtime=>by
  classical
  let key:=(tokens,seriesKey input)
  exact match memoLookup key runtime.wordMemo with
  | some result=>(result,runtime)
  | none=>
    let result:=tokens.reverse.foldl (fun (out : RawSeries × RawRuntime) token=>
      match token with
      | .inverse=>originalResolvent setup out.1 out.2
      | .jordan a=>originalJS setup a out.1 out.2) (input,runtime)
    (result.1,{result.2 with wordMemo:=(key,result.1)::result.2.wordMemo})


structure RawTemporalTerm where
  exponent : RawAngle
  tokens : List Token
  coefficient : ℚ

def temporalWord (a b : Fin 4) : List Token := [.inverse,.jordan a,.inverse,.jordan b,.inverse]

def rawTemporalTable (a b : Fin 4) (equation : Option (Fin 4)) : List RawTemporalTerm :=
  let base:=if a=b then [(temporalWord a b,(2 : ℚ))] else [(temporalWord a b,1),(temporalWord b a,1)]
  match equation with
  | none=>base.map (fun row=>⟨angleZero,row.1,row.2⟩)
  | some axis=>base.flatMap (fun row=>row.1.zipIdx.filterMap (fun token=>
      match token.1 with
      | .inverse=>some ⟨Fin.cases angleZero (fun i=>angleUnit i) axis,
          row.1.take token.2++[.inverse,.inverse]++row.1.drop (token.2+1),row.2⟩
      | .jordan a=>if a=axis then some ⟨angleZero,row.1.take token.2++row.1.drop (token.2+1),-row.2⟩ else none))

def originalApplyT (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4)) :
    RuntimeAction (List ℕ) := fun runtime=>
  let result:=(rawTemporalTable a b equation).foldl (fun (out : RawSeries × RawRuntime) term=>
    let operated:=originalWord setup term.tokens input out.2
    (List.range (setup.depth+1)).foldl (fun (acc : RawSeries × RawRuntime) k=>
      let scaled:=runAngular (angularScale (polynomialCoefficient (MvPolynomial.C term.coefficient))
        (angularShift (operated.1.getD k []) term.exponent)) acc.2
      let added:=runAngular (angularAdd [acc.1.getD k [],scaled.1]) scaled.2
      (acc.1.set k added.1,added.2)) (out.1,operated.2))
    (List.replicate (setup.depth+1) [],runtime)
  runtimeSequence (result.1.map (fun row=>runArena (angularAverage row))) result.2

def runtimeSource (depth : ℕ) (slot : Fin 13) : RuntimeAction RawSeries := fun runtime=>
  let result:=originalSource depth slot runtime.arena
  (result.1,{runtime with arena:=result.2})

def runtimeTrace (depth : ℕ) : RuntimeAction RawSeries := fun runtime=>
  let result:=originalTrace depth runtime.arena
  (result.1,{runtime with arena:=result.2})

def originalAffine (setup : RawSetup) (equation : Option (Fin 4)) : RuntimeAction (List ℕ) := fun runtime=>
  match equation with
  | none=>
    let affine:=runtimeSequence ((List.finRange 4).map (fun a=>fun current=>
      let source:=runtimeSource setup.depth (Fin.castAdd 9 a) current
      originalJS setup a source.1 source.2)) runtime
    runtimeSequence ((List.range (setup.depth+1)).map (fun k=>runArena (rawAdd
      (affine.1.map (fun row=>angularLookup angleZero (row.getD k [])))))) affine.2
  | some a=>
    let source:=runtimeSource setup.depth (Fin.castAdd 9 a) runtime
    runtimeSequence (source.1.map (fun row=>runArena (rawScale (polynomialCoefficient (-1)) (angularLookup angleZero row)))) source.2

def originalForceOrEnergy (setup : RawSetup) (equation : Option (Fin 4)) : RuntimeAction (List ℕ) := fun runtime=>
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  let diagonal:=runtimeSequence ((List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)) first.2
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let cross:=runtimeSequence (crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)) diagonal.2
  let time:=runtimeSequence ((List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)) cross.2
  let terms : List (ℚ × List ℕ):=[(1/2,first.1)]++diagonal.1.map (fun row=>(-1/2,row))++
    cross.1.map (fun row=>(-1,row))++time.1.map (fun row=>(-1,row))
  runtimeSequence ((List.range (setup.depth+1)).map (fun k=>fun current=>
    let scaled:=runtimeSequence (terms.map (fun row=>runArena
      (rawScale (polynomialCoefficient (MvPolynomial.C row.1)) (row.2.getD k 0)))) current
    runArena (rawAdd ((affine.1.getD k 0)::scaled.1)) scaled.2)) time.2


structure RawStageRecord where
  order : ℕ
  residuals : List ℕ
  correctedForces : List ℕ
  clockAtoms : List ℕ
  clockDefinitions : List ℕ
  energy : ℕ
  correctionChecks : List Bool
  newestExcluded : Bool

structure RawEngineState where
  runtime : RawRuntime
  clocks : RawClocks
  definitions : RawClocks
  leadingEnergy : ℕ
  leadingChecks : List Bool
  stages : List RawStageRecord

def originalBoot (clocks : RawClocks) (runtime : RawRuntime) : RawEngineState :=
  let setup:=runtimeSetup 0 clocks runtime
  let forces:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))) setup.2
  let leading:=originalForceOrEnergy setup.1 none forces.2
  ⟨leading.2,clocks,[],leading.1.getD 0 0,forces.1.map (fun row=>decide (row.getD 0 0=0)),[]⟩

def originalEngineInitial : RawEngineState :=
  let seeded:=runArena (rawScalar (polynomialCoefficient (MvPolynomial.X 0))) ⟨rawInitial,[],[],[],[]⟩
  originalBoot [((0,0),seeded.1)] seeded.2


def jacobianCoefficient (a b : Fin 4) : NormalizedCoefficient :=
  Fin.cases (Fin.cases ⟨-MvPolynomial.X 1,![3,0,0]⟩ (fun _=>polynomialCoefficient 0))
    (fun i=>Fin.cases (polynomialCoefficient 0) (fun j=>⟨-centralQ i j,![3,0,0]⟩)) a b

def originalInstall (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    RawClocks × List ℕ × List ℕ × RawRuntime :=
  (List.finRange 4).foldl
    (fun (out : RawClocks × List ℕ × List ℕ × RawRuntime) a=>
      let atom:=runArena (rawAtom (.clock k a) false) out.2.2.2
      let clocks:=clockInsert out.1 (k+1) a atom.1
      let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
        (rawScale (correctionCoefficient a b) (residualIds.getD b.val 0)))) atom.2
      let definition:=runArena (rawAdd scaled.1) scaled.2
      (clocks,out.2.1++[atom.1],out.2.2.1++[definition.1],definition.2))
    (clocks,[],[],runtime)

def originalChecks (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ) (runtime : RawRuntime) :
    List ℕ × List Bool × RawRuntime :=
  (List.finRange 4).foldl
    (fun (out : List ℕ × List Bool × RawRuntime) a=>
      let result:=originalForceOrEnergy setup (some a) out.2.2
      let new:=result.1.getD order 0
      let scaled:=runtimeSequence ((List.finRange 4).map (fun b=>runArena
        (rawScale (jacobianCoefficient a b) (clockIds.getD b.val 0)))) result.2
      let expected:=runArena (rawAdd ((residualIds.getD a.val 0)::scaled.1)) scaled.2
      (out.1++[new],out.2.1++[decide (new=expected.1)],expected.2)) ([],[],runtime)

-- The original loop creates each clock atom before its definition, then runs
-- corrected forces and their expected-J expressions before the energy request.
def originalEngineNext (k : ℕ) (engine : RawEngineState) : RawEngineState :=
  let order:=k+1
  let before:=runtimeSetup order engine.clocks engine.runtime
  let residuals:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2
  let residualIds:=residuals.1.map (fun row=>row.getD order 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let clocks:=installed.1
  let clockIds:=installed.2.1
  let definitionIds:=installed.2.2.1
  let after:=runtimeSetup order clocks installed.2.2.2
  let checked:=originalChecks after.1 order residualIds clockIds after.2
  let energy:=originalForceOrEnergy after.1 none checked.2.2
  let energyId:=energy.1.getD order 0
  let clockNodes:=clockIds.map (fun id=>((rawRows energy.2.arena id).getD 0 ⟨polynomialCoefficient 0,[]⟩).word.getD 0 0)
  let excluded:=(rawRows energy.2.arena energyId).all (fun row=>row.word.all (fun node=> !clockNodes.contains node))
  let definitions:=(List.finRange 4).foldl (fun defs a=>clockInsert defs order a (definitionIds.getD a.val 0)) engine.definitions
  let record : RawStageRecord:=⟨order,residualIds,checked.1,clockIds,definitionIds,energyId,checked.2.1,excluded⟩
  { runtime:=energy.2,clocks:=clocks,definitions:=definitions,leadingEnergy:=engine.leadingEnergy,
    leadingChecks:=engine.leadingChecks,stages:=engine.stages++[record] }

def originalEngine (order : ℕ) : RawEngineState :=
  Nat.rec originalEngineInitial (fun k previous=>originalEngineNext k previous) order


private theorem rawFold_grows {α β : Type} (items : List α) (step : β × RawArena → α → β × RawArena)
    (grows : ∀ out i,RawExtends out.2 (step out i).2) (initial : β × RawArena) :
    RawExtends initial.2 (items.foldl step initial).2 := by
  induction items generalizing initial with
  | nil=>exact RawExtends.refl _
  | cons i items ih=>exact (grows initial i).trans (ih (step initial i))

theorem angularAdd_grows (polynomials : List RawAngular) (state : RawArena) : RawExtends state (angularAdd polynomials state).2 := by
  dsimp only [angularAdd]
  refine rawFold_grows (β:=RawAngular) _ _ ?_ ([],state)
  intro out row
  exact rawAdd_extends _ _

theorem angularScale_grows (c : NormalizedCoefficient) (polynomial : RawAngular) (state : RawArena) :
    RawExtends state (angularScale c polynomial state).2 := by
  dsimp only [angularScale]
  refine rawFold_grows (β:=RawAngular) _ _ ?_ ([],state)
  intro out row
  split_ifs
  · exact rawScale_extends _ _ _
  · exact (rawScale_extends _ _ _).trans (rawScale_extends _ _ _)

theorem angularSequence_grows (actions : List AngularAction)
    (grows : ∀ action,action∈actions → ∀ state,RawExtends state (action state).2) (state : RawArena) :
    RawExtends state (angularSequence actions state).2 := by
  induction actions generalizing state with
  | nil=>exact RawExtends.refl _
  | cons action actions ih=>
    exact (grows action (by simp) state).trans (ih (fun a h=>grows a (by simp [h])) (action state).2)

theorem angularAverage_grows (polynomial : RawAngular) (state : RawArena) :
    RawExtends state (angularAverage polynomial state).2 := by
  apply RawExtends.trans (rawSequence_extends _ ?_ state)
  · exact rawAdd_extends _ _
  · intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _

theorem originalSource_grows (depth : ℕ) (slot : Fin 13) (state : RawArena) :
    RawExtends state (originalSource depth slot state).2 := by
  let principal := if slot.val=0 ∨ (4 ≤ slot.val ∧ slot.val ≤ 9) then
    rawScalar (principalCoefficient slot) state else (0,state)
  have hp : RawExtends state principal.2 := by
    dsimp only [principal]
    split_ifs
    · exact rawScalar_extends _ _
    · exact RawExtends.refl _
  let first := rawAtom (.source 1 (Fin.castSucc slot)) false principal.2
  let lower := rawAtom (.source 0 (Fin.castSucc slot)) false first.2
  have hl : RawExtends state lower.2 :=
    (hp.trans (rawAtom_extends _ _ _)).trans (rawAtom_extends _ _ _)
  change RawExtends state (if slot=0 then
    let extra:=rawAtom (.source 0 (Fin.last 13)) false lower.2
    rawAdd [lower.1,extra.1] extra.2 else lower).2
  split_ifs
  · exact (hl.trans (rawAtom_extends _ _ _)).trans (rawAdd_extends _ _)
  · exact hl

theorem originalTrace_grows (depth : ℕ) (state : RawArena) : RawExtends state (originalTrace depth state).2 := by
  apply RawExtends.trans (((originalSource_grows _ _ _).trans (originalSource_grows _ _ _)).trans (originalSource_grows _ _ _))
  apply angularSequence_grows
  intro action member current
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  exact angularAdd_grows _ _

theorem originalSetup_grows (depth : ℕ) (clocks : RawClocks) (state : RawArena) :
    RawExtends state (originalSetup depth clocks state).2 := by
  apply angularSequence_grows
  intro action member current
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  exact angularAdd_grows _ _

def RuntimeGrows {α : Type} (action : RuntimeAction α) : Prop :=
  ∀ runtime,RawExtends runtime.arena (action runtime).2.arena

theorem runArena_grows (action : RawAction) (grows : ∀ state,RawExtends state (action state).2) : RuntimeGrows (runArena action) :=
  fun runtime=>grows runtime.arena

theorem runAngular_grows (action : AngularAction) (grows : ∀ state,RawExtends state (action state).2) : RuntimeGrows (runAngular action) :=
  fun runtime=>grows runtime.arena

theorem runtimeSequence_grows {α : Type} (actions : List (RuntimeAction α))
    (grows : ∀ action,action∈actions → RuntimeGrows action) : RuntimeGrows (runtimeSequence actions) := by
  intro runtime
  induction actions generalizing runtime with
  | nil=>exact RawExtends.refl _
  | cons action actions ih=>
    exact (grows action (by simp) runtime).trans (ih (fun a h=>grows a (by simp [h])) (action runtime).2)

private theorem runtimeFold_grows {α β : Type} (items : List α)
    (step : β × RawRuntime → α → β × RawRuntime)
    (grows : ∀ out i,RawExtends out.2.arena (step out i).2.arena) (initial : β × RawRuntime) :
    RawExtends initial.2.arena (items.foldl step initial).2.arena := by
  induction items generalizing initial with
  | nil=>exact RawExtends.refl _
  | cons i items ih=>exact (grows initial i).trans (ih (step initial i))

theorem memoPair_grows (r left right : ℕ) : RuntimeGrows (memoPair r left right) := by
  intro runtime
  unfold memoPair
  split
  · exact RawExtends.refl _
  · dsimp only [cacheMoyalResult]
    split_ifs
    · exact RawExtends.refl _
    · exact rawPair_extends _ _ _ _

theorem memoMoyal_grows (r left right : ℕ) : RuntimeGrows (memoMoyal r left right) := by
  intro runtime
  unfold memoMoyal
  split
  · exact RawExtends.refl _
  · dsimp only [cacheMoyalResult]
    split_ifs
    · exact rawMultiply_extends _ _ _
    · exact RawExtends.refl _
    · apply RawExtends.trans (runtimeSequence_grows _ ?_ runtime)
      · exact rawAdd_extends _ _
      · intro action member current
        obtain ⟨a,_,ha⟩:=List.mem_flatMap.mp member
        obtain ⟨b,_,rfl⟩:=List.mem_map.mp ha
        let first := runArena (rawPoly [a]) current
        let second := runArena (rawPoly [b]) first.2
        exact ((rawPoly_extends [a] current.arena).trans (rawPoly_extends [b] first.2.arena)).trans
          (memoPair_grows r first.1 second.1 second.2)
    · exact rawPair_extends _ _ _ _

theorem memoJordan_grows (r left right : ℕ) : RuntimeGrows (memoJordan r left right) := by
  intro runtime
  exact (((memoMoyal_grows _ _ _ _).trans (memoMoyal_grows _ _ _ _)).trans (rawAdd_extends _ _)).trans (rawScale_extends _ _ _)

theorem runtimeWeighted_grows (r : ℕ) (left right : RawAngular) : RuntimeGrows (runtimeWeighted r left right) := by
  intro runtime
  dsimp only [runtimeWeighted]
  refine runtimeFold_grows (β:=RawAngular) _ _ ?_ ([],runtime)
  intro out pair
  exact (memoJordan_grows _ _ _ _).trans (rawAdd_extends _ _)

theorem runtimeSetup_grows (depth : ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    RawExtends runtime.arena (runtimeSetup depth clocks runtime).2.arena := originalSetup_grows _ _ _


theorem originalJS_grows (setup : RawSetup) (axis : Fin 4) (input : RawSeries) : RuntimeGrows (originalJS setup axis input) := by
  intro runtime
  dsimp only [originalJS]
  split
  · exact RawExtends.refl _
  · apply runtimeSequence_grows
    intro action member current
    obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
    apply RawExtends.trans (runtimeSequence_grows _ ?_ current)
    · exact angularAdd_grows _ _
    · intro action member current
      obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
      obtain ⟨j,_,rfl⟩:=List.mem_map.mp hi
      exact runtimeWeighted_grows _ _ _ current

theorem originalResolvent_grows (setup : RawSetup) (input : RawSeries) : RuntimeGrows (originalResolvent setup input) := by
  intro runtime
  dsimp only [originalResolvent]
  split
  · exact RawExtends.refl _
  · refine runtimeFold_grows (β:=RawSeries) _ _ ?_ ([],runtime)
    intro out k
    have hg : RawExtends out.2.arena
        (runtimeSequence ((List.range (k+1)).flatMap (fun i=>(List.range (k+1-i)).filterMap (fun j=>
          if i=0 ∧ k-i-j=0 then none else
            some (runtimeWeighted (k-i-j) (setup.ellclock.getD i []) (out.1.getD j []))))) out.2).2.arena := by
      apply runtimeSequence_grows
      intro action member current
      obtain ⟨i,_,hi⟩:=List.mem_flatMap.mp member
      obtain ⟨j,_,hj⟩:=List.mem_filterMap.mp hi
      split_ifs at hj
      cases hj
      exact runtimeWeighted_grows _ _ _ current
    exact (((hg.trans (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)).trans
      (angularAdd_grows _ _)).trans (angularScale_grows _ _ _)

theorem originalWord_grows (setup : RawSetup) (tokens : List Token) (input : RawSeries) :
    RuntimeGrows (originalWord setup tokens input) := by
  intro runtime
  dsimp only [originalWord]
  split
  · exact RawExtends.refl _
  · refine runtimeFold_grows (β:=RawSeries) _ _ ?_ (input,runtime)
    intro out token
    cases token with
    | inverse=>exact originalResolvent_grows _ _ out.2
    | jordan a=>exact originalJS_grows _ _ _ out.2

theorem originalApplyT_grows (setup : RawSetup) (a b : Fin 4) (input : RawSeries) (equation : Option (Fin 4)) :
    RuntimeGrows (originalApplyT setup a b input equation) := by
  intro runtime
  unfold originalApplyT
  apply RawExtends.trans (runtimeFold_grows (β:=RawSeries) _ _ ?_ (List.replicate (setup.depth+1) [],runtime))
  · apply runtimeSequence_grows
    intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact angularAverage_grows _ _
  · intro out term
    apply RawExtends.trans (originalWord_grows setup term.tokens input out.2)
    refine runtimeFold_grows (β:=RawSeries) _ _ ?_ (out.1,(originalWord setup term.tokens input out.2).2)
    intro acc k
    exact (angularScale_grows _ _ _).trans (angularAdd_grows _ _)

theorem runtimeSource_grows (depth : ℕ) (slot : Fin 13) : RuntimeGrows (runtimeSource depth slot) :=
  fun runtime=>originalSource_grows depth slot runtime.arena

theorem runtimeTrace_grows (depth : ℕ) : RuntimeGrows (runtimeTrace depth) :=
  fun runtime=>originalTrace_grows depth runtime.arena

theorem originalAffine_grows (setup : RawSetup) (equation : Option (Fin 4)) : RuntimeGrows (originalAffine setup equation) := by
  intro runtime
  cases equation with
  | none=>
    apply RawExtends.trans (runtimeSequence_grows _ ?_ runtime)
    · apply runtimeSequence_grows
      intro action member current
      obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
      exact rawAdd_extends _ _
    · intro action member current
      obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
      exact (runtimeSource_grows _ _ current).trans
        (originalJS_grows setup a _ (runtimeSource setup.depth (Fin.castAdd 9 a) current).2)
  | some a=>
    apply RawExtends.trans (runtimeSource_grows setup.depth (Fin.castAdd 9 a) runtime)
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _


theorem originalForceOrEnergy_grows (setup : RawSetup) (equation : Option (Fin 4)) :
    RuntimeGrows (originalForceOrEnergy setup equation) := by
  intro runtime
  let affine:=originalAffine setup equation runtime
  let trace:=runtimeTrace setup.depth affine.2
  let first:=originalApplyT setup 0 0 trace.1 equation trace.2
  have hf : RawExtends runtime.arena first.2.arena :=
    ((originalAffine_grows setup equation runtime).trans (runtimeTrace_grows setup.depth affine.2)).trans
      (originalApplyT_grows setup 0 0 trace.1 equation trace.2)
  let diagonalActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨4+i.val,by omega⟩ current
    originalApplyT setup (Fin.succ i) (Fin.succ i) source.1 equation source.2)
  let diagonal:=runtimeSequence diagonalActions first.2
  have hd : RawExtends first.2.arena diagonal.2.arena := by
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth ⟨4+i.val,by omega⟩ current).trans
      (originalApplyT_grows setup (Fin.succ i) (Fin.succ i) _ equation
        (runtimeSource setup.depth ⟨4+i.val,by omega⟩ current).2)
  let crossIndices : List (Fin 4 × Fin 4 × Fin 13):=[(1,2,7),(1,3,8),(2,3,9)]
  let crossActions : List (RuntimeAction (List ℕ)) := crossIndices.map (fun entry=>fun current=>
    let source:=runtimeSource setup.depth entry.2.2 current
    originalApplyT setup entry.1 entry.2.1 source.1 equation source.2)
  let cross:=runtimeSequence crossActions diagonal.2
  have hc : RawExtends diagonal.2.arena cross.2.arena := by
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨entry,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth entry.2.2 current).trans
      (originalApplyT_grows setup entry.1 entry.2.1 _ equation (runtimeSource setup.depth entry.2.2 current).2)
  let timeActions : List (RuntimeAction (List ℕ)) := (List.finRange 3).map (fun i=>fun current=>
    let source:=runtimeSource setup.depth ⟨10+i.val,by omega⟩ current
    originalApplyT setup 0 (Fin.succ i) source.1 equation source.2)
  let time:=runtimeSequence timeActions cross.2
  have ht : RawExtends cross.2.arena time.2.arena := by
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp member
    exact (runtimeSource_grows setup.depth ⟨10+i.val,by omega⟩ current).trans
      (originalApplyT_grows setup 0 (Fin.succ i) _ equation (runtimeSource setup.depth ⟨10+i.val,by omega⟩ current).2)
  apply RawExtends.trans (((hf.trans hd).trans hc).trans ht)
  apply runtimeSequence_grows
  intro action member current
  obtain ⟨k,_,rfl⟩:=List.mem_map.mp member
  apply RawExtends.trans (runtimeSequence_grows _ ?_ current)
  · exact rawAdd_extends _ _
  · intro action member current
    obtain ⟨row,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _


private theorem projectedFold_grows {α β : Type} (projection : β → RawArena) (items : List α)
    (step : β → α → β) (grows : ∀ out i,RawExtends (projection out) (projection (step out i))) (initial : β) :
    RawExtends (projection initial) (projection (items.foldl step initial)) := by
  induction items generalizing initial with
  | nil=>exact RawExtends.refl _
  | cons i items ih=>exact (grows initial i).trans (ih (step initial i))

theorem originalInstall_grows (k : ℕ) (residualIds : List ℕ) (clocks : RawClocks) (runtime : RawRuntime) :
    RawExtends runtime.arena (originalInstall k residualIds clocks runtime).2.2.2.arena := by
  refine projectedFold_grows (fun out : RawClocks × List ℕ × List ℕ × RawRuntime=>out.2.2.2.arena)
    _ _ ?_ (clocks,[],[],runtime)
  intro out a
  apply RawExtends.trans (rawAtom_extends (.clock k a) false out.2.2.2.arena)
  apply RawExtends.trans (runtimeSequence_grows _ ?_ (runArena (rawAtom (.clock k a) false) out.2.2.2).2)
  · exact rawAdd_extends _ _
  · intro action member current
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _

theorem originalChecks_grows (setup : RawSetup) (order : ℕ) (residualIds clockIds : List ℕ) (runtime : RawRuntime) :
    RawExtends runtime.arena (originalChecks setup order residualIds clockIds runtime).2.2.arena := by
  refine projectedFold_grows (fun out : List ℕ × List Bool × RawRuntime=>out.2.2.arena)
    _ _ ?_ ([],[],runtime)
  intro out a
  apply RawExtends.trans (originalForceOrEnergy_grows setup (some a) out.2.2)
  apply RawExtends.trans (runtimeSequence_grows _ ?_ (originalForceOrEnergy setup (some a) out.2.2).2)
  · exact rawAdd_extends _ _
  · intro action member current
    obtain ⟨b,_,rfl⟩:=List.mem_map.mp member
    exact rawScale_extends _ _ _

theorem originalEngineNext_grows (k : ℕ) (engine : RawEngineState) :
    RawExtends engine.runtime.arena (originalEngineNext k engine).runtime.arena := by
  let before:=runtimeSetup (k+1) engine.clocks engine.runtime
  let residuals:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy before.1 (some a))) before.2
  let residualIds:=residuals.1.map (fun row=>row.getD (k+1) 0)
  let installed:=originalInstall k residualIds engine.clocks residuals.2
  let after:=runtimeSetup (k+1) installed.1 installed.2.2.2
  let checked:=originalChecks after.1 (k+1) residualIds installed.2.1 after.2
  have hr : RawExtends before.2.arena residuals.2.arena := by
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  exact (((((runtimeSetup_grows (k+1) engine.clocks engine.runtime).trans hr).trans (originalInstall_grows k residualIds engine.clocks residuals.2)).trans
    (runtimeSetup_grows (k+1) installed.1 installed.2.2.2)).trans (originalChecks_grows after.1 (k+1) residualIds installed.2.1 after.2)).trans
      (originalForceOrEnergy_grows after.1 none checked.2.2)

attribute [local irreducible] originalForceOrEnergy runtimeSequence runtimeSetup
set_option backward.isDefEq.respectTransparency true

theorem originalBoot_grows (clocks : RawClocks) (runtime : RawRuntime) :
    RawExtends runtime.arena (originalBoot clocks runtime).runtime.arena := by
  let setup:=runtimeSetup 0 clocks runtime
  let forces:=runtimeSequence ((List.finRange 4).map (fun a=>originalForceOrEnergy setup.1 (some a))) setup.2
  have hf : RawExtends setup.2.arena forces.2.arena := by
    apply runtimeSequence_grows
    intro action member current
    obtain ⟨a,_,rfl⟩:=List.mem_map.mp member
    exact originalForceOrEnergy_grows _ _ _
  change RawExtends runtime.arena (originalForceOrEnergy setup.1 none forces.2).2.arena
  exact ((runtimeSetup_grows 0 clocks runtime).trans hf).trans
    (originalForceOrEnergy_grows setup.1 none forces.2)

theorem originalEngine_initial_grows : RawExtends rawInitial originalEngineInitial.runtime.arena := by
  let seeded:=runArena (rawScalar (polynomialCoefficient (MvPolynomial.X 0))) ⟨rawInitial,[],[],[],[]⟩
  exact (rawScalar_extends (polynomialCoefficient (MvPolynomial.X 0)) rawInitial).trans
    (originalBoot_grows [((0,0),seeded.1)] seeded.2)

theorem originalEngine_extends {earlier later : ℕ} (h : earlier ≤ later) :
    RawExtends (originalEngine earlier).runtime.arena (originalEngine later).runtime.arena := by
  induction h with
  | refl=>exact RawExtends.refl _
  | step h ih=>exact ih.trans (originalEngineNext_grows _ _)

theorem originalEngine_initialized (order : ℕ) : RawInitialized (originalEngine order).runtime.arena :=
  originalEngine_initial_grows.trans (originalEngine_extends (Nat.zero_le order))


theorem originalEngine_rows_preserved {earlier later : ℕ} (h : earlier ≤ later)
    (id : ℕ) (valid : id < (originalEngine earlier).runtime.arena.polynomials.length) :
    rawRows (originalEngine later).runtime.arena id=rawRows (originalEngine earlier).runtime.arena id :=
  rawRows_preserved (originalEngine_extends h) id valid

theorem originalEngine_nodes_preserved {earlier later : ℕ} (h : earlier ≤ later)
    (id : ℕ) (valid : id < (originalEngine earlier).runtime.arena.nodes.length) :
    rawNode (originalEngine later).runtime.arena id=rawNode (originalEngine earlier).runtime.arena id :=
  rawNode_preserved (originalEngine_extends h) id valid

theorem originalEngineNext_stage_count (k : ℕ) (engine : RawEngineState) :
    (originalEngineNext k engine).stages.length=engine.stages.length+1 := by
  simp only [originalEngineNext,List.length_append,List.length_cons,List.length_nil]

theorem originalEngine_stage_count (order : ℕ) : (originalEngine order).stages.length=order := by
  induction order with
  | zero=>rfl
  | succ k ih=>exact (originalEngineNext_stage_count k (originalEngine k)).trans (congrArg (·+1) ih)

theorem originalEngineNext_stage_prefix (k : ℕ) (engine : RawEngineState) :
    engine.stages.IsPrefix (originalEngineNext k engine).stages := List.prefix_append _ _

theorem originalEngine_stage_prefix {earlier later : ℕ} (h : earlier ≤ later) :
    (originalEngine earlier).stages.IsPrefix (originalEngine later).stages := by
  induction h with
  | refl=>exact List.prefix_refl _
  | step h ih=>exact ih.trans (originalEngineNext_stage_prefix _ _)

theorem originalEngine_stage_preserved {earlier later : ℕ} (h : earlier ≤ later)
    (index : ℕ) (valid : index < earlier) (fallback : RawStageRecord) :
    (originalEngine later).stages.getD index fallback=(originalEngine earlier).stages.getD index fallback := by
  have old : index < (originalEngine earlier).stages.length := by simpa only [originalEngine_stage_count] using valid
  have new : index < (originalEngine later).stages.length :=
    lt_of_lt_of_le old (originalEngine_stage_prefix h).length_le
  rw [List.getD_eq_getElem _ _ new,List.getD_eq_getElem _ _ old]
  exact ((originalEngine_stage_prefix h).getElem old).symm


def originalStageRecord (k : ℕ) : RawStageRecord :=
  (originalEngine (k+1)).stages[k]'(by rw [originalEngine_stage_count]; omega)

def originalStageAt (order : ℕ) (k : Fin order) : RawStageRecord :=
  (originalEngine order).stages[k.val]'(by rw [originalEngine_stage_count]; exact k.isLt)

theorem originalStageAt_preserved (order : ℕ) (k : Fin order) :
    originalStageAt order k=originalStageRecord k.val := by
  exact ((originalEngine_stage_prefix (show k.val+1 ≤ order by omega)).getElem
    (show k.val < (originalEngine (k.val+1)).stages.length by rw [originalEngine_stage_count]; omega)).symm

-- Python stage returns definitions, not the clock atom handles.
def originalFiveId (k : ℕ) (i : Fin 5) : ℕ :=
  Fin.lastCases (originalStageRecord k).energy
    (fun a=>(originalStageRecord k).clockDefinitions.getD a.val 0) i

def originalFiveRows (k : ℕ) (i : Fin 5) : List RawRow :=
  rawRows (originalEngine (k+1)).runtime.arena (originalFiveId k i)

theorem originalFive_clock_definition (k : ℕ) (a : Fin 4) :
    originalFiveId k a.castSucc=(originalStageRecord k).clockDefinitions.getD a.val 0 := by
  simp only [originalFiveId,Fin.lastCases_castSucc]

theorem originalFive_energy (k : ℕ) : originalFiveId k (Fin.last 4)=(originalStageRecord k).energy := by
  simp only [originalFiveId,Fin.lastCases_last]

theorem originalFiveRows_at_later (k later : ℕ) (h : k+1 ≤ later) (i : Fin 5)
    (valid : originalFiveId k i < (originalEngine (k+1)).runtime.arena.polynomials.length) :
    rawRows (originalEngine later).runtime.arena (originalFiveId k i)=originalFiveRows k i :=
  originalEngine_rows_preserved h _ valid

end LowEnergy.PreparationVacuumSharedPool
