import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.IntegerEnergy.MidSector.Complete
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
namespace TopPopulation
open Propagation.Interface Contraction Load.Source
open scoped Matrix BigOperators MatrixOrder Matrix.Norms.L2Operator

abbrev HighIndex := LoadPrimitive.NativeIndex ⊕ LoadPrimitive.NativeIndex

def highRow : HighIndex → OrdinaryFull ⊕ OrdinaryFull
  | .inl ⟨body,e⟩ => .inl (.inr (body,1),e)
  | .inr ⟨body,e⟩ => .inr (.inr (body,1),e)

theorem highRow_injective : Function.Injective highRow := by
  rintro (⟨b,e⟩ | ⟨b,e⟩) (⟨c,f⟩ | ⟨c,f⟩) h <;> simp_all [highRow]

def selectedInt (T : IntTable 64 4) :=
  submatrix (fromTable T pointerFin pairFin) highRow id

def gramInt (T : IntTable 64 4) := multiply (adjoint (selectedInt T)) (selectedInt T)

def centered (G : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2)) :
    MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2) :=
  ⟨fun i j => G.re i j - (if i=j then scale else 0), G.im⟩

def squareSum (G : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2)) : Int :=
  ∑ i : Fin 2 × Fin 2, ∑ j : Fin 2 × Fin 2, ((centered G).re i j ^ 2 + (centered G).im i j ^ 2)

noncomputable section

theorem centered_value (G : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2)) :
    value (centered G) = value G - (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
  ext i j
  by_cases h : i=j
  · subst j
    simp [centered,value,raw,scale]
    ring
  · simp [centered,value,raw,scale,h]

theorem norm_from_square (G : MatrixInt (Fin 2 × Fin 2) (Fin 2 × Fin 2))
    (bound : squareSum G < (scale/10000)^2) :
    ‖value G - (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (1/10000 : ℝ) := by
  rw [← centered_value]
  have h := integer_operator_norm_bound (centered G) (scale/10000)
    (by norm_num [scale]) (le_of_lt bound)
  convert h using 1
  norm_num [scale]


theorem gram_norm_from_literal (T : IntTable 64 4) (G : IntTable 4 4)
    (source : toTable (gramInt T) pairFin pairFin = G)
    (bound : squareSum (fromTable G pairFin pairFin) < (scale/10000)^2) :
    ‖value (gramInt T) - (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (1/10000 : ℝ) := by
  have same : gramInt T = fromTable G pairFin pairFin := by
    rw [← from_to_table (gramInt T) pairFin pairFin, source]
  rw [same]
  exact norm_from_square _ bound
end

noncomputable section

def sourceHighInt (a b : Basis) (ordered : a < b) :=
  submatrix (chargedElevenInt a b ordered) highRow id

def sourceHigh (a b : Basis) (ordered : a < b) : Matrix HighIndex (Fin 2 × Fin 2) ℂ :=
  (qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)).submatrix highRow id

def sourceGram (a b : Basis) (ordered : a < b) :=
  (sourceHigh a b ordered)ᴴ * sourceHigh a b ordered

def sourceGramInt (a b : Basis) (ordered : a < b) :=
  multiply (adjoint (sourceHighInt a b ordered)) (sourceHighInt a b ordered)

theorem source_high_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceHighInt a b ordered) - sourceHigh a b ordered‖ ≤ (1/10^12 : ℝ) := by
  rw [sourceHighInt, value_submatrix, charged_eleven_original, sourceHigh]
  change ‖(value (sourceOrdinaryElevenSelectedInt a b ordered) -
    qvalue ((ordinaryElevenColumnsQ a b ordered).submatrix id chargedInjection)).submatrix highRow id‖ ≤ _
  exact (submatrix_rows_norm_le _ highRow highRow_injective).trans
    (source_ordinary_selected_errors a b ordered).2

theorem source_high_norm (a b : Basis) (ordered : a < b) :
    ‖sourceHigh a b ordered‖ ≤ (24 : ℝ) :=
  (submatrix_rows_norm_le _ highRow highRow_injective).trans
    (source_ordinary_selected_norms_24 a b ordered).2

theorem source_gram_error (a b : Basis) (ordered : a < b) :
    ‖value (sourceGramInt a b ordered) - sourceGram a b ordered‖ ≤ (1/10^10 : ℝ) := by
  have adj : ‖value (adjoint (sourceHighInt a b ordered)) - (sourceHigh a b ordered)ᴴ‖ ≤
      (1/10^12 : ℝ) := by
    simpa only [value_adjoint, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose] using
      source_high_error a b ordered
  have adjNorm : ‖(sourceHigh a b ordered)ᴴ‖ ≤ (24 : ℝ) := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using source_high_norm a b ordered
  have h := rectangular_int_mul_error (adjoint (sourceHighInt a b ordered))
    (sourceHighInt a b ordered) ((sourceHigh a b ordered)ᴴ) (sourceHigh a b ordered)
    (by norm_num) (by norm_num) (1/10^12) (1/10^12) adj (source_high_error a b ordered)
  apply h.trans
  calc
    _ ≤ (64/10^30 : ℝ) + (1/10^12)*(24+1/10^12) + 24*(1/10^12) := by
      gcongr
      · exact source_high_norm a b ordered
    _ ≤ 1/10^10 := by norm_num

theorem source_gram_hermitian (a b : Basis) (ordered : a < b) :
    (sourceGram a b ordered).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self _

end

def highA006Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795374924216857682864663,-57270982183498659936,744724764853515939575,57270982183449347188],by decide⟩ : Vector Int 4),
  (⟨#[-57270982183498659936,999999488935419491939628613544,-57270982183448613793,744619523909753224767],by decide⟩ : Vector Int 4),
  (⟨#[744724764853515939575,-57270982183448613793,999996795374924216857580860300,57270982183399219454],by decide⟩ : Vector Int 4),
  (⟨#[57270982183449347188,744619523909753224767,57270982183399219454,999999488935419491939429670797],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-8974742649495944888,-293971,8974742649496117221],by decide⟩ : Vector Int 4),
  (⟨#[8974742649495944888,0,8974742649496101312,-515041],by decide⟩ : Vector Int 4),
  (⟨#[293971,-8974742649496101312,0,8974742649496306481],by decide⟩ : Vector Int 4),
  (⟨#[-8974742649496117221,515041,-8974742649496306481,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA006_literal : toTable (gramInt midElevenTable) pairFin pairFin = highA006Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA006_square :
    squareSum (fromTable highA006Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA007Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795603901528082035886403,-57861581144734461144,731023426711840209416,57861581144783695652],by decide⟩ : Vector Int 4),
  (⟨#[-57861581144734461144,999999489164380998963626518306,-57861581144785129423,730917595795207484335],by decide⟩ : Vector Int 4),
  (⟨#[731023426711840209416,-57861581144785129423,999996795603901528082037359435,57861581144785270924],by decide⟩ : Vector Int 4),
  (⟨#[57861581144783695652,730917595795207484335,57861581144785270924,999999489164380998963726665857],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9054238911350140707,-60309,9054238911349874862],by decide⟩ : Vector Int 4),
  (⟨#[9054238911350140707,0,9054238911349889318,259270],by decide⟩ : Vector Int 4),
  (⟨#[60309,-9054238911349889318,0,9054238911349966789],by decide⟩ : Vector Int 4),
  (⟨#[-9054238911349874862,-259270,-9054238911349966789,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA007_literal : toTable (gramInt midA007ElevenTable) pairFin pairFin = highA007Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA007_square :
    squareSum (fromTable highA007Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA008Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795751726910886381908847,-58244002552422541765,722090757213683746949,58244002552471647830],by decide⟩ : Vector Int 4),
  (⟨#[-58244002552422541765,999999489312196139971260515142,-58244002552420159092,721984543052878211426],by decide⟩ : Vector Int 4),
  (⟨#[722090757213683746949,-58244002552420159092,999996795751726910886287547955,58244002552469510571],by decide⟩ : Vector Int 4),
  (⟨#[58244002552471647830,721984543052878211426,58244002552469510571,999999489312196139971554955569],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9105590626018126590,-181295,9105590626018018901],by decide⟩ : Vector Int 4),
  (⟨#[9105590626018126590,0,9105590626018197756,762274],by decide⟩ : Vector Int 4),
  (⟨#[181295,-9105590626018197756,0,9105590626017991627],by decide⟩ : Vector Int 4),
  (⟨#[-9105590626018018901,-762274,-9105590626017991627,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA008_literal : toTable (gramInt midA008ElevenTable) pairFin pairFin = highA008Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA008_square :
    squareSum (fromTable highA008Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA009Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795833394832571113127886,-58455659991978579119,717126350931069738985,58455659991978755381],by decide⟩ : Vector Int 4),
  (⟨#[-58455659991978579119,999999489393858390352778401684,-58455659991980977641,717019924241596659645],by decide⟩ : Vector Int 4),
  (⟨#[717126350931069738985,-58455659991980977641,999996795833394832571114787519,58455659991980990062],by decide⟩ : Vector Int 4),
  (⟨#[58455659991978755381,717019924241596659645,58455659991980990062,999999489393858390352682720318],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9133970545516327822,-60136,9133970545516264224],by decide⟩ : Vector Int 4),
  (⟨#[9133970545516327822,0,9133970545516271811,-247708],by decide⟩ : Vector Int 4),
  (⟨#[60136,-9133970545516271811,0,9133970545516257885],by decide⟩ : Vector Int 4),
  (⟨#[-9133970545516264224,247708,-9133970545516257885,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA009_literal : toTable (gramInt midA009ElevenTable) pairFin pairFin = highA009Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA009_square :
    squareSum (fromTable highA009Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA010Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795995167212720414378921,-58875732821469119072,707230536338335268629,58875732821518317076],by decide⟩ : Vector Int 4),
  (⟨#[-58875732821469119072,999999489555619508844696326632,-58875732821469853037,707123686968805931198],by decide⟩ : Vector Int 4),
  (⟨#[707230536338335268629,-58875732821469853037,999996795995167212720416051503,58875732821469838006],by decide⟩ : Vector Int 4),
  (⟨#[58875732821518317076,707123686968805931198,58875732821469838006,999999489555619508844694818844],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9190208237438169895,4465,9190208237437904601],by decide⟩ : Vector Int 4),
  (⟨#[9190208237438169895,0,9190208237438021569,-3903],by decide⟩ : Vector Int 4),
  (⟨#[-4465,-9190208237438021569,0,9190208237438164874],by decide⟩ : Vector Int 4),
  (⟨#[-9190208237437904601,3903,-9190208237438164874,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA010_literal : toTable (gramInt midA010ElevenTable) pairFin pairFin = highA010Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA010_square :
    squareSum (fromTable highA010Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA011Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796030011900148403757426,-58966354954142291061,705088229959816366218,58966354954093108873],by decide⟩ : Vector Int 4),
  (⟨#[-58966354954142291061,999999489590461765769815300550,-58966354954144789607,704981289252995951226],by decide⟩ : Vector Int 4),
  (⟨#[705088229959816366218,-58966354954144789607,999996796030011900148397428841,58966354954095361528],by decide⟩ : Vector Int 4),
  (⟨#[58966354954093108873,704981289252995951226,58966354954095361528,999999489590461765769813815703],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9202325148559909360,-176082,9202325148560046358],by decide⟩ : Vector Int 4),
  (⟨#[9202325148559909360,0,9202325148559807669,-3844],by decide⟩ : Vector Int 4),
  (⟨#[176082,-9202325148559807669,0,9202325148560043061],by decide⟩ : Vector Int 4),
  (⟨#[-9202325148560046358,3844,-9202325148560043061,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA011_literal : toTable (gramInt midA011ElevenTable) pairFin pairFin = highA011Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA011_square :
    squareSum (fromTable highA011Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA012Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796049041677250874888175,-59015867723675505504,703916628493359306080,59015867723675270719],by decide⟩ : Vector Int 4),
  (⟨#[-59015867723675505504,999999489609490214776105824262,-59015867723669224704,703809637859253055788],by decide⟩ : Vector Int 4),
  (⟨#[703916628493359306080,-59015867723669224704,999996796049041677250968129779,59015867723619946679],by decide⟩ : Vector Int 4),
  (⟨#[59015867723675270719,703809637859253055788,59015867723619946679,999999489609490214776101324524],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9208943126775498841,338430,9208943126775468654],by decide⟩ : Vector Int 4),
  (⟨#[9208943126775498841,0,9208943126775488865,-11648],by decide⟩ : Vector Int 4),
  (⟨#[-338430,-9208943126775488865,0,9208943126775785699],by decide⟩ : Vector Int 4),
  (⟨#[-9208943126775468654,11648,-9208943126775785699,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA012_literal : toTable (gramInt midA012ElevenTable) pairFin pairFin = highA012Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA012_square :
    squareSum (fromTable highA012Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA013Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796248403767428275535767,-59535481008571807437,691573600589574392279,59535481008522399145],by decide⟩ : Vector Int 4),
  (⟨#[-59535481008571807437,999999489808838360641269892289,-59535481008572408812,691466085018730598303],by decide⟩ : Vector Int 4),
  (⟨#[691573600589574392279,-59535481008572408812,999996796248403767428178681213,59535481008523082610],by decide⟩ : Vector Int 4),
  (⟨#[59535481008522399145,691466085018730598303,59535481008523082610,999999489808838360641265364948],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9278298725611965091,-250653,9278298725612199764],by decide⟩ : Vector Int 4),
  (⟨#[9278298725611965091,0,9278298725612028387,-11720],by decide⟩ : Vector Int 4),
  (⟨#[250653,-9278298725612028387,0,9278298725612230277],by decide⟩ : Vector Int 4),
  (⟨#[-9278298725612199764,11720,-9278298725612230277,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA013_literal : toTable (gramInt midA013ElevenTable) pairFin pairFin = highA013Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA013_square :
    squareSum (fromTable highA013Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA014Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796311586058583643355095,-59700502395074734639,687635497015821277514,59700502395074711117],by decide⟩ : Vector Int 4),
  (⟨#[-59700502395074734639,999999489872016220789029658821,-59700502395077434585,687527814357899840137],by decide⟩ : Vector Int 4),
  (⟨#[687635497015821277514,-59700502395077434585,999996796311586058583740530700,59700502395077821690],by decide⟩ : Vector Int 4),
  (⟨#[59700502395074711117,687527814357899840137,59700502395077821690,999999489872016220789431345679],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9300288041019506025,156165,9300288041019503730],by decide⟩ : Vector Int 4),
  (⟨#[9300288041019506025,0,9300288041019629513,1039922],by decide⟩ : Vector Int 4),
  (⟨#[-156165,-9300288041019629513,0,9300288041019463316],by decide⟩ : Vector Int 4),
  (⟨#[-9300288041019503730,-1039922,-9300288041019463316,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA014_literal : toTable (gramInt midA014ElevenTable) pairFin pairFin = highA014Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA014_square :
    squareSum (fromTable highA014Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA015Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796413444139065397160158,-59966888483137434398,681260016545708862636,59966888483137523664],by decide⟩ : Vector Int 4),
  (⟨#[-59966888483137434398,999999489973867145968846705061,-59966888483141484618,681152063786245763517],by decide⟩ : Vector Int 4),
  (⟨#[681260016545708862636,-59966888483141484618,999996796413444139065496163182,59966888483141409516],by decide⟩ : Vector Int 4),
  (⟨#[59966888483137523664,681152063786245763517,59966888483141409516,999999489973867145968748204081],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9335746804909138104,192123,9335746804909106292],by decide⟩ : Vector Int 4),
  (⟨#[9335746804909138104,0,9335746804909029446,-255008],by decide⟩ : Vector Int 4),
  (⟨#[-192123,-9335746804909029446,0,9335746804909063181],by decide⟩ : Vector Int 4),
  (⟨#[-9335746804909106292,255008,-9335746804909063181,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA015_literal : toTable (gramInt midA015ElevenTable) pairFin pairFin = highA015Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA015_square :
    squareSum (fromTable highA015Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA016Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796426366776789714997477,-60000715575320192053,680448802651460952899,60000715575271277112],by decide⟩ : Vector Int 4),
  (⟨#[-60000715575320192053,999999489986788874850964889249,-60000715575319931411,680340815559530361892],by decide⟩ : Vector Int 4),
  (⟨#[680448802651460952899,-60000715575319931411,999996796426366776789616499186,60000715575270440996],by decide⟩ : Vector Int 4),
  (⟨#[60000715575271277112,680340815559530361892,60000715575270440996,999999489986788874851261926130],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9340246230623772033,-222547,9340246230623824250],by decide⟩ : Vector Int 4),
  (⟨#[9340246230623772033,0,9340246230623578026,768995],by decide⟩ : Vector Int 4),
  (⟨#[222547,-9340246230623578026,0,9340246230623843733],by decide⟩ : Vector Int 4),
  (⟨#[-9340246230623824250,-768995,-9340246230623843733,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA016_literal : toTable (gramInt midA016ElevenTable) pairFin pairFin = highA016Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA016_square :
    squareSum (fromTable highA016Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA017Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796452318692657220424046,-60068669981103108814,678818071884118757713,60068669981102752032],by decide⟩ : Vector Int 4),
  (⟨#[-60068669981103108814,999999490012738964816357313606,-60068669981048387570,678710015799381309997],by decide⟩ : Vector Int 4),
  (⟨#[678818071884118757713,-60068669981048387570,999996796452318692657218734468,60068669981048982383],by decide⟩ : Vector Int 4),
  (⟨#[60068669981102752032,678710015799381309997,60068669981048982383,999999490012738964816460387209],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9349282761122395138,156366,9349282761122237826],by decide⟩ : Vector Int 4),
  (⟨#[9349282761122395138,0,9349282761122326029,266846],by decide⟩ : Vector Int 4),
  (⟨#[-156366,-9349282761122326029,0,9349282761122384947],by decide⟩ : Vector Int 4),
  (⟨#[-9349282761122237826,-266846,-9349282761122384947,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA017_literal : toTable (gramInt midA017ElevenTable) pairFin pairFin = highA017Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA017_square :
    squareSum (fromTable highA017Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA018Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796538920864248886114619,-60295639312537931705,673360727527359514930,60295639312537844590],by decide⟩ : Vector Int 4),
  (⟨#[-60295639312537931705,999999490099335036376613599225,-60295639312487904814,673252440782060095586],by decide⟩ : Vector Int 4),
  (⟨#[673360727527359514930,-60295639312487904814,999996796538920864248882732712,60295639312487899958],by decide⟩ : Vector Int 4),
  (⟨#[60295639312537844590,673252440782060095586,60295639312487899958,999999490099335036376612091215],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9379443189618505726,-39466,9379443189618537703],by decide⟩ : Vector Int 4),
  (⟨#[9379443189618505726,0,9379443189618679158,-3903],by decide⟩ : Vector Int 4),
  (⟨#[39466,-9379443189618679158,0,9379443189618678367],by decide⟩ : Vector Int 4),
  (⟨#[-9379443189618537703,3903,-9379443189618678367,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA018_literal : toTable (gramInt midA018ElevenTable) pairFin pairFin = highA018Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA018_square :
    squareSum (fromTable highA018Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA019Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796599682885722168040875,-60455073614028916768,669517424793789814217,60455073614078013856],by decide⟩ : Vector Int 4),
  (⟨#[-60455073614028916768,999999490160092771534246876470,-60455073614082292548,669408975817004407999],by decide⟩ : Vector Int 4),
  (⟨#[669517424793789814217,-60455073614082292548,999996796599682885722057292670,60455073614131718799],by decide⟩ : Vector Int 4),
  (⟨#[60455073614078013856,669408975817004407999,60455073614131718799,999999490160092771534643770314],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9400609302726710795,-475464,9400609302726570393],by decide⟩ : Vector Int 4),
  (⟨#[9400609302726710795,0,9400609302726723684,1027514],by decide⟩ : Vector Int 4),
  (⟨#[475464,-9400609302726723684,0,9400609302726452230],by decide⟩ : Vector Int 4),
  (⟨#[-9400609302726570393,-1027514,-9400609302726452230,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA019_literal : toTable (gramInt midA019ElevenTable) pairFin pairFin = highA019Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA019_square :
    squareSum (fromTable highA019Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA020Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796610576914519100241885,-60483674978961852748,668827109914771874130,60483674979011160059],by decide⟩ : Vector Int 4),
  (⟨#[-60483674978961852748,999999490170986031278933487314,-60483674979011856693,668718631817071198596],by decide⟩ : Vector Int 4),
  (⟨#[668827109914771874130,-60483674979011856693,999996796610576914519095438341,60483674979011937093],by decide⟩ : Vector Int 4),
  (⟨#[60483674979011160059,668718631817071198596,60483674979011937093,999999490170986031278838094722],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9404404603286231082,-75504,9404404603285902520],by decide⟩ : Vector Int 4),
  (⟨#[9404404603286231082,0,9404404603285916035,-246960],by decide⟩ : Vector Int 4),
  (⟨#[75504,-9404404603285916035,0,9404404603286028263],by decide⟩ : Vector Int 4),
  (⟨#[-9404404603285902520,246960,-9404404603286028263,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA020_literal : toTable (gramInt midA020ElevenTable) pairFin pairFin = highA020Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA020_square :
    squareSum (fromTable highA020Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA021Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796816587686094107092798,-61025478703303905404,655701336062397468337,61025478703304223908],by decide⟩ : Vector Int 4),
  (⟨#[-61025478703303905404,999999490376982227696068668102,-61025478703303873449,655592305287851991525],by decide⟩ : Vector Int 4),
  (⟨#[655701336062397468337,-61025478703303873449,999996796816587686094113287470,61025478703303532487],by decide⟩ : Vector Int 4),
  (⟨#[61025478703304223908,655592305287851991525,61025478703303532487,999999490376982227696167101177],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9476199807391033002,46450,9476199807390900535],by decide⟩ : Vector Int 4),
  (⟨#[9476199807391033002,0,9476199807390757909,254832],by decide⟩ : Vector Int 4),
  (⟨#[-46450,-9476199807390757909,0,9476199807390871533],by decide⟩ : Vector Int 4),
  (⟨#[-9476199807390900535,-254832,-9476199807390871533,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA021_literal : toTable (gramInt midA021ElevenTable) pairFin pairFin = highA021Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA021_square :
    squareSum (fromTable highA021Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA022Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796822009938649146867946,-61039763262033234760,655354022104931980199,61039763261885938725],by decide⟩ : Vector Int 4),
  (⟨#[-61039763262033234760,999999490382404095805750260675,-61039763262037603625,655244976733025159922],by decide⟩ : Vector Int 4),
  (⟨#[655354022104931980199,-61039763262037603625,999996796822009938649147373312,61039763261889895496],by decide⟩ : Vector Int 4),
  (⟨#[61039763261885938725,655244976733025159922,61039763261889895496,999999490382404095805653451695],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9478090102240650077,-61818,9478090102241062602],by decide⟩ : Vector Int 4),
  (⟨#[9478090102240650077,0,9478090102240442656,-250628],by decide⟩ : Vector Int 4),
  (⟨#[61818,-9478090102240442656,0,9478090102241018932],by decide⟩ : Vector Int 4),
  (⟨#[-9478090102241062602,250628,-9478090102241018932,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA022_literal : toTable (gramInt midA022ElevenTable) pairFin pairFin = highA022Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA022_square :
    squareSum (fromTable highA022Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA023Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796862111986950560202129,-61145447957384193892,652782411727690775808,61145447957383847755],by decide⟩ : Vector Int 4),
  (⟨#[-61145447957384193892,999999490422503299498449813594,-61145447957386048000,652673258312120380828],by decide⟩ : Vector Int 4),
  (⟨#[652782411727690775808,-61145447957386048000,999996796862111986950363759794,61145447957386196515],by decide⟩ : Vector Int 4),
  (⟨#[61145447957383847755,652673258312120380828,61145447957386196515,999999490422503299498643512938],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9492071400010153835,-539751,9492071400010282247],by decide⟩ : Vector Int 4),
  (⟨#[9492071400010153835,0,9492071400010341978,501466],by decide⟩ : Vector Int 4),
  (⟨#[539751,-9492071400010341978,0,9492071400010273904],by decide⟩ : Vector Int 4),
  (⟨#[-9492071400010282247,-501466,-9492071400010273904,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA023_literal : toTable (gramInt midA023ElevenTable) pairFin pairFin = highA023Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA023_square :
    squareSum (fromTable highA023Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA106Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795401533816226781844891,-57227837905659156576,746291656344095596173,57227837905658937732],by decide⟩ : Vector Int 4),
  (⟨#[-57227837905659156576,999999488962027403130404822182,-57227837905606509510,746186361775880282956],by decide⟩ : Vector Int 4),
  (⟨#[746291656344095596173,-57227837905606509510,999996795401533816226786069491,57227837905606698548],by decide⟩ : Vector Int 4),
  (⟨#[57227837905658937732,746186361775880282956,57227837905606698548,999999488962027403130008462053],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-8966570898042407219,107469,8966570898042509106],by decide⟩ : Vector Int 4),
  (⟨#[8966570898042407219,0,8966570898042733642,-1026131],by decide⟩ : Vector Int 4),
  (⟨#[-107469,-8966570898042733642,0,8966570898042655399],by decide⟩ : Vector Int 4),
  (⟨#[-8966570898042509106,1026131,-8966570898042655399,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA106_literal : toTable (gramInt midA106ElevenTable) pairFin pairFin = highA106Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA106_square :
    squareSum (fromTable highA106Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA107Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795630524272016349821235,-57818476333327483427,732603456989645527833,57818476333278353491],by decide⟩ : Vector Int 4),
  (⟨#[-57818476333327483427,999999489191002047403684268447,-57818476333380532905,732497572119303446828],by decide⟩ : Vector Int 4),
  (⟨#[732603456989645527833,-57818476333380532905,999996795630524272016454879734,57818476333331321236],by decide⟩ : Vector Int 4),
  (⟨#[57818476333278353491,732497572119303446828,57818476333331321236,999999489191002047403590034359],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9046067332461009154,206256,9046067332461115595],by decide⟩ : Vector Int 4),
  (⟨#[9046067332461009154,0,9046067332460827693,-243962],by decide⟩ : Vector Int 4),
  (⟨#[-206256,-9046067332460827693,0,9046067332460966954],by decide⟩ : Vector Int 4),
  (⟨#[-9046067332461115595,243962,-9046067332460966954,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA107_literal : toTable (gramInt midA107ElevenTable) pairFin pairFin = highA107Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA107_square :
    squareSum (fromTable highA107Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA108Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795778358148526978401848,-58200923504754995656,723679277447331171830,58200923504755091161],by decide⟩ : Vector Int 4),
  (⟨#[-58200923504754995656,999999489338825677371074780773,-58200923504758228708,723573009117382975476],by decide⟩ : Vector Int 4),
  (⟨#[723679277447331171830,-58200923504758228708,999996795778358148526787588346,58200923504758160577],by decide⟩ : Vector Int 4),
  (⟨#[58200923504755091161,723573009117382975476,58200923504758160577,999999489338825677370877497383],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9097419159432555933,-526577,9097419159432524993],by decide⟩ : Vector Int 4),
  (⟨#[9097419159432555933,0,9097419159432448957,-510745],by decide⟩ : Vector Int 4),
  (⟨#[526577,-9097419159432448957,0,9097419159432483641],by decide⟩ : Vector Int 4),
  (⟨#[-9097419159432524993,510745,-9097419159432483641,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA108_literal : toTable (gramInt midA108ElevenTable) pairFin pairFin = highA108Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA108_square :
    squareSum (fromTable highA108Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA109Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996795860030765252165827859,-58412595273982728728,718719564126274969358,58412595273982885585],by decide⟩ : Vector Int 4),
  (⟨#[-58412595273982728728,999999489420492620162539856365,-58412595273985227494,718613083149035780304],by decide⟩ : Vector Int 4),
  (⟨#[718719564126274969358,-58412595273985227494,999996795860030765251967461494,58412595273985056893],by decide⟩ : Vector Int 4),
  (⟨#[58412595273982885585,718613083149035780304,58412595273985056893,999999489420492620162638480030],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9125799141276734990,-545873,9125799141276668438],by decide⟩ : Vector Int 4),
  (⟨#[9125799141276734990,0,9125799141276629680,255326],by decide⟩ : Vector Int 4),
  (⟨#[545873,-9125799141276629680,0,9125799141276694355],by decide⟩ : Vector Int 4),
  (⟨#[-9125799141276668438,-255326,-9125799141276694355,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA109_literal : toTable (gramInt midA109ElevenTable) pairFin pairFin = highA109Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA109_square :
    squareSum (fromTable highA109Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA110Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796021812451032263997387,-58832696692018779489,708833051034078935187,58832696691969350626],by decide⟩ : Vector Int 4),
  (⟨#[-58832696692018779489,999999489582263039061420257658,-58832696691966553200,708726147139464253261],by decide⟩ : Vector Int 4),
  (⟨#[708833051034078935187,-58832696691966553200,999996796021812451032257316732,58832696691966334593],by decide⟩ : Vector Int 4),
  (⟨#[58832696691969350626,708726147139464253261,58832696691966334593,999999489582263039061215569021],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9182036957334013580,-15752,9182036957334377778],by decide⟩ : Vector Int 4),
  (⟨#[9182036957334013580,0,9182036957334289194,-529915],by decide⟩ : Vector Int 4),
  (⟨#[15752,-9182036957334289194,0,9182036957334244815],by decide⟩ : Vector Int 4),
  (⟨#[-9182036957334377778,529915,-9182036957334244815,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA110_literal : toTable (gramInt midA110ElevenTable) pairFin pairFin = highA110Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA110_square :
    squareSum (fromTable highA110Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA111Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796056659143775194690280,-58923325017725846896,706692749078667864526,58923325017824538020],by decide⟩ : Vector Int 4),
  (⟨#[-58923325017725846896,999999489617107300172754098955,-58923325017725585035,706585753795387197511],by decide⟩ : Vector Int 4),
  (⟨#[706692749078667864526,-58923325017725585035,999996796056659143775194532988,58923325017775233593],by decide⟩ : Vector Int 4),
  (⟨#[58923325017824538020,706585753795387197511,58923325017775233593,999999489617107300172961736406],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9194153895305060451,-31463,9194153895304527270],by decide⟩ : Vector Int 4),
  (⟨#[9194153895305060451,0,9194153895305031156,537550],by decide⟩ : Vector Int 4),
  (⟨#[31463,-9194153895305031156,0,9194153895304824990],by decide⟩ : Vector Int 4),
  (⟨#[-9194153895304527270,-537550,-9194153895304824990,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA111_literal : toTable (gramInt midA111ElevenTable) pairFin pairFin = highA111Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA111_square :
    squareSum (fromTable highA111Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA112Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796075690016184774282596,-58972841175075017979,705522242430760654465,58972841175074695272],by decide⟩ : Vector Int 4),
  (⟨#[-58972841175075017979,999999489636136843869411778560,-58972841175079691266,705415197192697805522],by decide⟩ : Vector Int 4),
  (⟨#[705522242430760654465,-58972841175079691266,999996796075690016184673219058,58972841175030574090],by decide⟩ : Vector Int 4),
  (⟨#[58972841175074695272,705415197192697805522,58972841175030574090,999999489636136843869507360062],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9200771888200238346,-387897,9200771888200240315],by decide⟩ : Vector Int 4),
  (⟨#[9200771888200238346,0,9200771888200323477,247450],by decide⟩ : Vector Int 4),
  (⟨#[387897,-9200771888200323477,0,9200771888200554064],by decide⟩ : Vector Int 4),
  (⟨#[-9200771888200240315,-247450,-9200771888200554064,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA112_literal : toTable (gramInt midA112ElevenTable) pairFin pairFin = highA112Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA112_square :
    squareSum (fromTable highA112Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA113Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796275063587138483445429,-59492490177128220226,693190690180050069246,59492490177177618502],by decide⟩ : Vector Int 4),
  (⟨#[-59492490177128220226,999999489835496464034602783958,-59492490177129815916,693083119710446538814],by decide⟩ : Vector Int 4),
  (⟨#[693190690180050069246,-59492490177129815916,999996796275063587138482100392,59492490177179132089],by decide⟩ : Vector Int 4),
  (⟨#[59492490177177618502,693083119710446538814,59492490177179132089,999999489835496464034705839474],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9270127641533935040,-34835,9270127641533699425],by decide⟩ : Vector Int 4),
  (⟨#[9270127641533935040,0,9270127641533897727,266798],by decide⟩ : Vector Int 4),
  (⟨#[34835,-9270127641533897727,0,9270127641533694895],by decide⟩ : Vector Int 4),
  (⟨#[-9270127641533699425,-266798,-9270127641533694895,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA113_literal : toTable (gramInt midA113ElevenTable) pairFin pairFin = highA113Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA113_square :
    squareSum (fromTable highA113Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA114Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796338249519088222193687,-59657522970088079792,689256225770766605375,59657522970063651213],by decide⟩ : Vector Int 4),
  (⟨#[-59657522970088079792,999999489898677962917705365480,-59657522970118361649,689148488120435782850],by decide⟩ : Vector Int 4),
  (⟨#[689256225770766605375,-59657522970118361649,999996796338249519088229099871,59657522970068962437],by decide⟩ : Vector Int 4),
  (⟨#[59657522970063651213,689148488120435782850,59657522970068962437,999999489898677962917508365282],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9292117006174709876,-46582,9292117006174666885],by decide⟩ : Vector Int 4),
  (⟨#[9292117006174709876,0,9292117006174429752,-510011],by decide⟩ : Vector Int 4),
  (⟨#[46582,-9292117006174429752,0,9292117006174714655],by decide⟩ : Vector Int 4),
  (⟨#[-9292117006174666885,510011,-9292117006174714655,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA114_literal : toTable (gramInt midA114ElevenTable) pairFin pairFin = highA114Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA114_square :
    squareSum (fromTable highA114Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA115Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796440113471311796757367,-59923927535126994766,682886614408974955003,59923927535127152082],by decide⟩ : Vector Int 4),
  (⟨#[-59923927535126994766,999999490000534756511566301369,-59923927535125796460,682778606505210742964],by decide⟩ : Vector Int 4),
  (⟨#[682886614408974955003,-59923927535125796460,999996796440113471311804674035,59923927535125624987],by decide⟩ : Vector Int 4),
  (⟨#[59923927535127152082,682778606505210742964,59923927535125624987,999999490000534756511664796804],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9327575849709146799,147505,9327575849709080293],by decide⟩ : Vector Int 4),
  (⟨#[9327575849709146799,0,9327575849709019846,254993],by decide⟩ : Vector Int 4),
  (⟨#[-147505,-9327575849709019846,0,9327575849709084429],by decide⟩ : Vector Int 4),
  (⟨#[-9327575849709080293,-254993,-9327575849709084429,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA115_literal : toTable (gramInt midA115ElevenTable) pairFin pairFin = highA115Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA115_square :
    squareSum (fromTable highA115Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA116Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796453036854182021063275,-59957756979094235761,682076145325577361079,59957756979094126800],by decide⟩ : Vector Int 4),
  (⟨#[-59957756979094235761,999999490013457230117000810199,-59957756979092543336,681968103070034521389],by decide⟩ : Vector Int 4),
  (⟨#[682076145325577361079,-59957756979092543336,999996796453036854182019344929,59957756979117233919],by decide⟩ : Vector Int 4),
  (⟨#[59957756979094126800,681968103070034521389,59957756979117233919,999999490013457230117197787193],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9332075285552093475,27823,9332075285552172222],by decide⟩ : Vector Int 4),
  (⟨#[9332075285552093475,0,9332075285552212222,509951],by decide⟩ : Vector Int 4),
  (⟨#[-27823,-9332075285552212222,0,9332075285552028701],by decide⟩ : Vector Int 4),
  (⟨#[-9332075285552172222,-509951,-9332075285552028701,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA116_literal : toTable (gramInt midA116ElevenTable) pairFin pairFin = highA116Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA116_square :
    squareSum (fromTable highA116Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA117Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796478990266628135212541,-60025716113633060879,680446910464900866556,60025716113583929377],by decide⟩ : Vector Int 4),
  (⟨#[-60025716113633060879,999999490039408815812196318717,-60025716113630689652,680338799177424296534],by decide⟩ : Vector Int 4),
  (⟨#[680446910464900866556,-60025716113630689652,999996796478990266628136567644,60025716113581475930],by decide⟩ : Vector Int 4),
  (⟨#[60025716113583929377,680338799177424296534,60025716113581475930,999999490039408815812099400204],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9341111836408123268,65935,9341111836408261236],by decide⟩ : Vector Int 4),
  (⟨#[9341111836408123268,0,9341111836408161846,-250911],by decide⟩ : Vector Int 4),
  (⟨#[-65935,-9341111836408161846,0,9341111836408332583],by decide⟩ : Vector Int 4),
  (⟨#[-9341111836408261236,250911,-9341111836408332583,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA117_literal : toTable (gramInt midA117ElevenTable) pairFin pairFin = highA117Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA117_square :
    squareSum (fromTable highA117Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA118Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796565597433675674572723,-60252701276196801263,674994559315978761625,60252701276196709997],by decide⟩ : Vector Int 4),
  (⟨#[-60252701276196801263,999999490126009879988993743175,-60252701276196883611,674886217239282470274],by decide⟩ : Vector Int 4),
  (⟨#[674994559315978761625,-60252701276196883611,999996796565597433675685619752,60252701276196792347],by decide⟩ : Vector Int 4),
  (⟨#[60252701276196709997,674886217239282470274,60252701276196792347,999999490126009879989089148710],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9371272332996810711,90707,9371272332996841892],by decide⟩ : Vector Int 4),
  (⟨#[9371272332996810711,0,9371272332996776386,246993],by decide⟩ : Vector Int 4),
  (⟨#[-90707,-9371272332996776386,0,9371272332996807568],by decide⟩ : Vector Int 4),
  (⟨#[-9371272332996841892,-246993,-9371272332996807568,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA118_literal : toTable (gramInt midA118ElevenTable) pairFin pairFin = highA118Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA118_square :
    squareSum (fromTable highA118Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA119Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796626362961298163607291,-60412146732595957678,671154761152022669864,60412146732694201489],by decide⟩ : Vector Int 4),
  (⟨#[-60412146732595957678,999999490186771119301650449729,-60412146732593395841,671046256752151392140],by decide⟩ : Vector Int 4),
  (⟨#[671154761152022669864,-60412146732593395841,999996796626362961298266633880,60412146732691886564],by decide⟩ : Vector Int 4),
  (⟨#[60412146732694201489,671046256752151392140,60412146732691886564,999999490186771119301550450418],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9392438494026366656,361057,9392438494026092564],by decide⟩ : Vector Int 4),
  (⟨#[9392438494026366656,0,9392438494026471329,-258886],by decide⟩ : Vector Int 4),
  (⟨#[-361057,-9392438494026471329,0,9392438494026098952],by decide⟩ : Vector Int 4),
  (⟨#[-9392438494026092564,258886,-9392438494026098952,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA119_literal : toTable (gramInt midA119ElevenTable) pairFin pairFin = highA119Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA119_square :
    squareSum (fromTable highA119Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA120Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796637257618820218469888,-60440750101598846315,670465074714360673968,60440750101648130294],by decide⟩ : Vector Int 4),
  (⟨#[-60440750101598846315,999999490197665007412686005475,-60440750101598855011,670356541176893620391],by decide⟩ : Vector Int 4),
  (⟨#[670465074714360673968,-60440750101598855011,999996796637257618820128191511,60440750101648221163],by decide⟩ : Vector Int 4),
  (⟨#[60440750101648130294,670356541176893620391,60440750101648221163,999999490197665007412789022500],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9396233803190489975,-138574,9396233803190303683],by decide⟩ : Vector Int 4),
  (⟨#[9396233803190489975,0,9396233803190505099,266700],by decide⟩ : Vector Int 4),
  (⟨#[138574,-9396233803190505099,0,9396233803190270128],by decide⟩ : Vector Int 4),
  (⟨#[-9396233803190303683,-266700,-9396233803190270128,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA120_literal : toTable (gramInt midA120ElevenTable) pairFin pairFin = highA120Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA120_square :
    squareSum (fromTable highA120Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA121Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796843280285958638212189,-60982591962507171155,657351191046125245467,60982591962507087690],by decide⟩ : Vector Int 4),
  (⟨#[-60982591962507171155,999999490403673092603703277023,-60982591962554777971,657242104520971139639],by decide⟩ : Vector Int 4),
  (⟨#[657351191046125245467,-60982591962554777971,999996796843280285958536385045,60982591962554777072],by decide⟩ : Vector Int 4),
  (⟨#[60982591962507087690,657242104520971139639,60982591962554777072,999999490403673092603701729118],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9468029170745288656,-263740,9468029170745305181],by decide⟩ : Vector Int 4),
  (⟨#[9468029170745288656,0,9468029170745156529,-4007],by decide⟩ : Vector Int 4),
  (⟨#[263740,-9468029170745156529,0,9468029170745156218],by decide⟩ : Vector Int 4),
  (⟨#[-9468029170745305181,4007,-9468029170745156218,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA121_literal : toTable (gramInt midA121ElevenTable) pairFin pairFin = highA121Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA121_square :
    squareSum (fromTable highA121Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA122Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796848702851763770609835,-60996877531100775408,657004190197178267301,60996877531001989708],by decide⟩ : Vector Int 4),
  (⟨#[-60996877531100775408,999999490409095273784562183350,-60996877531155070759,656895089066678941117],by decide⟩ : Vector Int 4),
  (⟨#[657004190197178267301,-60996877531155070759,999996796848702851763975982557,60996877531056697359],by decide⟩ : Vector Int 4),
  (⟨#[60996877531001989708,656895089066678941117,60996877531056697359,999999490409095273784652881779],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9469919469915654427,465305,9469919469916155278],by decide⟩ : Vector Int 4),
  (⟨#[9469919469915654427,0,9469919469915578776,234807],by decide⟩ : Vector Int 4),
  (⟨#[-465305,-9469919469915578776,0,9469919469915931795],by decide⟩ : Vector Int 4),
  (⟨#[-9469919469916155278,-234807,-9469919469915931795,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA122_literal : toTable (gramInt midA122ElevenTable) pairFin pairFin = highA122Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA122_square :
    squareSum (fromTable highA122Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def highA123Table : IntTable 4 4 := ⟨
⟨#[
  (⟨#[999996796888807217062511823853,-61102569705245063530,654434895765789091849,61102569705219797760],by decide⟩ : Vector Int 4),
  (⟨#[-61102569705245063530,999999490449196793149145570496,-61102569705266899765,654325686530860734718],by decide⟩ : Vector Int 4),
  (⟨#[654434895765789091849,-61102569705266899765,999996796888807217062410151495,61102569705218184514],by decide⟩ : Vector Int 4),
  (⟨#[61102569705219797760,654325686530860734718,61102569705218184514,999999490449196793148944122240],by decide⟩ : Vector Int 4)
],by decide⟩,
⟨#[
  (⟨#[0,-9483900799671730667,-230367,9483900799671727396],by decide⟩ : Vector Int 4),
  (⟨#[9483900799671730667,0,9483900799671465418,-521527],by decide⟩ : Vector Int 4),
  (⟨#[230367,-9483900799671465418,0,9483900799671824686],by decide⟩ : Vector Int 4),
  (⟨#[-9483900799671727396,521527,-9483900799671824686,0],by decide⟩ : Vector Int 4)
],by decide⟩⟩

theorem highA123_literal : toTable (gramInt midA123ElevenTable) pairFin pairFin = highA123Table := by
  apply int_table_ext
  · decide +kernel
  · decide +kernel
theorem highA123_square :
    squareSum (fromTable highA123Table pairFin pairFin) < (scale/10000)^2 := by decide +kernel

def midTable (a : Fin 2) (b : Fin 18) : IntTable 64 4 :=
  if a=0 then ![midElevenTable,midA007ElevenTable,midA008ElevenTable,midA009ElevenTable,midA010ElevenTable,midA011ElevenTable,midA012ElevenTable,midA013ElevenTable,midA014ElevenTable,midA015ElevenTable,midA016ElevenTable,midA017ElevenTable,midA018ElevenTable,midA019ElevenTable,midA020ElevenTable,midA021ElevenTable,midA022ElevenTable,midA023ElevenTable] b
  else ![midA106ElevenTable,midA107ElevenTable,midA108ElevenTable,midA109ElevenTable,midA110ElevenTable,midA111ElevenTable,midA112ElevenTable,midA113ElevenTable,midA114ElevenTable,midA115ElevenTable,midA116ElevenTable,midA117ElevenTable,midA118ElevenTable,midA119ElevenTable,midA120ElevenTable,midA121ElevenTable,midA122ElevenTable,midA123ElevenTable] b

theorem mid_table_source (a : Fin 2) (b : Fin 18) :
    toTable (chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b))
      pointerFin pairFin = midTable a b := by
  fin_cases a <;> fin_cases b
  · exact mid_eleven_original_literal
  · exact midA007_eleven_original_literal
  · exact midA008_eleven_original_literal
  · exact midA009_eleven_original_literal
  · exact midA010_eleven_original_literal
  · exact midA011_eleven_original_literal
  · exact midA012_eleven_original_literal
  · exact midA013_eleven_original_literal
  · exact midA014_eleven_original_literal
  · exact midA015_eleven_original_literal
  · exact midA016_eleven_original_literal
  · exact midA017_eleven_original_literal
  · exact midA018_eleven_original_literal
  · exact midA019_eleven_original_literal
  · exact midA020_eleven_original_literal
  · exact midA021_eleven_original_literal
  · exact midA022_eleven_original_literal
  · exact midA023_eleven_original_literal
  · exact midA106_eleven_original_literal
  · exact midA107_eleven_original_literal
  · exact midA108_eleven_original_literal
  · exact midA109_eleven_original_literal
  · exact midA110_eleven_original_literal
  · exact midA111_eleven_original_literal
  · exact midA112_eleven_original_literal
  · exact midA113_eleven_original_literal
  · exact midA114_eleven_original_literal
  · exact midA115_eleven_original_literal
  · exact midA116_eleven_original_literal
  · exact midA117_eleven_original_literal
  · exact midA118_eleven_original_literal
  · exact midA119_eleven_original_literal
  · exact midA120_eleven_original_literal
  · exact midA121_eleven_original_literal
  · exact midA122_eleven_original_literal
  · exact midA123_eleven_original_literal

noncomputable section
theorem mid_gram_norm (a : Fin 2) (b : Fin 18) :
    ‖value (gramInt (midTable a b)) - (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤
      (1/10000 : ℝ) := by
  fin_cases a <;> fin_cases b
  · exact gram_norm_from_literal _ _ highA006_literal highA006_square
  · exact gram_norm_from_literal _ _ highA007_literal highA007_square
  · exact gram_norm_from_literal _ _ highA008_literal highA008_square
  · exact gram_norm_from_literal _ _ highA009_literal highA009_square
  · exact gram_norm_from_literal _ _ highA010_literal highA010_square
  · exact gram_norm_from_literal _ _ highA011_literal highA011_square
  · exact gram_norm_from_literal _ _ highA012_literal highA012_square
  · exact gram_norm_from_literal _ _ highA013_literal highA013_square
  · exact gram_norm_from_literal _ _ highA014_literal highA014_square
  · exact gram_norm_from_literal _ _ highA015_literal highA015_square
  · exact gram_norm_from_literal _ _ highA016_literal highA016_square
  · exact gram_norm_from_literal _ _ highA017_literal highA017_square
  · exact gram_norm_from_literal _ _ highA018_literal highA018_square
  · exact gram_norm_from_literal _ _ highA019_literal highA019_square
  · exact gram_norm_from_literal _ _ highA020_literal highA020_square
  · exact gram_norm_from_literal _ _ highA021_literal highA021_square
  · exact gram_norm_from_literal _ _ highA022_literal highA022_square
  · exact gram_norm_from_literal _ _ highA023_literal highA023_square
  · exact gram_norm_from_literal _ _ highA106_literal highA106_square
  · exact gram_norm_from_literal _ _ highA107_literal highA107_square
  · exact gram_norm_from_literal _ _ highA108_literal highA108_square
  · exact gram_norm_from_literal _ _ highA109_literal highA109_square
  · exact gram_norm_from_literal _ _ highA110_literal highA110_square
  · exact gram_norm_from_literal _ _ highA111_literal highA111_square
  · exact gram_norm_from_literal _ _ highA112_literal highA112_square
  · exact gram_norm_from_literal _ _ highA113_literal highA113_square
  · exact gram_norm_from_literal _ _ highA114_literal highA114_square
  · exact gram_norm_from_literal _ _ highA115_literal highA115_square
  · exact gram_norm_from_literal _ _ highA116_literal highA116_square
  · exact gram_norm_from_literal _ _ highA117_literal highA117_square
  · exact gram_norm_from_literal _ _ highA118_literal highA118_square
  · exact gram_norm_from_literal _ _ highA119_literal highA119_square
  · exact gram_norm_from_literal _ _ highA120_literal highA120_square
  · exact gram_norm_from_literal _ _ highA121_literal highA121_square
  · exact gram_norm_from_literal _ _ highA122_literal highA122_square
  · exact gram_norm_from_literal _ _ highA123_literal highA123_square

theorem mid_source_gram_int (a : Fin 2) (b : Fin 18) :
    sourceGramInt (midAnchor a) (midPartner b) (mid_address_ordered a b) = gramInt (midTable a b) := by
  have same : chargedElevenInt (midAnchor a) (midPartner b) (mid_address_ordered a b) =
      fromTable (midTable a b) pointerFin pairFin := by
    rw [← from_to_table (chargedElevenInt (midAnchor a) (midPartner b)
      (mid_address_ordered a b)) pointerFin pairFin, mid_table_source]
  simp only [sourceGramInt, sourceHighInt, gramInt, selectedInt, same]

theorem mid_source_gram_norm (a : Fin 2) (b : Fin 18) :
    ‖sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b) -
      (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)‖ ≤ (1/1000 : ℝ) := by
  have err := source_gram_error (midAnchor a) (midPartner b) (mid_address_ordered a b)
  rw [mid_source_gram_int, norm_sub_rev] at err
  have tri := norm_sub_le_norm_sub_add_norm_sub
    (sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b))
    (value (gramInt (midTable a b))) (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
  exact tri.trans ((add_le_add err (mid_gram_norm a b)).trans (by norm_num))

theorem mid_source_gram_floor (a : Fin 2) (b : Fin 18) :
    (999/1000 : ℝ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) ≤
      sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b) := by
  have h := hermitian_lower_from_center _ (source_gram_hermitian
    (midAnchor a) (midPartner b) (mid_address_ordered a b)) 1 (1/1000)
    (by simpa only [one_smul] using mid_source_gram_norm a b)
  norm_num at h ⊢
  exact h

def midReferenceHigh : ℝ :=
  ∑ a : Fin 2, ∑ b : Fin 18,
    Collision.energy (sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b))
      (midSectorBody a b)

theorem mid_reference_high_lower : (74/100 : ℝ) < midReferenceHigh := by
  have rows (a : Fin 2) (b : Fin 18) :
      (999/1000 : ℝ) * (midSectorBody a b).trace.re ≤
        Collision.energy (sourceGram (midAnchor a) (midPartner b) (mid_address_ordered a b))
          (midSectorBody a b) :=
    energy_lower_from_order _ _ (mid_sector_body_positive a b) _ (mid_source_gram_floor a b)
  have lower := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => rows a b))
  change (∑ a : Fin 2, ∑ b : Fin 18, (999/1000 : ℝ) * (midSectorBody a b).trace.re) ≤
    midReferenceHigh at lower
  simp_rw [← Finset.mul_sum] at lower
  nlinarith only [lower, mid_sector_body_mass_lower]

end
end TopPopulation
end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
