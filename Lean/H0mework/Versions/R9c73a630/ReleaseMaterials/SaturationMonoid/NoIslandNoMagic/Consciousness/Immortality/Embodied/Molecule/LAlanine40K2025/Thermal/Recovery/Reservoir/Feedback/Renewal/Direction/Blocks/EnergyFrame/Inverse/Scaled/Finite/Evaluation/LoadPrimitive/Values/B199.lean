import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B132
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B133

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v3185_pa : Scalar.QComplex := ((999999011601036393483751736290 : Int)/10^30,(-1405986113117950122697292110 : Int)/10^30)
theorem v3185_pa_checked : Scalar.distance (sourceCoefficient 41 70 1 0) v3185_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3185_pb : Scalar.QComplex := ((-606651380595452901789845 : Int)/10^30,(-431477078842928995836648005 : Int)/10^30)
theorem v3185_pb_checked : Scalar.distance (sourceCoefficient 41 70 1 1) v3185_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3185_pg : Scalar.QComplex := ((-93086336198428796012019 : Int)/10^30,(130878225375921964610 : Int)/10^30)
theorem v3185_pg_checked : Scalar.distance (sourceCoefficient 41 70 1 2) v3185_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3185_mb : Scalar.QComplex := ((-978996440746622307108162 : Int)/10^30,(-431476394671474175994065434 : Int)/10^30)
theorem v3185_mb_checked : Scalar.distance (sourceCoefficient 41 70 3 1) v3185_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3185_mg : Scalar.QComplex := ((-93086188596117610643010 : Int)/10^30,(211207492330270069547 : Int)/10^30)
theorem v3185_mg_checked : Scalar.distance (sourceCoefficient 41 70 3 2) v3185_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3185_upper : Scalar.QComplex := ((999995095615495571562896393246 : Int)/10^30,(-3131891593888509246631746413 : Int)/10^30)
theorem v3185_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 70 5) 1) 14) v3185_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3185 : Material (41 : Basis) (70 : Basis) where
  plus := ![v3185_pa,v3185_pb,v3185_pg]
  minus := ![(Primitive.Addresses.material3185 1).one,v3185_mb,v3185_mg]
  upper := v3185_upper
  lower := (Primitive.Addresses.material3185 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3185_pa_checked.trans (by decide +kernel)
    · exact v3185_pb_checked.trans (by decide +kernel)
    · exact v3185_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 70 Primitive.Addresses.material3185
    · exact v3185_mb_checked.trans (by decide +kernel)
    · exact v3185_mg_checked.trans (by decide +kernel)
  upper_error := v3185_upper_checked
  lower_error := reuse_lower_error 41 70 Primitive.Addresses.material3185

def v3186_pa : Scalar.QComplex := ((999998977150603563672325331072 : Int)/10^30,(-1430278905197083426235389316 : Int)/10^30)
theorem v3186_pa_checked : Scalar.distance (sourceCoefficient 41 71 1 0) v3186_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3186_pb : Scalar.QComplex := ((-617133171524273116819796 : Int)/10^30,(-431477062304113423667869672 : Int)/10^30)
theorem v3186_pb_checked : Scalar.distance (sourceCoefficient 41 71 1 1) v3186_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3186_pg : Scalar.QComplex := ((-93086332810963027167449 : Int)/10^30,(133139554363388366292 : Int)/10^30)
theorem v3186_pg_checked : Scalar.distance (sourceCoefficient 41 71 1 2) v3186_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3186_mb : Scalar.QComplex := ((-989478213500339759648216 : Int)/10^30,(-431476369087351272749254156 : Int)/10^30)
theorem v3186_mb_checked : Scalar.distance (sourceCoefficient 41 71 3 1) v3186_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3186_mg : Scalar.QComplex := ((-93086183257228033400133 : Int)/10^30,(213468817552509948637 : Int)/10^30)
theorem v3186_mg_checked : Scalar.distance (sourceCoefficient 41 71 3 2) v3186_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3186_upper : Scalar.QComplex := ((999995019237958747922339715111 : Int)/10^30,(-3156184290328060634713252169 : Int)/10^30)
theorem v3186_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 71 5) 1) 14) v3186_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3186 : Material (41 : Basis) (71 : Basis) where
  plus := ![v3186_pa,v3186_pb,v3186_pg]
  minus := ![(Primitive.Addresses.material3186 1).one,v3186_mb,v3186_mg]
  upper := v3186_upper
  lower := (Primitive.Addresses.material3186 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3186_pa_checked.trans (by decide +kernel)
    · exact v3186_pb_checked.trans (by decide +kernel)
    · exact v3186_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 71 Primitive.Addresses.material3186
    · exact v3186_mb_checked.trans (by decide +kernel)
    · exact v3186_mg_checked.trans (by decide +kernel)
  upper_error := v3186_upper_checked
  lower_error := reuse_lower_error 41 71 Primitive.Addresses.material3186

def v3187_pa : Scalar.QComplex := ((999998939097201794225438790558 : Int)/10^30,(-1456641503904375876402090955 : Int)/10^30)
theorem v3187_pa_checked : Scalar.distance (sourceCoefficient 41 72 1 0) v3187_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3187_pb : Scalar.QComplex := ((-628508037017547409582918 : Int)/10^30,(-431477043972016231270841903 : Int)/10^30)
theorem v3187_pb_checked : Scalar.distance (sourceCoefficient 41 72 1 1) v3187_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3187_pg : Scalar.QComplex := ((-93086329062363314392274 : Int)/10^30,(135593554209919589405 : Int)/10^30)
theorem v3187_pg_checked : Scalar.distance (sourceCoefficient 41 72 1 2) v3187_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3187_mb : Scalar.QComplex := ((-1000853058938457542200271 : Int)/10^30,(-431476340939264290458279049 : Int)/10^30)
theorem v3187_mb_checked : Scalar.distance (sourceCoefficient 41 72 3 1) v3187_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3187_mg : Scalar.QComplex := ((-93086177390938372893747 : Int)/10^30,(215922813250432154092 : Int)/10^30)
theorem v3187_mg_checked : Scalar.distance (sourceCoefficient 41 72 3 2) v3187_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3187_upper : Scalar.QComplex := ((999994935685159882033153935596 : Int)/10^30,(-3182546784094639802324388045 : Int)/10^30)
theorem v3187_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 72 5) 1) 14) v3187_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3187 : Material (41 : Basis) (72 : Basis) where
  plus := ![v3187_pa,v3187_pb,v3187_pg]
  minus := ![(Primitive.Addresses.material3187 1).one,v3187_mb,v3187_mg]
  upper := v3187_upper
  lower := (Primitive.Addresses.material3187 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3187_pa_checked.trans (by decide +kernel)
    · exact v3187_pb_checked.trans (by decide +kernel)
    · exact v3187_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 72 Primitive.Addresses.material3187
    · exact v3187_mb_checked.trans (by decide +kernel)
    · exact v3187_mg_checked.trans (by decide +kernel)
  upper_error := v3187_upper_checked
  lower_error := reuse_lower_error 41 72 Primitive.Addresses.material3187

def v3188_pa : Scalar.QComplex := ((999998925287812316624231351297 : Int)/10^30,(-1466091136444274797768275208 : Int)/10^30)
theorem v3188_pa_checked : Scalar.distance (sourceCoefficient 41 73 1 0) v3188_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3188_pb : Scalar.QComplex := ((-632585339817158520144176 : Int)/10^30,(-431477037303559343888139305 : Int)/10^30)
theorem v3188_pb_checked : Scalar.distance (sourceCoefficient 41 73 1 1) v3188_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3188_pg : Scalar.QComplex := ((-93086327700307586498545 : Int)/10^30,(136473186634965095038 : Int)/10^30)
theorem v3188_pg_checked : Scalar.distance (sourceCoefficient 41 73 1 2) v3188_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3188_mb : Scalar.QComplex := ((-1004930354465324520860826 : Int)/10^30,(-431476330752281204883697266 : Int)/10^30)
theorem v3188_mb_checked : Scalar.distance (sourceCoefficient 41 73 3 1) v3188_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3188_mg : Scalar.QComplex := ((-93086175269799986515108 : Int)/10^30,(216802444172557558233 : Int)/10^30)
theorem v3188_mg_checked : Scalar.distance (sourceCoefficient 41 73 3 2) v3188_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3188_upper : Scalar.QComplex := ((999994905566582471997311280353 : Int)/10^30,(-3191996378726667627012306501 : Int)/10^30)
theorem v3188_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 73 5) 1) 14) v3188_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3188 : Material (41 : Basis) (73 : Basis) where
  plus := ![v3188_pa,v3188_pb,v3188_pg]
  minus := ![(Primitive.Addresses.material3188 1).one,v3188_mb,v3188_mg]
  upper := v3188_upper
  lower := (Primitive.Addresses.material3188 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3188_pa_checked.trans (by decide +kernel)
    · exact v3188_pb_checked.trans (by decide +kernel)
    · exact v3188_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 73 Primitive.Addresses.material3188
    · exact v3188_mb_checked.trans (by decide +kernel)
    · exact v3188_mg_checked.trans (by decide +kernel)
  upper_error := v3188_upper_checked
  lower_error := reuse_lower_error 41 73 Primitive.Addresses.material3188

def v3189_pa : Scalar.QComplex := ((999998909642082843658866225612 : Int)/10^30,(-1476724295673466178932453976 : Int)/10^30)
theorem v3189_pa_checked : Scalar.distance (sourceCoefficient 41 74 1 0) v3189_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3189_pb : Scalar.QComplex := ((-637173307586796633845705 : Int)/10^30,(-431477029738480004742073237 : Int)/10^30)
theorem v3189_pb_checked : Scalar.distance (sourceCoefficient 41 74 1 1) v3189_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3189_pg : Scalar.QComplex := ((-93086326156064578761746 : Int)/10^30,(137462989313503731390 : Int)/10^30)
theorem v3189_pg_checked : Scalar.distance (sourceCoefficient 41 74 1 2) v3189_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3189_mb : Scalar.QComplex := ((-1009518313998329802282900 : Int)/10^30,(-431476319227995131762433339 : Int)/10^30)
theorem v3189_mb_checked : Scalar.distance (sourceCoefficient 41 74 3 1) v3189_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3189_mg : Scalar.QComplex := ((-93086172871402421249503 : Int)/10^30,(217792245149935255594 : Int)/10^30)
theorem v3189_mg_checked : Scalar.distance (sourceCoefficient 41 74 3 2) v3189_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3189_upper : Scalar.QComplex := ((999994871569008104593771108753 : Int)/10^30,(-3202629495115907694072627887 : Int)/10^30)
theorem v3189_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 74 5) 1) 14) v3189_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3189 : Material (41 : Basis) (74 : Basis) where
  plus := ![v3189_pa,v3189_pb,v3189_pg]
  minus := ![(Primitive.Addresses.material3189 1).one,v3189_mb,v3189_mg]
  upper := v3189_upper
  lower := (Primitive.Addresses.material3189 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3189_pa_checked.trans (by decide +kernel)
    · exact v3189_pb_checked.trans (by decide +kernel)
    · exact v3189_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 74 Primitive.Addresses.material3189
    · exact v3189_mb_checked.trans (by decide +kernel)
    · exact v3189_mg_checked.trans (by decide +kernel)
  upper_error := v3189_upper_checked
  lower_error := reuse_lower_error 41 74 Primitive.Addresses.material3189

def v3190_pa : Scalar.QComplex := ((999998887654478090225669793864 : Int)/10^30,(-1491539408298348833031642738 : Int)/10^30)
theorem v3190_pa_checked : Scalar.distance (sourceCoefficient 41 75 1 0) v3190_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3190_pb : Scalar.QComplex := ((-643565693614733763526025 : Int)/10^30,(-431477019089653011228856643 : Int)/10^30)
theorem v3190_pb_checked : Scalar.distance (sourceCoefficient 41 75 1 1) v3190_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3190_pg : Scalar.QComplex := ((-93086323984008342800194 : Int)/10^30,(138842075036136620327 : Int)/10^30)
theorem v3190_pg_checked : Scalar.distance (sourceCoefficient 41 75 1 2) v3190_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3190_mb : Scalar.QComplex := ((-1015910688456631377250515 : Int)/10^30,(-431476303062830863563698555 : Int)/10^30)
theorem v3190_mb_checked : Scalar.distance (sourceCoefficient 41 75 3 1) v3190_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3190_mg : Scalar.QComplex := ((-93086169509258127126824 : Int)/10^30,(219171328484684796810 : Int)/10^30)
theorem v3190_mg_checked : Scalar.distance (sourceCoefficient 41 75 3 2) v3190_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3190_upper : Scalar.QComplex := ((999994824011895725085996925166 : Int)/10^30,(-3217444547726809294283600986 : Int)/10^30)
theorem v3190_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 75 5) 1) 14) v3190_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3190 : Material (41 : Basis) (75 : Basis) where
  plus := ![v3190_pa,v3190_pb,v3190_pg]
  minus := ![(Primitive.Addresses.material3190 1).one,v3190_mb,v3190_mg]
  upper := v3190_upper
  lower := (Primitive.Addresses.material3190 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3190_pa_checked.trans (by decide +kernel)
    · exact v3190_pb_checked.trans (by decide +kernel)
    · exact v3190_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 75 Primitive.Addresses.material3190
    · exact v3190_mb_checked.trans (by decide +kernel)
    · exact v3190_mg_checked.trans (by decide +kernel)
  upper_error := v3190_upper_checked
  lower_error := reuse_lower_error 41 75 Primitive.Addresses.material3190

def v3191_pa : Scalar.QComplex := ((999998869037112694867176532484 : Int)/10^30,(-1503969579324400160047130217 : Int)/10^30)
theorem v3191_pa_checked : Scalar.distance (sourceCoefficient 41 76 1 0) v3191_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3191_pb : Scalar.QComplex := ((-648929031219220043569322 : Int)/10^30,(-431477010057660234521393782 : Int)/10^30)
theorem v3191_pb_checked : Scalar.distance (sourceCoefficient 41 76 1 1) v3191_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3191_pg : Scalar.QComplex := ((-93086322143220794717494 : Int)/10^30,(139999155088444033243 : Int)/10^30)
theorem v3191_pg_checked : Scalar.distance (sourceCoefficient 41 76 1 2) v3191_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3191_mb : Scalar.QComplex := ((-1021274016269898970061559 : Int)/10^30,(-431476289402522652967004049 : Int)/10^30)
theorem v3191_mb_checked : Scalar.distance (sourceCoefficient 41 76 3 1) v3191_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3191_mg : Scalar.QComplex := ((-93086166669963292263191 : Int)/10^30,(220328406517641677079 : Int)/10^30)
theorem v3191_mg_checked : Scalar.distance (sourceCoefficient 41 76 3 2) v3191_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3191_upper : Scalar.QComplex := ((999994783941210523448435976698 : Int)/10^30,(-3229874668107697310260853681 : Int)/10^30)
theorem v3191_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 76 5) 1) 14) v3191_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3191 : Material (41 : Basis) (76 : Basis) where
  plus := ![v3191_pa,v3191_pb,v3191_pg]
  minus := ![(Primitive.Addresses.material3191 1).one,v3191_mb,v3191_mg]
  upper := v3191_upper
  lower := (Primitive.Addresses.material3191 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3191_pa_checked.trans (by decide +kernel)
    · exact v3191_pb_checked.trans (by decide +kernel)
    · exact v3191_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 76 Primitive.Addresses.material3191
    · exact v3191_mb_checked.trans (by decide +kernel)
    · exact v3191_mg_checked.trans (by decide +kernel)
  upper_error := v3191_upper_checked
  lower_error := reuse_lower_error 41 76 Primitive.Addresses.material3191

def v3192_pa : Scalar.QComplex := ((999998864705008759501153041824 : Int)/10^30,(-1506847269495578492801581865 : Int)/10^30)
theorem v3192_pa_checked : Scalar.distance (sourceCoefficient 41 77 1 0) v3192_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3192_pb : Scalar.QComplex := ((-650170689421142694143673 : Int)/10^30,(-431477007954005733847203280 : Int)/10^30)
theorem v3192_pb_checked : Scalar.distance (sourceCoefficient 41 77 1 1) v3192_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3192_pg : Scalar.QComplex := ((-93086321714670832229705 : Int)/10^30,(140267028947594120185 : Int)/10^30)
theorem v3192_pg_checked : Scalar.distance (sourceCoefficient 41 77 1 2) v3192_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3192_mb : Scalar.QComplex := ((-1022515672194136436476722 : Int)/10^30,(-431476286227373829529763062 : Int)/10^30)
theorem v3192_mb_checked : Scalar.distance (sourceCoefficient 41 77 3 1) v3192_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3192_mg : Scalar.QComplex := ((-93086166010250413488372 : Int)/10^30,(220596279907230767367 : Int)/10^30)
theorem v3192_mg_checked : Scalar.distance (sourceCoefficient 41 77 3 2) v3192_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3192_upper : Scalar.QComplex := ((999994774642480866801561970450 : Int)/10^30,(-3232752346516075783235775967 : Int)/10^30)
theorem v3192_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 77 5) 1) 14) v3192_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3192 : Material (41 : Basis) (77 : Basis) where
  plus := ![v3192_pa,v3192_pb,v3192_pg]
  minus := ![(Primitive.Addresses.material3192 1).one,v3192_mb,v3192_mg]
  upper := v3192_upper
  lower := (Primitive.Addresses.material3192 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3192_pa_checked.trans (by decide +kernel)
    · exact v3192_pb_checked.trans (by decide +kernel)
    · exact v3192_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 77 Primitive.Addresses.material3192
    · exact v3192_mb_checked.trans (by decide +kernel)
    · exact v3192_mg_checked.trans (by decide +kernel)
  upper_error := v3192_upper_checked
  lower_error := reuse_lower_error 41 77 Primitive.Addresses.material3192

def v3193_pa : Scalar.QComplex := ((999998838487532207415924245361 : Int)/10^30,(-1524146838881987549388832368 : Int)/10^30)
theorem v3193_pa_checked : Scalar.distance (sourceCoefficient 41 78 1 0) v3193_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3193_pb : Scalar.QComplex := ((-657635062146728921763494 : Int)/10^30,(-431476995207234516577794903 : Int)/10^30)
theorem v3193_pb_checked : Scalar.distance (sourceCoefficient 41 78 1 1) v3193_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3193_pg : Scalar.QComplex := ((-93086319119438809990784 : Int)/10^30,(141877383821402787417 : Int)/10^30)
theorem v3193_pg_checked : Scalar.distance (sourceCoefficient 41 78 1 2) v3193_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3193_mb : Scalar.QComplex := ((-1029980031140506092435422 : Int)/10^30,(-431476267039189879152786397 : Int)/10^30)
theorem v3193_mb_checked : Scalar.distance (sourceCoefficient 41 78 3 1) v3193_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3193_mg : Scalar.QComplex := ((-93086162025355629167222 : Int)/10^30,(222206631941862367946 : Int)/10^30)
theorem v3193_mg_checked : Scalar.distance (sourceCoefficient 41 78 3 2) v3193_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3193_upper : Scalar.QComplex := ((999994718567556006301123190275 : Int)/10^30,(-3250051844887822290932045687 : Int)/10^30)
theorem v3193_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 78 5) 1) 14) v3193_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3193 : Material (41 : Basis) (78 : Basis) where
  plus := ![v3193_pa,v3193_pb,v3193_pg]
  minus := ![(Primitive.Addresses.material3193 1).one,v3193_mb,v3193_mg]
  upper := v3193_upper
  lower := (Primitive.Addresses.material3193 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3193_pa_checked.trans (by decide +kernel)
    · exact v3193_pb_checked.trans (by decide +kernel)
    · exact v3193_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 78 Primitive.Addresses.material3193
    · exact v3193_mb_checked.trans (by decide +kernel)
    · exact v3193_mg_checked.trans (by decide +kernel)
  upper_error := v3193_upper_checked
  lower_error := reuse_lower_error 41 78 Primitive.Addresses.material3193

def v3194_pa : Scalar.QComplex := ((999998829971689826002686738368 : Int)/10^30,(-1529723913450315392533454874 : Int)/10^30)
theorem v3194_pa_checked : Scalar.distance (sourceCoefficient 41 79 1 0) v3194_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3194_pb : Scalar.QComplex := ((-660041443597082541018736 : Int)/10^30,(-431476991061201325235224386 : Int)/10^30)
theorem v3194_pb_checked : Scalar.distance (sourceCoefficient 41 79 1 1) v3194_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3194_pg : Scalar.QComplex := ((-93086318275854075790239 : Int)/10^30,(142396533689596799662 : Int)/10^30)
theorem v3194_pg_checked : Scalar.distance (sourceCoefficient 41 79 1 2) v3194_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3194_mb : Scalar.QComplex := ((-1032386408117014006933294 : Int)/10^30,(-431476260816559419309974263 : Int)/10^30)
theorem v3194_mb_checked : Scalar.distance (sourceCoefficient 41 79 3 1) v3194_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3194_mg : Scalar.QComplex := ((-93086160733768254462491 : Int)/10^30,(222725780888777525972 : Int)/10^30)
theorem v3194_mg_checked : Scalar.distance (sourceCoefficient 41 79 3 2) v3194_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3194_upper : Scalar.QComplex := ((999994700426201551553502260311 : Int)/10^30,(-3255628896452181294618213027 : Int)/10^30)
theorem v3194_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 79 5) 1) 14) v3194_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3194 : Material (41 : Basis) (79 : Basis) where
  plus := ![v3194_pa,v3194_pb,v3194_pg]
  minus := ![(Primitive.Addresses.material3194 1).one,v3194_mb,v3194_mg]
  upper := v3194_upper
  lower := (Primitive.Addresses.material3194 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3194_pa_checked.trans (by decide +kernel)
    · exact v3194_pb_checked.trans (by decide +kernel)
    · exact v3194_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 79 Primitive.Addresses.material3194
    · exact v3194_mb_checked.trans (by decide +kernel)
    · exact v3194_mg_checked.trans (by decide +kernel)
  upper_error := v3194_upper_checked
  lower_error := reuse_lower_error 41 79 Primitive.Addresses.material3194

def v3195_pa : Scalar.QComplex := ((999998816606859696103576449470 : Int)/10^30,(-1538435855077639669863761006 : Int)/10^30)
theorem v3195_pa_checked : Scalar.distance (sourceCoefficient 41 80 1 0) v3195_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3195_pb : Scalar.QComplex := ((-663800449207674792344890 : Int)/10^30,(-431476984548879315285677990 : Int)/10^30)
theorem v3195_pb_checked : Scalar.distance (sourceCoefficient 41 80 1 1) v3195_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3195_pg : Scalar.QComplex := ((-93086316951331742204944 : Int)/10^30,(143207497085819924574 : Int)/10^30)
theorem v3195_pg_checked : Scalar.distance (sourceCoefficient 41 80 1 2) v3195_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3195_mb : Scalar.QComplex := ((-1036145406708116083901611 : Int)/10^30,(-431476251060387291582441701 : Int)/10^30)
theorem v3195_mb_checked : Scalar.distance (sourceCoefficient 41 80 3 1) v3195_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3195_mg : Scalar.QComplex := ((-93086158709421527552353 : Int)/10^30,(223536742840038795999 : Int)/10^30)
theorem v3195_mg_checked : Scalar.distance (sourceCoefficient 41 80 3 2) v3195_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3195_upper : Scalar.QComplex := ((999994672025370419407848996560 : Int)/10^30,(-3264340802037607538313232169 : Int)/10^30)
theorem v3195_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 80 5) 1) 14) v3195_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3195 : Material (41 : Basis) (80 : Basis) where
  plus := ![v3195_pa,v3195_pb,v3195_pg]
  minus := ![(Primitive.Addresses.material3195 1).one,v3195_mb,v3195_mg]
  upper := v3195_upper
  lower := (Primitive.Addresses.material3195 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3195_pa_checked.trans (by decide +kernel)
    · exact v3195_pb_checked.trans (by decide +kernel)
    · exact v3195_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 80 Primitive.Addresses.material3195
    · exact v3195_mb_checked.trans (by decide +kernel)
    · exact v3195_mg_checked.trans (by decide +kernel)
  upper_error := v3195_upper_checked
  lower_error := reuse_lower_error 41 80 Primitive.Addresses.material3195

def v3196_pa : Scalar.QComplex := ((999998775906333677362924734796 : Int)/10^30,(-1564667962936536327717609002 : Int)/10^30)
theorem v3196_pa_checked : Scalar.distance (sourceCoefficient 41 81 1 0) v3196_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3196_pb : Scalar.QComplex := ((-675119009782950256725442 : Int)/10^30,(-431476964676261784040369413 : Int)/10^30)
theorem v3196_pb_checked : Scalar.distance (sourceCoefficient 41 81 1 1) v3196_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3196_pg : Scalar.QComplex := ((-93086312913351373582573 : Int)/10^30,(145649349891853196577 : Int)/10^30)
theorem v3196_pg_checked : Scalar.distance (sourceCoefficient 41 81 1 2) v3196_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3196_mb : Scalar.QComplex := ((-1047463945919800262338332 : Int)/10^30,(-431476221420369152402931690 : Int)/10^30)
theorem v3196_mb_checked : Scalar.distance (sourceCoefficient 41 81 3 1) v3196_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3196_mg : Scalar.QComplex := ((-93086152564233667815751 : Int)/10^30,(225978591252263475893 : Int)/10^30)
theorem v3196_mg_checked : Scalar.distance (sourceCoefficient 41 81 3 2) v3196_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3196_upper : Scalar.QComplex := ((999994586050666613099359046596 : Int)/10^30,(-3290572800581445394720169454 : Int)/10^30)
theorem v3196_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 81 5) 1) 14) v3196_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3196 : Material (41 : Basis) (81 : Basis) where
  plus := ![v3196_pa,v3196_pb,v3196_pg]
  minus := ![(Primitive.Addresses.material3196 1).one,v3196_mb,v3196_mg]
  upper := v3196_upper
  lower := (Primitive.Addresses.material3196 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3196_pa_checked.trans (by decide +kernel)
    · exact v3196_pb_checked.trans (by decide +kernel)
    · exact v3196_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 81 Primitive.Addresses.material3196
    · exact v3196_mb_checked.trans (by decide +kernel)
    · exact v3196_mg_checked.trans (by decide +kernel)
  upper_error := v3196_upper_checked
  lower_error := reuse_lower_error 41 81 Primitive.Addresses.material3196

def v3197_pa : Scalar.QComplex := ((999998760303724713953876730177 : Int)/10^30,(-1574608209595401953442022898 : Int)/10^30)
theorem v3197_pa_checked : Scalar.distance (sourceCoefficient 41 82 1 0) v3197_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3197_pb : Scalar.QComplex := ((-679408001069798368027927 : Int)/10^30,(-431476957042415507420091215 : Int)/10^30)
theorem v3197_pb_checked : Scalar.distance (sourceCoefficient 41 82 1 1) v3197_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3197_pg : Scalar.QComplex := ((-93086311363697485346685 : Int)/10^30,(146574651782281682488 : Int)/10^30)
theorem v3197_pg_checked : Scalar.distance (sourceCoefficient 41 82 1 2) v3197_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3197_mb : Scalar.QComplex := ((-1051752929021995379912000 : Int)/10^30,(-431476210085319406659375647 : Int)/10^30)
theorem v3197_mb_checked : Scalar.distance (sourceCoefficient 41 82 3 1) v3197_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3197_mg : Scalar.QComplex := ((-93086150216086499197176 : Int)/10^30,(226903891460878267885 : Int)/10^30)
theorem v3197_mg_checked : Scalar.distance (sourceCoefficient 41 82 3 2) v3197_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3197_upper : Scalar.QComplex := ((999994553292116926874115809539 : Int)/10^30,(-3300513005506793672244859494 : Int)/10^30)
theorem v3197_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 82 5) 1) 14) v3197_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3197 : Material (41 : Basis) (82 : Basis) where
  plus := ![v3197_pa,v3197_pb,v3197_pg]
  minus := ![(Primitive.Addresses.material3197 1).one,v3197_mb,v3197_mg]
  upper := v3197_upper
  lower := (Primitive.Addresses.material3197 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3197_pa_checked.trans (by decide +kernel)
    · exact v3197_pb_checked.trans (by decide +kernel)
    · exact v3197_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 82 Primitive.Addresses.material3197
    · exact v3197_mb_checked.trans (by decide +kernel)
    · exact v3197_mg_checked.trans (by decide +kernel)
  upper_error := v3197_upper_checked
  lower_error := reuse_lower_error 41 82 Primitive.Addresses.material3197

def v3198_pa : Scalar.QComplex := ((999998738846409359182468152542 : Int)/10^30,(-1588176813447815034391770839 : Int)/10^30)
theorem v3198_pa_checked : Scalar.distance (sourceCoefficient 41 83 1 0) v3198_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3198_pb : Scalar.QComplex := ((-685262546238054951105811 : Int)/10^30,(-431476946530330919561048427 : Int)/10^30)
theorem v3198_pb_checked : Scalar.distance (sourceCoefficient 41 83 1 1) v3198_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3198_pg : Scalar.QComplex := ((-93086309231072941563673 : Int)/10^30,(147837704416275110354 : Int)/10^30)
theorem v3198_pg_checked : Scalar.distance (sourceCoefficient 41 83 1 2) v3198_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3198_mb : Scalar.QComplex := ((-1057607462938881678308060 : Int)/10^30,(-431476194521029931650576161 : Int)/10^30)
theorem v3198_mb_checked : Scalar.distance (sourceCoefficient 41 83 3 1) v3198_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3198_mg : Scalar.QComplex := ((-93086146993505212130355 : Int)/10^30,(228166941784220544317 : Int)/10^30)
theorem v3198_mg_checked : Scalar.distance (sourceCoefficient 41 83 3 2) v3198_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3198_upper : Scalar.QComplex := ((999994508416654215114358331363 : Int)/10^30,(-3314081552116985485305391206 : Int)/10^30)
theorem v3198_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 83 5) 1) 14) v3198_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3198 : Material (41 : Basis) (83 : Basis) where
  plus := ![v3198_pa,v3198_pb,v3198_pg]
  minus := ![(Primitive.Addresses.material3198 1).one,v3198_mb,v3198_mg]
  upper := v3198_upper
  lower := (Primitive.Addresses.material3198 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3198_pa_checked.trans (by decide +kernel)
    · exact v3198_pb_checked.trans (by decide +kernel)
    · exact v3198_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 83 Primitive.Addresses.material3198
    · exact v3198_mb_checked.trans (by decide +kernel)
    · exact v3198_mg_checked.trans (by decide +kernel)
  upper_error := v3198_upper_checked
  lower_error := reuse_lower_error 41 83 Primitive.Addresses.material3198

def v3199_pa : Scalar.QComplex := ((999998682421997609353226271961 : Int)/10^30,(-1623315825330826115928314941 : Int)/10^30)
theorem v3199_pa_checked : Scalar.distance (sourceCoefficient 41 84 1 0) v3199_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3199_pb : Scalar.QComplex := ((-700424233440203314987363 : Int)/10^30,(-431476918814548709078279123 : Int)/10^30)
theorem v3199_pb_checked : Scalar.distance (sourceCoefficient 41 84 1 1) v3199_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3199_pg : Scalar.QComplex := ((-93086303615215025799196 : Int)/10^30,(151108668877586726069 : Int)/10^30)
theorem v3199_pg_checked : Scalar.distance (sourceCoefficient 41 84 1 2) v3199_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3199_mb : Scalar.QComplex := ((-1072769120578169198339607 : Int)/10^30,(-431476153721404842608899415 : Int)/10^30)
theorem v3199_mb_checked : Scalar.distance (sourceCoefficient 41 84 3 1) v3199_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3199_mg : Scalar.QComplex := ((-93086138554954376065121 : Int)/10^30,(231437900181370148172 : Int)/10^30)
theorem v3199_mg_checked : Scalar.distance (sourceCoefficient 41 84 3 2) v3199_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3199_upper : Scalar.QComplex := ((999994391345579778997621179304 : Int)/10^30,(-3349220414281150187832040542 : Int)/10^30)
theorem v3199_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 84 5) 1) 14) v3199_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3199 : Material (41 : Basis) (84 : Basis) where
  plus := ![v3199_pa,v3199_pb,v3199_pg]
  minus := ![(Primitive.Addresses.material3199 1).one,v3199_mb,v3199_mg]
  upper := v3199_upper
  lower := (Primitive.Addresses.material3199 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3199_pa_checked.trans (by decide +kernel)
    · exact v3199_pb_checked.trans (by decide +kernel)
    · exact v3199_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 84 Primitive.Addresses.material3199
    · exact v3199_mb_checked.trans (by decide +kernel)
    · exact v3199_mg_checked.trans (by decide +kernel)
  upper_error := v3199_upper_checked
  lower_error := reuse_lower_error 41 84 Primitive.Addresses.material3199

def v3200_pa : Scalar.QComplex := ((999998550962828809829521028792 : Int)/10^30,(-1702372533457826165455814822 : Int)/10^30)
theorem v3200_pa_checked : Scalar.distance (sourceCoefficient 41 85 1 0) v3200_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v3200_pb : Scalar.QComplex := ((-734535409206433928615707 : Int)/10^30,(-431476853861916156528966909 : Int)/10^30)
theorem v3200_pb_checked : Scalar.distance (sourceCoefficient 41 85 1 1) v3200_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3200_pg : Scalar.QComplex := ((-93086290490282122962758 : Int)/10^30,(158467773797827397792 : Int)/10^30)
theorem v3200_pg_checked : Scalar.distance (sourceCoefficient 41 85 1 2) v3200_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3200_mb : Scalar.QComplex := ((-1106880227592053581579420 : Int)/10^30,(-431476059332388098962139891 : Int)/10^30)
theorem v3200_mb_checked : Scalar.distance (sourceCoefficient 41 85 3 1) v3200_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v3200_mg : Scalar.QComplex := ((-93086119079450255855253 : Int)/10^30,(238796991035253760266 : Int)/10^30)
theorem v3200_mg_checked : Scalar.distance (sourceCoefficient 41 85 3 2) v3200_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v3200_upper : Scalar.QComplex := ((999994123441900513798416373906 : Int)/10^30,(-3428276777775870670137072222 : Int)/10^30)
theorem v3200_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 41 85 5) 1) 14) v3200_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material3200 : Material (41 : Basis) (85 : Basis) where
  plus := ![v3200_pa,v3200_pb,v3200_pg]
  minus := ![(Primitive.Addresses.material3200 1).one,v3200_mb,v3200_mg]
  upper := v3200_upper
  lower := (Primitive.Addresses.material3200 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v3200_pa_checked.trans (by decide +kernel)
    · exact v3200_pb_checked.trans (by decide +kernel)
    · exact v3200_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 41 85 Primitive.Addresses.material3200
    · exact v3200_mb_checked.trans (by decide +kernel)
    · exact v3200_mg_checked.trans (by decide +kernel)
  upper_error := v3200_upper_checked
  lower_error := reuse_lower_error 41 85 Primitive.Addresses.material3200

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
