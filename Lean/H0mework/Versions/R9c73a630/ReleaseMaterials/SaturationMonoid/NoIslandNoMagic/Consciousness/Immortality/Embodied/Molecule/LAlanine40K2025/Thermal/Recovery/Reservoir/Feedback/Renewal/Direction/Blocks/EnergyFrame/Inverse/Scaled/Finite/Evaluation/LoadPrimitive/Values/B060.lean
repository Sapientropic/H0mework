import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B040

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v961_pa : Scalar.QComplex := ((999999888418109289401255717656 : Int)/10^30,(-472402126340133183372881797 : Int)/10^30)
theorem v961_pa_checked : Scalar.distance (sourceCoefficient 10 47 1 0) v961_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v961_pb : Scalar.QComplex := ((-203830886999360185186039 : Int)/10^30,(-431477448746207866099593708 : Int)/10^30)
theorem v961_pb_checked : Scalar.distance (sourceCoefficient 10 47 1 1) v961_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v961_pg : Scalar.QComplex := ((-93086416909553591759126 : Int)/10^30,(43974226188184546383 : Int)/10^30)
theorem v961_pg_checked : Scalar.distance (sourceCoefficient 10 47 1 2) v961_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v961_mb : Scalar.QComplex := ((-576176416348879002148275 : Int)/10^30,(-431477112190558926233437122 : Int)/10^30)
theorem v961_mb_checked : Scalar.distance (sourceCoefficient 10 47 3 1) v961_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v961_mg : Scalar.QComplex := ((-93086344301449642138563 : Int)/10^30,(124303595150928862494 : Int)/10^30)
theorem v961_mg_checked : Scalar.distance (sourceCoefficient 10 47 3 2) v961_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v961_upper : Scalar.QComplex := ((999997583712529652273871919025 : Int)/10^30,(-2198310510881097728994650683 : Int)/10^30)
theorem v961_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 47 5) 1) 14) v961_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material961 : Material (10 : Basis) (47 : Basis) where
  plus := ![v961_pa,v961_pb,v961_pg]
  minus := ![(Primitive.Addresses.material961 1).one,v961_mb,v961_mg]
  upper := v961_upper
  lower := (Primitive.Addresses.material961 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v961_pa_checked.trans (by decide +kernel)
    · exact v961_pb_checked.trans (by decide +kernel)
    · exact v961_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 47 Primitive.Addresses.material961
    · exact v961_mb_checked.trans (by decide +kernel)
    · exact v961_mg_checked.trans (by decide +kernel)
  upper_error := v961_upper_checked
  lower_error := reuse_lower_error 10 47 Primitive.Addresses.material961

def v962_pa : Scalar.QComplex := ((999999875083632741090740861077 : Int)/10^30,(-499832690921391924431939664 : Int)/10^30)
theorem v962_pa_checked : Scalar.distance (sourceCoefficient 10 48 1 0) v962_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v962_pb : Scalar.QComplex := ((-215666557174361555842791 : Int)/10^30,(-431477440654229448242616747 : Int)/10^30)
theorem v962_pb_checked : Scalar.distance (sourceCoefficient 10 48 1 1) v962_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v962_pg : Scalar.QComplex := ((-93086415416047445379561 : Int)/10^30,(46527639317693215929 : Int)/10^30)
theorem v962_pg_checked : Scalar.distance (sourceCoefficient 10 48 1 2) v962_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v962_mb : Scalar.QComplex := ((-588012075133906524371564 : Int)/10^30,(-431477093884933219160273320 : Int)/10^30)
theorem v962_mb_checked : Scalar.distance (sourceCoefficient 10 48 3 1) v962_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v962_mg : Scalar.QComplex := ((-93086340604463522551910 : Int)/10^30,(126857006040856587874 : Int)/10^30)
theorem v962_mg_checked : Scalar.distance (sourceCoefficient 10 48 3 2) v962_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v962_upper : Scalar.QComplex := ((999997523035406978227073087427 : Int)/10^30,(-2225741011593655918612071710 : Int)/10^30)
theorem v962_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 48 5) 1) 14) v962_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material962 : Material (10 : Basis) (48 : Basis) where
  plus := ![v962_pa,v962_pb,v962_pg]
  minus := ![(Primitive.Addresses.material962 1).one,v962_mb,v962_mg]
  upper := v962_upper
  lower := (Primitive.Addresses.material962 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v962_pa_checked.trans (by decide +kernel)
    · exact v962_pb_checked.trans (by decide +kernel)
    · exact v962_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 48 Primitive.Addresses.material962
    · exact v962_mb_checked.trans (by decide +kernel)
    · exact v962_mg_checked.trans (by decide +kernel)
  upper_error := v962_upper_checked
  lower_error := reuse_lower_error 10 48 Primitive.Addresses.material962

def v963_pa : Scalar.QComplex := ((999999863825282775161818950187 : Int)/10^30,(-521871072110844970175601821 : Int)/10^30)
theorem v963_pa_checked : Scalar.distance (sourceCoefficient 10 49 1 0) v963_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v963_pb : Scalar.QComplex := ((-225175621652596679254514 : Int)/10^30,(-431477433839335266890679287 : Int)/10^30)
theorem v963_pb_checked : Scalar.distance (sourceCoefficient 10 49 1 1) v963_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v963_pg : Scalar.QComplex := ((-93086414156929196203698 : Int)/10^30,(48579113370277802883 : Int)/10^30)
theorem v963_pg_checked : Scalar.distance (sourceCoefficient 10 49 1 2) v963_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v963_mb : Scalar.QComplex := ((-597521130190535609754100 : Int)/10^30,(-431477078864147202953866310 : Int)/10^30)
theorem v963_mb_checked : Scalar.distance (sourceCoefficient 10 49 3 1) v963_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v963_mg : Scalar.QComplex := ((-93086337575016029784283 : Int)/10^30,(128908478243021287596 : Int)/10^30)
theorem v963_mg_checked : Scalar.distance (sourceCoefficient 10 49 3 2) v963_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v963_upper : Scalar.QComplex := ((999997473740827153615753041120 : Int)/10^30,(-2247779340528638301111172082 : Int)/10^30)
theorem v963_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 49 5) 1) 14) v963_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material963 : Material (10 : Basis) (49 : Basis) where
  plus := ![v963_pa,v963_pb,v963_pg]
  minus := ![(Primitive.Addresses.material963 1).one,v963_mb,v963_mg]
  upper := v963_upper
  lower := (Primitive.Addresses.material963 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v963_pa_checked.trans (by decide +kernel)
    · exact v963_pb_checked.trans (by decide +kernel)
    · exact v963_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 49 Primitive.Addresses.material963
    · exact v963_mb_checked.trans (by decide +kernel)
    · exact v963_mg_checked.trans (by decide +kernel)
  upper_error := v963_upper_checked
  lower_error := reuse_lower_error 10 49 Primitive.Addresses.material963

def v964_pa : Scalar.QComplex := ((999999862478002030478575483266 : Int)/10^30,(-524446352858653144723492509 : Int)/10^30)
theorem v964_pa_checked : Scalar.distance (sourceCoefficient 10 50 1 0) v964_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v964_pb : Scalar.QComplex := ((-226286797210057338303096 : Int)/10^30,(-431477433024751818863182541 : Int)/10^30)
theorem v964_pb_checked : Scalar.distance (sourceCoefficient 10 50 1 1) v964_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v964_pg : Scalar.QComplex := ((-93086414006353803019063 : Int)/10^30,(48818837039986907220 : Int)/10^30)
theorem v964_pg_checked : Scalar.distance (sourceCoefficient 10 50 1 2) v964_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v964_mb : Scalar.QComplex := ((-598632304631305997357227 : Int)/10^30,(-431477077090669597633798947 : Int)/10^30)
theorem v964_mb_checked : Scalar.distance (sourceCoefficient 10 50 3 1) v964_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v964_mg : Scalar.QComplex := ((-93086337217569962460081 : Int)/10^30,(129148201693530531133 : Int)/10^30)
theorem v964_mg_checked : Scalar.distance (sourceCoefficient 10 50 3 2) v964_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v964_upper : Scalar.QComplex := ((999997467948847472476448948833 : Int)/10^30,(-2250354615115583974556969805 : Int)/10^30)
theorem v964_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 50 5) 1) 14) v964_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material964 : Material (10 : Basis) (50 : Basis) where
  plus := ![v964_pa,v964_pb,v964_pg]
  minus := ![(Primitive.Addresses.material964 1).one,v964_mb,v964_mg]
  upper := v964_upper
  lower := (Primitive.Addresses.material964 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v964_pa_checked.trans (by decide +kernel)
    · exact v964_pb_checked.trans (by decide +kernel)
    · exact v964_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 50 Primitive.Addresses.material964
    · exact v964_mb_checked.trans (by decide +kernel)
    · exact v964_mg_checked.trans (by decide +kernel)
  upper_error := v964_upper_checked
  lower_error := reuse_lower_error 10 50 Primitive.Addresses.material964

def v965_pa : Scalar.QComplex := ((999999856488314787675955028053 : Int)/10^30,(-535745601782267828505010625 : Int)/10^30)
theorem v965_pa_checked : Scalar.distance (sourceCoefficient 10 51 1 0) v965_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v965_pb : Scalar.QComplex := ((-231162168246844982986799 : Int)/10^30,(-431477429405606540476746323 : Int)/10^30)
theorem v965_pb_checked : Scalar.distance (sourceCoefficient 10 51 1 1) v965_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v965_pg : Scalar.QComplex := ((-93086413337179525348579 : Int)/10^30,(49870643688100285180 : Int)/10^30)
theorem v965_pg_checked : Scalar.distance (sourceCoefficient 10 51 1 2) v965_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v965_mb : Scalar.QComplex := ((-603507670729610814586192 : Int)/10^30,(-431477069264300040633173228 : Int)/10^30)
theorem v965_mb_checked : Scalar.distance (sourceCoefficient 10 51 3 1) v965_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v965_mg : Scalar.QComplex := ((-93086335640734168244832 : Int)/10^30,(130200007372540960923 : Int)/10^30)
theorem v965_mg_checked : Scalar.distance (sourceCoefficient 10 51 3 2) v965_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v965_upper : Scalar.QComplex := ((999997442457690568305456518580 : Int)/10^30,(-2261653836872637888735626889 : Int)/10^30)
theorem v965_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 51 5) 1) 14) v965_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material965 : Material (10 : Basis) (51 : Basis) where
  plus := ![v965_pa,v965_pb,v965_pg]
  minus := ![(Primitive.Addresses.material965 1).one,v965_mb,v965_mg]
  upper := v965_upper
  lower := (Primitive.Addresses.material965 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v965_pa_checked.trans (by decide +kernel)
    · exact v965_pb_checked.trans (by decide +kernel)
    · exact v965_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 51 Primitive.Addresses.material965
    · exact v965_mb_checked.trans (by decide +kernel)
    · exact v965_mg_checked.trans (by decide +kernel)
  upper_error := v965_upper_checked
  lower_error := reuse_lower_error 10 51 Primitive.Addresses.material965

def v966_pa : Scalar.QComplex := ((999999843236648621684201806522 : Int)/10^30,(-559934530263925820895519937 : Int)/10^30)
theorem v966_pa_checked : Scalar.distance (sourceCoefficient 10 52 1 0) v966_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v966_pb : Scalar.QComplex := ((-241599145151136135103461 : Int)/10^30,(-431477421410975348191888258 : Int)/10^30)
theorem v966_pb_checked : Scalar.distance (sourceCoefficient 10 52 1 1) v966_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v966_pg : Scalar.QComplex := ((-93086411858028425159664 : Int)/10^30,(52122304468546610683 : Int)/10^30)
theorem v966_pg_checked : Scalar.distance (sourceCoefficient 10 52 1 2) v966_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v966_mb : Scalar.QComplex := ((-613944636848731817707612 : Int)/10^30,(-431477052263030820701790202 : Int)/10^30)
theorem v966_mb_checked : Scalar.distance (sourceCoefficient 10 52 3 1) v966_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v966_mg : Scalar.QComplex := ((-93086332218501776323290 : Int)/10^30,(132451666038150290914 : Int)/10^30)
theorem v966_mg_checked : Scalar.distance (sourceCoefficient 10 52 3 2) v966_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v966_upper : Scalar.QComplex := ((999997387458147982222237402513 : Int)/10^30,(-2285842706456554718097547276 : Int)/10^30)
theorem v966_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 52 5) 1) 14) v966_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material966 : Material (10 : Basis) (52 : Basis) where
  plus := ![v966_pa,v966_pb,v966_pg]
  minus := ![(Primitive.Addresses.material966 1).one,v966_mb,v966_mg]
  upper := v966_upper
  lower := (Primitive.Addresses.material966 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v966_pa_checked.trans (by decide +kernel)
    · exact v966_pb_checked.trans (by decide +kernel)
    · exact v966_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 52 Primitive.Addresses.material966
    · exact v966_mb_checked.trans (by decide +kernel)
    · exact v966_mg_checked.trans (by decide +kernel)
  upper_error := v966_upper_checked
  lower_error := reuse_lower_error 10 52 Primitive.Addresses.material966

def v967_pa : Scalar.QComplex := ((999999841156529749178483842259 : Int)/10^30,(-563637219557398454626511418 : Int)/10^30)
theorem v967_pa_checked : Scalar.distance (sourceCoefficient 10 53 1 0) v967_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v967_pb : Scalar.QComplex := ((-243196772029592170356829 : Int)/10^30,(-431477420157500458067617821 : Int)/10^30)
theorem v967_pb_checked : Scalar.distance (sourceCoefficient 10 53 1 1) v967_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v967_pg : Scalar.QComplex := ((-93086411626001439293817 : Int)/10^30,(52466974561491254229 : Int)/10^30)
theorem v967_pg_checked : Scalar.distance (sourceCoefficient 10 53 1 2) v967_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v967_mb : Scalar.QComplex := ((-615542262050625975192551 : Int)/10^30,(-431477049630876355639480728 : Int)/10^30)
theorem v967_mb_checked : Scalar.distance (sourceCoefficient 10 53 3 1) v967_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v967_mg : Scalar.QComplex := ((-93086331689040110005199 : Int)/10^30,(132796335802529667961 : Int)/10^30)
theorem v967_mg_checked : Scalar.distance (sourceCoefficient 10 53 3 2) v967_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v967_upper : Scalar.QComplex := ((999997378987526392624221539489 : Int)/10^30,(-2289545386645210130604070467 : Int)/10^30)
theorem v967_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 53 5) 1) 14) v967_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material967 : Material (10 : Basis) (53 : Basis) where
  plus := ![v967_pa,v967_pb,v967_pg]
  minus := ![(Primitive.Addresses.material967 1).one,v967_mb,v967_mg]
  upper := v967_upper
  lower := (Primitive.Addresses.material967 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v967_pa_checked.trans (by decide +kernel)
    · exact v967_pb_checked.trans (by decide +kernel)
    · exact v967_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 53 Primitive.Addresses.material967
    · exact v967_mb_checked.trans (by decide +kernel)
    · exact v967_mg_checked.trans (by decide +kernel)
  upper_error := v967_upper_checked
  lower_error := reuse_lower_error 10 53 Primitive.Addresses.material967

def v968_pa : Scalar.QComplex := ((999999840093727745156314491985 : Int)/10^30,(-565519689259066792198568074 : Int)/10^30)
theorem v968_pa_checked : Scalar.distance (sourceCoefficient 10 54 1 0) v968_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v968_pb : Scalar.QComplex := ((-244009015226244029345493 : Int)/10^30,(-431477419517201879351330004 : Int)/10^30)
theorem v968_pb_checked : Scalar.distance (sourceCoefficient 10 54 1 1) v968_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v968_pg : Scalar.QComplex := ((-93086411507466602985178 : Int)/10^30,(52642206927763205611 : Int)/10^30)
theorem v968_pg_checked : Scalar.distance (sourceCoefficient 10 54 1 2) v968_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v968_mb : Scalar.QComplex := ((-616354504392293735265122 : Int)/10^30,(-431477048289648718700649272 : Int)/10^30)
theorem v968_mb_checked : Scalar.distance (sourceCoefficient 10 54 3 1) v968_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v968_mg : Scalar.QComplex := ((-93086331419287677912608 : Int)/10^30,(132971568001264375742 : Int)/10^30)
theorem v968_mg_checked : Scalar.distance (sourceCoefficient 10 54 3 2) v968_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v968_upper : Scalar.QComplex := ((999997374675754042758545007858 : Int)/10^30,(-2291427851708861135668236484 : Int)/10^30)
theorem v968_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 54 5) 1) 14) v968_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material968 : Material (10 : Basis) (54 : Basis) where
  plus := ![v968_pa,v968_pb,v968_pg]
  minus := ![(Primitive.Addresses.material968 1).one,v968_mb,v968_mg]
  upper := v968_upper
  lower := (Primitive.Addresses.material968 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v968_pa_checked.trans (by decide +kernel)
    · exact v968_pb_checked.trans (by decide +kernel)
    · exact v968_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 54 Primitive.Addresses.material968
    · exact v968_mb_checked.trans (by decide +kernel)
    · exact v968_mg_checked.trans (by decide +kernel)
  upper_error := v968_upper_checked
  lower_error := reuse_lower_error 10 54 Primitive.Addresses.material968

def v969_pa : Scalar.QComplex := ((999999831298909135625215314790 : Int)/10^30,(-580863282768580157860337089 : Int)/10^30)
theorem v969_pa_checked : Scalar.distance (sourceCoefficient 10 55 1 0) v969_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v969_pb : Scalar.QComplex := ((-250629429547087450806609 : Int)/10^30,(-431477414222240861767693223 : Int)/10^30)
theorem v969_pb_checked : Scalar.distance (sourceCoefficient 10 55 1 1) v969_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v969_pg : Scalar.QComplex := ((-93086410526963279022701 : Int)/10^30,(54070487121585768824 : Int)/10^30)
theorem v969_pg_checked : Scalar.distance (sourceCoefficient 10 55 1 2) v969_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v969_mb : Scalar.QComplex := ((-622974911678741455211514 : Int)/10^30,(-431477037281570286177449586 : Int)/10^30)
theorem v969_mb_checked : Scalar.distance (sourceCoefficient 10 55 3 1) v969_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v969_mg : Scalar.QComplex := ((-93086329206243239119443 : Int)/10^30,(134399846817142738815 : Int)/10^30)
theorem v969_mg_checked : Scalar.distance (sourceCoefficient 10 55 3 2) v969_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v969_upper : Scalar.QComplex := ((999997339399298094586372424396 : Int)/10^30,(-2306771407186835293675164273 : Int)/10^30)
theorem v969_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 55 5) 1) 14) v969_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material969 : Material (10 : Basis) (55 : Basis) where
  plus := ![v969_pa,v969_pb,v969_pg]
  minus := ![(Primitive.Addresses.material969 1).one,v969_mb,v969_mg]
  upper := v969_upper
  lower := (Primitive.Addresses.material969 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v969_pa_checked.trans (by decide +kernel)
    · exact v969_pb_checked.trans (by decide +kernel)
    · exact v969_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 55 Primitive.Addresses.material969
    · exact v969_mb_checked.trans (by decide +kernel)
    · exact v969_mg_checked.trans (by decide +kernel)
  upper_error := v969_upper_checked
  lower_error := reuse_lower_error 10 55 Primitive.Addresses.material969

def v970_pa : Scalar.QComplex := ((999999829177086317673445152658 : Int)/10^30,(-584504746074987205295911118 : Int)/10^30)
theorem v970_pa_checked : Scalar.distance (sourceCoefficient 10 56 1 0) v970_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v970_pb : Scalar.QComplex := ((-252200638772573957974381 : Int)/10^30,(-431477412945712377422254282 : Int)/10^30)
theorem v970_pb_checked : Scalar.distance (sourceCoefficient 10 56 1 1) v970_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v970_pg : Scalar.QComplex := ((-93086410290508480382962 : Int)/10^30,(54409457904267866379 : Int)/10^30)
theorem v970_pg_checked : Scalar.distance (sourceCoefficient 10 56 1 2) v970_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v970_mb : Scalar.QComplex := ((-624546119217608370640268 : Int)/10^30,(-431477034649159480183659038 : Int)/10^30)
theorem v970_mb_checked : Scalar.distance (sourceCoefficient 10 56 3 1) v970_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v970_mg : Scalar.QComplex := ((-93086328677272009745309 : Int)/10^30,(134738817269560680550 : Int)/10^30)
theorem v970_mg_checked : Scalar.distance (sourceCoefficient 10 56 3 2) v970_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v970_upper : Scalar.QComplex := ((999997330992643120952475992823 : Int)/10^30,(-2310412861407636809023292772 : Int)/10^30)
theorem v970_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 56 5) 1) 14) v970_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material970 : Material (10 : Basis) (56 : Basis) where
  plus := ![v970_pa,v970_pb,v970_pg]
  minus := ![(Primitive.Addresses.material970 1).one,v970_mb,v970_mg]
  upper := v970_upper
  lower := (Primitive.Addresses.material970 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v970_pa_checked.trans (by decide +kernel)
    · exact v970_pb_checked.trans (by decide +kernel)
    · exact v970_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 56 Primitive.Addresses.material970
    · exact v970_mb_checked.trans (by decide +kernel)
    · exact v970_mg_checked.trans (by decide +kernel)
  upper_error := v970_upper_checked
  lower_error := reuse_lower_error 10 56 Primitive.Addresses.material970

def v971_pa : Scalar.QComplex := ((999999822223514441933325943926 : Int)/10^30,(-596282600376410891910123672 : Int)/10^30)
theorem v971_pa_checked : Scalar.distance (sourceCoefficient 10 57 1 0) v971_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v971_pb : Scalar.QComplex := ((-257282517040674003912453 : Int)/10^30,(-431477408764702395501456987 : Int)/10^30)
theorem v971_pb_checked : Scalar.distance (sourceCoefficient 10 57 1 1) v971_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v971_pg : Scalar.QComplex := ((-93086409515863912472893 : Int)/10^30,(55505816193451744310 : Int)/10^30)
theorem v971_pg_checked : Scalar.distance (sourceCoefficient 10 57 1 2) v971_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v971_mb : Scalar.QComplex := ((-629627991985469575355996 : Int)/10^30,(-431477026082718988974416167 : Int)/10^30)
theorem v971_mb_checked : Scalar.distance (sourceCoefficient 10 57 3 1) v971_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v971_mg : Scalar.QComplex := ((-93086326956519904849470 : Int)/10^30,(135835174482036887959 : Int)/10^30)
theorem v971_mg_checked : Scalar.distance (sourceCoefficient 10 57 3 2) v971_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v971_upper : Scalar.QComplex := ((999997303711573556079287080925 : Int)/10^30,(-2322190686166095803205827994 : Int)/10^30)
theorem v971_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 57 5) 1) 14) v971_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material971 : Material (10 : Basis) (57 : Basis) where
  plus := ![v971_pa,v971_pb,v971_pg]
  minus := ![(Primitive.Addresses.material971 1).one,v971_mb,v971_mg]
  upper := v971_upper
  lower := (Primitive.Addresses.material971 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v971_pa_checked.trans (by decide +kernel)
    · exact v971_pb_checked.trans (by decide +kernel)
    · exact v971_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 57 Primitive.Addresses.material971
    · exact v971_mb_checked.trans (by decide +kernel)
    · exact v971_mg_checked.trans (by decide +kernel)
  upper_error := v971_upper_checked
  lower_error := reuse_lower_error 10 57 Primitive.Addresses.material971

def v972_pa : Scalar.QComplex := ((999999818392520934222517695342 : Int)/10^30,(-602673149518276209708737944 : Int)/10^30)
theorem v972_pa_checked : Scalar.distance (sourceCoefficient 10 58 1 0) v972_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v972_pb : Scalar.QComplex := ((-260039894724060017236599 : Int)/10^30,(-431477406462728946089862900 : Int)/10^30)
theorem v972_pb_checked : Scalar.distance (sourceCoefficient 10 58 1 1) v972_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v972_pg : Scalar.QComplex := ((-93086409089244696767852 : Int)/10^30,(56100689531466594372 : Int)/10^30)
theorem v972_pg_checked : Scalar.distance (sourceCoefficient 10 58 1 2) v972_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v972_mb : Scalar.QComplex := ((-632385366655658448963247 : Int)/10^30,(-431477021401253643611409477 : Int)/10^30)
theorem v972_mb_checked : Scalar.distance (sourceCoefficient 10 58 3 1) v972_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v972_mg : Scalar.QComplex := ((-93086326016551949388020 : Int)/10^30,(136430047230400038287 : Int)/10^30)
theorem v972_mg_checked : Scalar.distance (sourceCoefficient 10 58 3 2) v972_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v972_upper : Scalar.QComplex := ((999997288851077681413172037946 : Int)/10^30,(-2328581219178041611538406699 : Int)/10^30)
theorem v972_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 58 5) 1) 14) v972_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material972 : Material (10 : Basis) (58 : Basis) where
  plus := ![v972_pa,v972_pb,v972_pg]
  minus := ![(Primitive.Addresses.material972 1).one,v972_mb,v972_mg]
  upper := v972_upper
  lower := (Primitive.Addresses.material972 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v972_pa_checked.trans (by decide +kernel)
    · exact v972_pb_checked.trans (by decide +kernel)
    · exact v972_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 58 Primitive.Addresses.material972
    · exact v972_mb_checked.trans (by decide +kernel)
    · exact v972_mg_checked.trans (by decide +kernel)
  upper_error := v972_upper_checked
  lower_error := reuse_lower_error 10 58 Primitive.Addresses.material972

def v973_pa : Scalar.QComplex := ((999999807651727503790509504861 : Int)/10^30,(-620239073256886202046986539 : Int)/10^30)
theorem v973_pa_checked : Scalar.distance (sourceCoefficient 10 59 1 0) v973_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v973_pb : Scalar.QComplex := ((-267619194192166720019589 : Int)/10^30,(-431477400014165892076832320 : Int)/10^30)
theorem v973_pb_checked : Scalar.distance (sourceCoefficient 10 59 1 1) v973_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v973_pg : Scalar.QComplex := ((-93086407893731105359571 : Int)/10^30,(57735838470209067950 : Int)/10^30)
theorem v973_pg_checked : Scalar.distance (sourceCoefficient 10 59 1 2) v973_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v973_mb : Scalar.QComplex := ((-639964657736826085557698 : Int)/10^30,(-431477008412098908693235979 : Int)/10^30)
theorem v973_mb_checked : Scalar.distance (sourceCoefficient 10 59 3 1) v973_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v973_mg : Scalar.QComplex := ((-93086323409978913363726 : Int)/10^30,(138065194528627446521 : Int)/10^30)
theorem v973_mg_checked : Scalar.distance (sourceCoefficient 10 59 3 2) v973_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v973_upper : Scalar.QComplex := ((999997247793109443443724900100 : Int)/10^30,(-2346147098216636569810836964 : Int)/10^30)
theorem v973_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 59 5) 1) 14) v973_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material973 : Material (10 : Basis) (59 : Basis) where
  plus := ![v973_pa,v973_pb,v973_pg]
  minus := ![(Primitive.Addresses.material973 1).one,v973_mb,v973_mg]
  upper := v973_upper
  lower := (Primitive.Addresses.material973 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v973_pa_checked.trans (by decide +kernel)
    · exact v973_pb_checked.trans (by decide +kernel)
    · exact v973_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 59 Primitive.Addresses.material973
    · exact v973_mb_checked.trans (by decide +kernel)
    · exact v973_mg_checked.trans (by decide +kernel)
  upper_error := v973_upper_checked
  lower_error := reuse_lower_error 10 59 Primitive.Addresses.material973

def v974_pa : Scalar.QComplex := ((999999794877932822742864865358 : Int)/10^30,(-640502999430488090511482112 : Int)/10^30)
theorem v974_pa_checked : Scalar.distance (sourceCoefficient 10 60 1 0) v974_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v974_pb : Scalar.QComplex := ((-276362620677664782423776 : Int)/10^30,(-431477392354640418730289591 : Int)/10^30)
theorem v974_pb_checked : Scalar.distance (sourceCoefficient 10 60 1 1) v974_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v974_pg : Scalar.QComplex := ((-93086406472969327497344 : Int)/10^30,(59622134781957992068 : Int)/10^30)
theorem v974_pg_checked : Scalar.distance (sourceCoefficient 10 60 1 2) v974_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v974_mb : Scalar.QComplex := ((-648708074356921361803492 : Int)/10^30,(-431476993207393019664017215 : Int)/10^30)
theorem v974_mb_checked : Scalar.distance (sourceCoefficient 10 60 3 1) v974_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v974_mg : Scalar.QComplex := ((-93086320361428903108899 : Int)/10^30,(139951488911968620214 : Int)/10^30)
theorem v974_mg_checked : Scalar.distance (sourceCoefficient 10 60 3 2) v974_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v974_upper : Scalar.QComplex := ((999997200045635540848113771082 : Int)/10^30,(-2366410972163090000788351497 : Int)/10^30)
theorem v974_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 60 5) 1) 14) v974_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material974 : Material (10 : Basis) (60 : Basis) where
  plus := ![v974_pa,v974_pb,v974_pg]
  minus := ![(Primitive.Addresses.material974 1).one,v974_mb,v974_mg]
  upper := v974_upper
  lower := (Primitive.Addresses.material974 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v974_pa_checked.trans (by decide +kernel)
    · exact v974_pb_checked.trans (by decide +kernel)
    · exact v974_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 60 Primitive.Addresses.material974
    · exact v974_mb_checked.trans (by decide +kernel)
    · exact v974_mg_checked.trans (by decide +kernel)
  upper_error := v974_upper_checked
  lower_error := reuse_lower_error 10 60 Primitive.Addresses.material974

def v975_pa : Scalar.QComplex := ((999999791107844901883544657660 : Int)/10^30,(-646362333803804233672011754 : Int)/10^30)
theorem v975_pa_checked : Scalar.distance (sourceCoefficient 10 61 1 0) v975_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v975_pb : Scalar.QComplex := ((-278890791104027496513978 : Int)/10^30,(-431477390095851629525995038 : Int)/10^30)
theorem v975_pb_checked : Scalar.distance (sourceCoefficient 10 61 1 1) v975_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v975_pg : Scalar.QComplex := ((-93086406053843156230254 : Int)/10^30,(60167559230901748097 : Int)/10^30)
theorem v975_pg_checked : Scalar.distance (sourceCoefficient 10 61 1 2) v975_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v975_mb : Scalar.QComplex := ((-651236241892697690049713 : Int)/10^30,(-431476988766907858128150255 : Int)/10^30)
theorem v975_mb_checked : Scalar.distance (sourceCoefficient 10 61 3 1) v975_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v975_mg : Scalar.QComplex := ((-93086319471626153468460 : Int)/10^30,(140496912796138917711 : Int)/10^30)
theorem v975_mg_checked : Scalar.distance (sourceCoefficient 10 61 3 2) v975_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v975_upper : Scalar.QComplex := ((999997186162873661410293042175 : Int)/10^30,(-2372270291302786148960695918 : Int)/10^30)
theorem v975_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 61 5) 1) 14) v975_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material975 : Material (10 : Basis) (61 : Basis) where
  plus := ![v975_pa,v975_pb,v975_pg]
  minus := ![(Primitive.Addresses.material975 1).one,v975_mb,v975_mg]
  upper := v975_upper
  lower := (Primitive.Addresses.material975 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v975_pa_checked.trans (by decide +kernel)
    · exact v975_pb_checked.trans (by decide +kernel)
    · exact v975_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 61 Primitive.Addresses.material975
    · exact v975_mb_checked.trans (by decide +kernel)
    · exact v975_mg_checked.trans (by decide +kernel)
  upper_error := v975_upper_checked
  lower_error := reuse_lower_error 10 61 Primitive.Addresses.material975

def v976_pa : Scalar.QComplex := ((999999785568888898457358852699 : Int)/10^30,(-654875695244818101695271127 : Int)/10^30)
theorem v976_pa_checked : Scalar.distance (sourceCoefficient 10 62 1 0) v976_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v976_pb : Scalar.QComplex := ((-282564114239675971454714 : Int)/10^30,(-431477386778731378727016499 : Int)/10^30)
theorem v976_pb_checked : Scalar.distance (sourceCoefficient 10 62 1 1) v976_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v976_pg : Scalar.QComplex := ((-93086405438226613069051 : Int)/10^30,(60960037550928254711 : Int)/10^30)
theorem v976_pg_checked : Scalar.distance (sourceCoefficient 10 62 1 2) v976_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v976_mb : Scalar.QComplex := ((-654909560798074703538503 : Int)/10^30,(-431476982279876416712602880 : Int)/10^30)
theorem v976_mb_checked : Scalar.distance (sourceCoefficient 10 62 3 1) v976_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v976_mg : Scalar.QComplex := ((-93086318172136741245145 : Int)/10^30,(141289390289840177323 : Int)/10^30)
theorem v976_mg_checked : Scalar.distance (sourceCoefficient 10 62 3 2) v976_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v976_upper : Scalar.QComplex := ((999997165930636386535334893478 : Int)/10^30,(-2380783630504412628528115554 : Int)/10^30)
theorem v976_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 10 62 5) 1) 14) v976_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material976 : Material (10 : Basis) (62 : Basis) where
  plus := ![v976_pa,v976_pb,v976_pg]
  minus := ![(Primitive.Addresses.material976 1).one,v976_mb,v976_mg]
  upper := v976_upper
  lower := (Primitive.Addresses.material976 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v976_pa_checked.trans (by decide +kernel)
    · exact v976_pb_checked.trans (by decide +kernel)
    · exact v976_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 10 62 Primitive.Addresses.material976
    · exact v976_mb_checked.trans (by decide +kernel)
    · exact v976_mg_checked.trans (by decide +kernel)
  upper_error := v976_upper_checked
  lower_error := reuse_lower_error 10 62 Primitive.Addresses.material976

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
