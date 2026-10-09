import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B013
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B014

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v321_pa : Scalar.QComplex := ((999993216078270226293976452774 : Int)/10^30,(3683449122487424333559889249 : Int)/10^30)
theorem v321_pa_checked : Scalar.distance (sourceCoefficient 3 37 1 0) v321_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v321_pb : Scalar.QComplex := ((1589320193150686874972374 : Int)/10^30,(-431473154230412219939538196 : Int)/10^30)
theorem v321_pb_checked : Scalar.distance (sourceCoefficient 3 37 1 1) v321_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v321_pg : Scalar.QComplex := ((-93085643110576960934598 : Int)/10^30,(-342878556493122330359 : Int)/10^30)
theorem v321_pg_checked : Scalar.distance (sourceCoefficient 3 37 1 2) v321_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v321_mb : Scalar.QComplex := ((1216977702102783696527496 : Int)/10^30,(-431474365084983967385494407 : Int)/10^30)
theorem v321_mb_checked : Scalar.distance (sourceCoefficient 3 37 3 1) v321_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v321_mg : Scalar.QComplex := ((-93085904339289383452944 : Int)/10^30,(-262549711241073196627 : Int)/10^30)
theorem v321_mg_checked : Scalar.distance (sourceCoefficient 3 37 3 2) v321_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v321_upper : Scalar.QComplex := ((999998084004867851725854326501 : Int)/10^30,(1957546064147457520939018926 : Int)/10^30)
theorem v321_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 37 5) 1) 14) v321_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material321 : Material (3 : Basis) (37 : Basis) where
  plus := ![v321_pa,v321_pb,v321_pg]
  minus := ![(Primitive.Addresses.material321 1).one,v321_mb,v321_mg]
  upper := v321_upper
  lower := (Primitive.Addresses.material321 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v321_pa_checked.trans (by decide +kernel)
    · exact v321_pb_checked.trans (by decide +kernel)
    · exact v321_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 37 Primitive.Addresses.material321
    · exact v321_mb_checked.trans (by decide +kernel)
    · exact v321_mg_checked.trans (by decide +kernel)
  upper_error := v321_upper_checked
  lower_error := reuse_lower_error 3 37 Primitive.Addresses.material321

def v322_pa : Scalar.QComplex := ((999993301634910362199058814198 : Int)/10^30,(3660148263551727736751816326 : Int)/10^30)
theorem v322_pa_checked : Scalar.distance (sourceCoefficient 3 38 1 0) v322_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v322_pb : Scalar.QComplex := ((1579266374819571203270563 : Int)/10^30,(-431473176112364264103846950 : Int)/10^30)
theorem v322_pb_checked : Scalar.distance (sourceCoefficient 3 38 1 1) v322_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v322_pg : Scalar.QComplex := ((-93085649453049695839367 : Int)/10^30,(-340709560404189796242 : Int)/10^30)
theorem v322_pg_checked : Scalar.distance (sourceCoefficient 3 38 1 2) v322_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v322_mb : Scalar.QComplex := ((1206923868632024984118469 : Int)/10^30,(-431474378290935451314819064 : Int)/10^30)
theorem v322_mb_checked : Scalar.distance (sourceCoefficient 3 38 3 1) v322_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v322_mg : Scalar.QComplex := ((-93085908810013819973970 : Int)/10^30,(-260380710486488718583 : Int)/10^30)
theorem v322_mg_checked : Scalar.distance (sourceCoefficient 3 38 3 2) v322_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v322_upper : Scalar.QComplex := ((999998129346211875463571824044 : Int)/10^30,(1934245092252653960879237923 : Int)/10^30)
theorem v322_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 38 5) 1) 14) v322_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material322 : Material (3 : Basis) (38 : Basis) where
  plus := ![v322_pa,v322_pb,v322_pg]
  minus := ![(Primitive.Addresses.material322 1).one,v322_mb,v322_mg]
  upper := v322_upper
  lower := (Primitive.Addresses.material322 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v322_pa_checked.trans (by decide +kernel)
    · exact v322_pb_checked.trans (by decide +kernel)
    · exact v322_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 38 Primitive.Addresses.material322
    · exact v322_mb_checked.trans (by decide +kernel)
    · exact v322_mg_checked.trans (by decide +kernel)
  upper_error := v322_upper_checked
  lower_error := reuse_lower_error 3 38 Primitive.Addresses.material322

def v323_pa : Scalar.QComplex := ((999993351019216057387375124824 : Int)/10^30,(3646630960069823134999370723 : Int)/10^30)
theorem v323_pa_checked : Scalar.distance (sourceCoefficient 3 39 1 0) v323_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v323_pb : Scalar.QComplex := ((1573433949951988585915372 : Int)/10^30,(-431473188663369364230959765 : Int)/10^30)
theorem v323_pb_checked : Scalar.distance (sourceCoefficient 3 39 1 1) v323_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v323_pg : Scalar.QComplex := ((-93085653105422625492896 : Int)/10^30,(-339451281557601983319 : Int)/10^30)
theorem v323_pg_checked : Scalar.distance (sourceCoefficient 3 39 1 2) v323_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v323_mb : Scalar.QComplex := ((1201091435105168574824787 : Int)/10^30,(-431474385808815900070122097 : Int)/10^30)
theorem v323_mb_checked : Scalar.distance (sourceCoefficient 3 39 3 1) v323_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v323_mg : Scalar.QComplex := ((-93085911376547415852385 : Int)/10^30,(-259122428956582284908 : Int)/10^30)
theorem v323_mg_checked : Scalar.distance (sourceCoefficient 3 39 3 2) v323_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v323_upper : Scalar.QComplex := ((999998155400804488955003787915 : Int)/10^30,(1920727723670353520736992571 : Int)/10^30)
theorem v323_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 39 5) 1) 14) v323_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material323 : Material (3 : Basis) (39 : Basis) where
  plus := ![v323_pa,v323_pb,v323_pg]
  minus := ![(Primitive.Addresses.material323 1).one,v323_mb,v323_mg]
  upper := v323_upper
  lower := (Primitive.Addresses.material323 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v323_pa_checked.trans (by decide +kernel)
    · exact v323_pb_checked.trans (by decide +kernel)
    · exact v323_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 39 Primitive.Addresses.material323
    · exact v323_mb_checked.trans (by decide +kernel)
    · exact v323_mg_checked.trans (by decide +kernel)
  upper_error := v323_upper_checked
  lower_error := reuse_lower_error 3 39 Primitive.Addresses.material323

def v324_pa : Scalar.QComplex := ((999993433668739582606584767166 : Int)/10^30,(3623895611648956603508806549 : Int)/10^30)
theorem v324_pa_checked : Scalar.distance (sourceCoefficient 3 40 1 0) v324_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v324_pb : Scalar.QComplex := ((1563624137856985964628196 : Int)/10^30,(-431473209536366698212727255 : Int)/10^30)
theorem v324_pb_checked : Scalar.distance (sourceCoefficient 3 40 1 1) v324_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v324_pg : Scalar.QComplex := ((-93085659203753482762536 : Int)/10^30,(-337334926948808608721 : Int)/10^30)
theorem v324_pg_checked : Scalar.distance (sourceCoefficient 3 40 1 2) v324_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v324_mb : Scalar.QComplex := ((1191281608650350712743873 : Int)/10^30,(-431474398216379441629497926 : Int)/10^30)
theorem v324_mb_checked : Scalar.distance (sourceCoefficient 3 40 3 1) v324_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v324_mg : Scalar.QComplex := ((-93085915648557292119301 : Int)/10^30,(-257006069873219582150 : Int)/10^30)
theorem v324_mg_checked : Scalar.distance (sourceCoefficient 3 40 3 2) v324_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v324_upper : Scalar.QComplex := ((999998198811056077699088434102 : Int)/10^30,(1897992266465538082171882810 : Int)/10^30)
theorem v324_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 40 5) 1) 14) v324_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material324 : Material (3 : Basis) (40 : Basis) where
  plus := ![v324_pa,v324_pb,v324_pg]
  minus := ![(Primitive.Addresses.material324 1).one,v324_mb,v324_mg]
  upper := v324_upper
  lower := (Primitive.Addresses.material324 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v324_pa_checked.trans (by decide +kernel)
    · exact v324_pb_checked.trans (by decide +kernel)
    · exact v324_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 40 Primitive.Addresses.material324
    · exact v324_mb_checked.trans (by decide +kernel)
    · exact v324_mg_checked.trans (by decide +kernel)
  upper_error := v324_upper_checked
  lower_error := reuse_lower_error 3 40 Primitive.Addresses.material324

def v325_pa : Scalar.QComplex := ((999993486052330815469408087936 : Int)/10^30,(3609411712018292920811162264 : Int)/10^30)
theorem v325_pa_checked : Scalar.distance (sourceCoefficient 3 41 1 0) v325_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v325_pb : Scalar.QComplex := ((1557374648015942575758746 : Int)/10^30,(-431473222678757457230821168 : Int)/10^30)
theorem v325_pb_checked : Scalar.distance (sourceCoefficient 3 41 1 1) v325_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v325_pg : Scalar.QComplex := ((-93085663059515149505295 : Int)/10^30,(-335986671067595420162 : Int)/10^30)
theorem v325_pg_checked : Scalar.distance (sourceCoefficient 3 41 1 2) v325_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v325_mb : Scalar.QComplex := ((1185032109794986693764710 : Int)/10^30,(-431474405965737040888340965 : Int)/10^30)
theorem v325_mb_checked : Scalar.distance (sourceCoefficient 3 41 3 1) v325_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v325_mg : Scalar.QComplex := ((-93085918340833420889532 : Int)/10^30,(-255657811166675015164 : Int)/10^30)
theorem v325_mg_checked : Scalar.distance (sourceCoefficient 3 41 3 2) v325_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v325_upper : Scalar.QComplex := ((999998226196672497940993349340 : Int)/10^30,(1883508297997615235333704761 : Int)/10^30)
theorem v325_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 41 5) 1) 14) v325_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material325 : Material (3 : Basis) (41 : Basis) where
  plus := ![v325_pa,v325_pb,v325_pg]
  minus := ![(Primitive.Addresses.material325 1).one,v325_mb,v325_mg]
  upper := v325_upper
  lower := (Primitive.Addresses.material325 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v325_pa_checked.trans (by decide +kernel)
    · exact v325_pb_checked.trans (by decide +kernel)
    · exact v325_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 41 Primitive.Addresses.material325
    · exact v325_mb_checked.trans (by decide +kernel)
    · exact v325_mg_checked.trans (by decide +kernel)
  upper_error := v325_upper_checked
  lower_error := reuse_lower_error 3 41 Primitive.Addresses.material325

def v326_pa : Scalar.QComplex := ((999993528155180370975153377458 : Int)/10^30,(3597728137934088028387261835 : Int)/10^30)
theorem v326_pa_checked : Scalar.distance (sourceCoefficient 3 42 1 0) v326_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v326_pb : Scalar.QComplex := ((1552333438282259563338855 : Int)/10^30,(-431473233192245703497500160 : Int)/10^30)
theorem v326_pb_checked : Scalar.distance (sourceCoefficient 3 42 1 1) v326_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v326_pg : Scalar.QComplex := ((-93085666153200077440579 : Int)/10^30,(-334899087772632977368 : Int)/10^30)
theorem v326_pg_checked : Scalar.distance (sourceCoefficient 3 42 1 2) v326_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v326_mb : Scalar.QComplex := ((1179990892865709613266514 : Int)/10^30,(-431474412128884419992415842 : Int)/10^30)
theorem v326_mb_checked : Scalar.distance (sourceCoefficient 3 42 3 1) v326_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v326_mg : Scalar.QComplex := ((-93085920495981796285214 : Int)/10^30,(-254570225606958779685 : Int)/10^30)
theorem v326_mg_checked : Scalar.distance (sourceCoefficient 3 42 3 2) v326_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v326_upper : Scalar.QComplex := ((999998248134670402421664477267 : Int)/10^30,(1871824668649022700183920199 : Int)/10^30)
theorem v326_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 42 5) 1) 14) v326_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material326 : Material (3 : Basis) (42 : Basis) where
  plus := ![v326_pa,v326_pb,v326_pg]
  minus := ![(Primitive.Addresses.material326 1).one,v326_mb,v326_mg]
  upper := v326_upper
  lower := (Primitive.Addresses.material326 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v326_pa_checked.trans (by decide +kernel)
    · exact v326_pb_checked.trans (by decide +kernel)
    · exact v326_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 42 Primitive.Addresses.material326
    · exact v326_mb_checked.trans (by decide +kernel)
    · exact v326_mg_checked.trans (by decide +kernel)
  upper_error := v326_upper_checked
  lower_error := reuse_lower_error 3 42 Primitive.Addresses.material326

def v327_pa : Scalar.QComplex := ((999993583720275363108964002636 : Int)/10^30,(3582250449176924492375877351 : Int)/10^30)
theorem v327_pa_checked : Scalar.distance (sourceCoefficient 3 43 1 0) v327_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v327_pb : Scalar.QComplex := ((1545655150225605653711844 : Int)/10^30,(-431473246998947000584573688 : Int)/10^30)
theorem v327_pb_checked : Scalar.distance (sourceCoefficient 3 43 1 1) v327_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v327_pg : Scalar.QComplex := ((-93085670228697866181879 : Int)/10^30,(-333458323550568407688 : Int)/10^30)
theorem v327_pg_checked : Scalar.distance (sourceCoefficient 3 43 1 2) v327_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v327_mb : Scalar.QComplex := ((1173312595381126171330597 : Int)/10^30,(-431474420172518762249908060 : Int)/10^30)
theorem v327_mb_checked : Scalar.distance (sourceCoefficient 3 43 3 1) v327_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v327_mg : Scalar.QComplex := ((-93085923328163433502450 : Int)/10^30,(-253129458404385537981 : Int)/10^30)
theorem v327_mg_checked : Scalar.distance (sourceCoefficient 3 43 3 2) v327_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v327_upper : Scalar.QComplex := ((999998276986595966964983379446 : Int)/10^30,(1856346907043745300547002242 : Int)/10^30)
theorem v327_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 43 5) 1) 14) v327_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material327 : Material (3 : Basis) (43 : Basis) where
  plus := ![v327_pa,v327_pb,v327_pg]
  minus := ![(Primitive.Addresses.material327 1).one,v327_mb,v327_mg]
  upper := v327_upper
  lower := (Primitive.Addresses.material327 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v327_pa_checked.trans (by decide +kernel)
    · exact v327_pb_checked.trans (by decide +kernel)
    · exact v327_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 43 Primitive.Addresses.material327
    · exact v327_mb_checked.trans (by decide +kernel)
    · exact v327_mg_checked.trans (by decide +kernel)
  upper_error := v327_upper_checked
  lower_error := reuse_lower_error 3 43 Primitive.Addresses.material327

def v328_pa : Scalar.QComplex := ((999993604679998873805564008390 : Int)/10^30,(3576394707262395005575480297 : Int)/10^30)
theorem v328_pa_checked : Scalar.distance (sourceCoefficient 3 44 1 0) v328_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v328_pb : Scalar.QComplex := ((1543128524246028329814768 : Int)/10^30,(-431473252186561991919687898 : Int)/10^30)
theorem v328_pb_checked : Scalar.distance (sourceCoefficient 3 44 1 1) v328_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v328_pg : Scalar.QComplex := ((-93085671763815336169584 : Int)/10^30,(-332913232904730772972 : Int)/10^30)
theorem v328_pg_checked : Scalar.distance (sourceCoefficient 3 44 1 2) v328_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v328_mb : Scalar.QComplex := ((1170785965865649076125710 : Int)/10^30,(-431474423179767396633495589 : Int)/10^30)
theorem v328_mb_checked : Scalar.distance (sourceCoefficient 3 44 3 1) v328_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v328_mg : Scalar.QComplex := ((-93085924392891654509235 : Int)/10^30,(-252584366636772825108 : Int)/10^30)
theorem v328_mg_checked : Scalar.distance (sourceCoefficient 3 44 3 2) v328_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v328_upper : Scalar.QComplex := ((999998287839808944894376859785 : Int)/10^30,(1850491137676074203474437721 : Int)/10^30)
theorem v328_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 44 5) 1) 14) v328_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material328 : Material (3 : Basis) (44 : Basis) where
  plus := ![v328_pa,v328_pb,v328_pg]
  minus := ![(Primitive.Addresses.material328 1).one,v328_mb,v328_mg]
  upper := v328_upper
  lower := (Primitive.Addresses.material328 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v328_pa_checked.trans (by decide +kernel)
    · exact v328_pb_checked.trans (by decide +kernel)
    · exact v328_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 44 Primitive.Addresses.material328
    · exact v328_mb_checked.trans (by decide +kernel)
    · exact v328_mg_checked.trans (by decide +kernel)
  upper_error := v328_upper_checked
  lower_error := reuse_lower_error 3 44 Primitive.Addresses.material328

def v329_pa : Scalar.QComplex := ((999993615094949711755580056443 : Int)/10^30,(3573481402437123030445679680 : Int)/10^30)
theorem v329_pa_checked : Scalar.distance (sourceCoefficient 3 45 1 0) v329_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v329_pb : Scalar.QComplex := ((1541871496237394727600106 : Int)/10^30,(-431473254760116590999863665 : Int)/10^30)
theorem v329_pb_checked : Scalar.distance (sourceCoefficient 3 45 1 1) v329_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v329_pg : Scalar.QComplex := ((-93085672526168241177039 : Int)/10^30,(-332642043493477899144 : Int)/10^30)
theorem v329_pg_checked : Scalar.distance (sourceCoefficient 3 45 1 2) v329_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v329_mb : Scalar.QComplex := ((1169528936104202740133593 : Int)/10^30,(-431474424668562480450760213 : Int)/10^30)
theorem v329_mb_checked : Scalar.distance (sourceCoefficient 3 45 3 1) v329_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v329_mg : Scalar.QComplex := ((-93085924921220027664313 : Int)/10^30,(-252313176668619941137 : Int)/10^30)
theorem v329_mg_checked : Scalar.distance (sourceCoefficient 3 45 3 2) v329_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v329_upper : Scalar.QComplex := ((999998293226644435528322226874 : Int)/10^30,(1847577819214567235420395694 : Int)/10^30)
theorem v329_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 45 5) 1) 14) v329_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material329 : Material (3 : Basis) (45 : Basis) where
  plus := ![v329_pa,v329_pb,v329_pg]
  minus := ![(Primitive.Addresses.material329 1).one,v329_mb,v329_mg]
  upper := v329_upper
  lower := (Primitive.Addresses.material329 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v329_pa_checked.trans (by decide +kernel)
    · exact v329_pb_checked.trans (by decide +kernel)
    · exact v329_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 45 Primitive.Addresses.material329
    · exact v329_mb_checked.trans (by decide +kernel)
    · exact v329_mg_checked.trans (by decide +kernel)
  upper_error := v329_upper_checked
  lower_error := reuse_lower_error 3 45 Primitive.Addresses.material329

def v330_pa : Scalar.QComplex := ((999993673438375207118158405839 : Int)/10^30,(3557117263206791075950610354 : Int)/10^30)
theorem v330_pa_checked : Scalar.distance (sourceCoefficient 3 46 1 0) v330_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v330_pb : Scalar.QComplex := ((1534810724291873501012283 : Int)/10^30,(-431473269125122753624260125 : Int)/10^30)
theorem v330_pb_checked : Scalar.distance (sourceCoefficient 3 46 1 1) v330_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v330_pg : Scalar.QComplex := ((-93085676791202410169714 : Int)/10^30,(-331118762714531265655 : Int)/10^30)
theorem v330_pg_checked : Scalar.distance (sourceCoefficient 3 46 1 2) v330_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v330_mb : Scalar.QComplex := ((1162468154391376259598439 : Int)/10^30,(-431474432940435110705542856 : Int)/10^30)
theorem v330_mb_checked : Scalar.distance (sourceCoefficient 3 46 3 1) v330_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v330_mg : Scalar.QComplex := ((-93085927871729902378409 : Int)/10^30,(-250789892776327961188 : Int)/10^30)
theorem v330_mg_checked : Scalar.distance (sourceCoefficient 3 46 3 2) v330_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v330_upper : Scalar.QComplex := ((999998323326963266773533275099 : Int)/10^30,(1831213603661238866898362795 : Int)/10^30)
theorem v330_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 46 5) 1) 14) v330_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material330 : Material (3 : Basis) (46 : Basis) where
  plus := ![v330_pa,v330_pb,v330_pg]
  minus := ![(Primitive.Addresses.material330 1).one,v330_mb,v330_mg]
  upper := v330_upper
  lower := (Primitive.Addresses.material330 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v330_pa_checked.trans (by decide +kernel)
    · exact v330_pb_checked.trans (by decide +kernel)
    · exact v330_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 46 Primitive.Addresses.material330
    · exact v330_mb_checked.trans (by decide +kernel)
    · exact v330_mg_checked.trans (by decide +kernel)
  upper_error := v330_upper_checked
  lower_error := reuse_lower_error 3 46 Primitive.Addresses.material330

def v331_pa : Scalar.QComplex := ((999993687438700849894608373038 : Int)/10^30,(3553179245389972618794168556 : Int)/10^30)
theorem v331_pa_checked : Scalar.distance (sourceCoefficient 3 47 1 0) v331_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v331_pb : Scalar.QComplex := ((1533111554857984660284258 : Int)/10^30,(-431473272559052511826488539 : Int)/10^30)
theorem v331_pb_checked : Scalar.distance (sourceCoefficient 3 47 1 1) v331_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v331_pg : Scalar.QComplex := ((-93085677813238272038720 : Int)/10^30,(-330752186342507194992 : Int)/10^30)
theorem v331_pg_checked : Scalar.distance (sourceCoefficient 3 47 1 2) v331_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v331_mb : Scalar.QComplex := ((1160768982626839132113230 : Int)/10^30,(-431474434908056896603173122 : Int)/10^30)
theorem v331_mb_checked : Scalar.distance (sourceCoefficient 3 47 3 1) v331_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v331_mg : Scalar.QComplex := ((-93085928577426484626898 : Int)/10^30,(-250423315658826109191 : Int)/10^30)
theorem v331_mg_checked : Scalar.distance (sourceCoefficient 3 47 3 2) v331_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v331_upper : Scalar.QComplex := ((999998330530606560066500273533 : Int)/10^30,(1827275567546343396013615268 : Int)/10^30)
theorem v331_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 47 5) 1) 14) v331_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material331 : Material (3 : Basis) (47 : Basis) where
  plus := ![v331_pa,v331_pb,v331_pg]
  minus := ![(Primitive.Addresses.material331 1).one,v331_mb,v331_mg]
  upper := v331_upper
  lower := (Primitive.Addresses.material331 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v331_pa_checked.trans (by decide +kernel)
    · exact v331_pb_checked.trans (by decide +kernel)
    · exact v331_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 47 Primitive.Addresses.material331
    · exact v331_mb_checked.trans (by decide +kernel)
    · exact v331_mg_checked.trans (by decide +kernel)
  upper_error := v331_upper_checked
  lower_error := reuse_lower_error 3 47 Primitive.Addresses.material331

def v332_pa : Scalar.QComplex := ((999993784528209465627185855849 : Int)/10^30,(3525748849390603814471149242 : Int)/10^30)
theorem v332_pa_checked : Scalar.distance (sourceCoefficient 3 48 1 0) v332_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v332_pb : Scalar.QComplex := ((1521275933175785137607462 : Int)/10^30,(-431473296230692962019081536 : Int)/10^30)
theorem v332_pb_checked : Scalar.distance (sourceCoefficient 3 48 1 1) v332_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v332_pg : Scalar.QComplex := ((-93085684885540065449548 : Int)/10^30,(-328198786290227080617 : Int)/10^30)
theorem v332_pg_checked : Scalar.distance (sourceCoefficient 3 48 1 2) v332_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v332_mb : Scalar.QComplex := ((1148933344924022898944940 : Int)/10^30,(-431474448366080077636565694 : Int)/10^30)
theorem v332_mb_checked : Scalar.distance (sourceCoefficient 3 48 3 1) v332_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v332_mg : Scalar.QComplex := ((-93085933446256400448131 : Int)/10^30,(-247869910454215607362 : Int)/10^30)
theorem v332_mg_checked : Scalar.distance (sourceCoefficient 3 48 3 2) v332_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v332_upper : Scalar.QComplex := ((999998380277595543556605640132 : Int)/10^30,(1799845044833643252752811579 : Int)/10^30)
theorem v332_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 48 5) 1) 14) v332_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material332 : Material (3 : Basis) (48 : Basis) where
  plus := ![v332_pa,v332_pb,v332_pg]
  minus := ![(Primitive.Addresses.material332 1).one,v332_mb,v332_mg]
  upper := v332_upper
  lower := (Primitive.Addresses.material332 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v332_pa_checked.trans (by decide +kernel)
    · exact v332_pb_checked.trans (by decide +kernel)
    · exact v332_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 48 Primitive.Addresses.material332
    · exact v332_mb_checked.trans (by decide +kernel)
    · exact v332_mg_checked.trans (by decide +kernel)
  upper_error := v332_upper_checked
  lower_error := reuse_lower_error 3 48 Primitive.Addresses.material332

def v333_pa : Scalar.QComplex := ((999993861987173044258958992431 : Int)/10^30,(3503710601449557250348545912 : Int)/10^30)
theorem v333_pa_checked : Scalar.distance (sourceCoefficient 3 49 1 0) v333_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v333_pb : Scalar.QComplex := ((1511766907026628024847731 : Int)/10^30,(-431473314935461866114482523 : Int)/10^30)
theorem v333_pb_checked : Scalar.distance (sourceCoefficient 3 49 1 1) v333_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v333_pg : Scalar.QComplex := ((-93085690508400054280985 : Int)/10^30,(-326147322573983133185 : Int)/10^30)
theorem v333_pg_checked : Scalar.distance (sourceCoefficient 3 49 1 2) v333_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v333_mb : Scalar.QComplex := ((1139424306174137672764884 : Int)/10^30,(-431474458864980721008669800 : Int)/10^30)
theorem v333_mb_checked : Scalar.distance (sourceCoefficient 3 49 3 1) v333_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v333_mg : Scalar.QComplex := ((-93085937298793503009225 : Int)/10^30,(-245818442649550431863 : Int)/10^30)
theorem v333_mg_checked : Scalar.distance (sourceCoefficient 3 49 3 2) v333_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v333_upper : Scalar.QComplex := ((999998419700427104150310005045 : Int)/10^30,(1777806696028834087928345519 : Int)/10^30)
theorem v333_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 49 5) 1) 14) v333_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material333 : Material (3 : Basis) (49 : Basis) where
  plus := ![v333_pa,v333_pb,v333_pg]
  minus := ![(Primitive.Addresses.material333 1).one,v333_mb,v333_mg]
  upper := v333_upper
  lower := (Primitive.Addresses.material333 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v333_pa_checked.trans (by decide +kernel)
    · exact v333_pb_checked.trans (by decide +kernel)
    · exact v333_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 49 Primitive.Addresses.material333
    · exact v333_mb_checked.trans (by decide +kernel)
    · exact v333_mg_checked.trans (by decide +kernel)
  upper_error := v333_upper_checked
  lower_error := reuse_lower_error 3 49 Primitive.Addresses.material333

def v334_pa : Scalar.QComplex := ((999993871006896720817881275555 : Int)/10^30,(3501135336144820351161762213 : Int)/10^30)
theorem v334_pa_checked : Scalar.distance (sourceCoefficient 3 50 1 0) v334_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v334_pb : Scalar.QComplex := ((1510655735911386914880297 : Int)/10^30,(-431473317102962159687455835 : Int)/10^30)
theorem v334_pb_checked : Scalar.distance (sourceCoefficient 3 50 1 1) v334_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v334_pg : Scalar.QComplex := ((-93085691162013783739987 : Int)/10^30,(-325907600102223394450 : Int)/10^30)
theorem v334_pg_checked : Scalar.distance (sourceCoefficient 3 50 1 2) v334_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v334_mb : Scalar.QComplex := ((1138313133602181219266314 : Int)/10^30,(-431474460073589580358408253 : Int)/10^30)
theorem v334_mb_checked : Scalar.distance (sourceCoefficient 3 50 3 1) v334_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v334_mg : Scalar.QComplex := ((-93085937745537292668646 : Int)/10^30,(-245578719703011114369 : Int)/10^30)
theorem v334_mg_checked : Scalar.distance (sourceCoefficient 3 50 3 2) v334_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v334_upper : Scalar.QComplex := ((999998424275463057157916898330 : Int)/10^30,(1775231418992427545433494153 : Int)/10^30)
theorem v334_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 50 5) 1) 14) v334_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material334 : Material (3 : Basis) (50 : Basis) where
  plus := ![v334_pa,v334_pb,v334_pg]
  minus := ![(Primitive.Addresses.material334 1).one,v334_mb,v334_mg]
  upper := v334_upper
  lower := (Primitive.Addresses.material334 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v334_pa_checked.trans (by decide +kernel)
    · exact v334_pb_checked.trans (by decide +kernel)
    · exact v334_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 50 Primitive.Addresses.material334
    · exact v334_mb_checked.trans (by decide +kernel)
    · exact v334_mg_checked.trans (by decide +kernel)
  upper_error := v334_upper_checked
  lower_error := reuse_lower_error 3 50 Primitive.Addresses.material334

def v335_pa : Scalar.QComplex := ((999993910503265816990554356621 : Int)/10^30,(3489836154663359445113524605 : Int)/10^30)
theorem v335_pa_checked : Scalar.distance (sourceCoefficient 3 51 1 0) v335_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v335_pb : Scalar.QComplex := ((1505780384274422430519729 : Int)/10^30,(-431473326567946401100280855 : Int)/10^30)
theorem v335_pb_checked : Scalar.distance (sourceCoefficient 3 51 1 1) v335_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v335_pg : Scalar.QComplex := ((-93085694021283227402386 : Int)/10^30,(-324855798685730303964 : Int)/10^30)
theorem v335_pg_checked : Scalar.distance (sourceCoefficient 3 51 1 2) v335_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v335_mb : Scalar.QComplex := ((1133437775612677850651141 : Int)/10^30,(-431474465331361412511301050 : Int)/10^30)
theorem v335_mb_checked : Scalar.distance (sourceCoefficient 3 51 3 1) v335_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v335_mg : Scalar.QComplex := ((-93085939697148420638109 : Int)/10^30,(-244526916210731007777 : Int)/10^30)
theorem v335_mg_checked : Scalar.distance (sourceCoefficient 3 51 3 2) v335_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v335_upper : Scalar.QComplex := ((999998444270411144863584585777 : Int)/10^30,(1763932186172620183547934322 : Int)/10^30)
theorem v335_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 51 5) 1) 14) v335_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material335 : Material (3 : Basis) (51 : Basis) where
  plus := ![v335_pa,v335_pb,v335_pg]
  minus := ![(Primitive.Addresses.material335 1).one,v335_mb,v335_mg]
  upper := v335_upper
  lower := (Primitive.Addresses.material335 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v335_pa_checked.trans (by decide +kernel)
    · exact v335_pb_checked.trans (by decide +kernel)
    · exact v335_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 51 Primitive.Addresses.material335
    · exact v335_mb_checked.trans (by decide +kernel)
    · exact v335_mg_checked.trans (by decide +kernel)
  upper_error := v335_upper_checked
  lower_error := reuse_lower_error 3 51 Primitive.Addresses.material335

def v336_pa : Scalar.QComplex := ((999993994626125199566144070747 : Int)/10^30,(3465647368831037255085046651 : Int)/10^30)
theorem v336_pa_checked : Scalar.distance (sourceCoefficient 3 52 1 0) v336_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v336_pb : Scalar.QComplex := ((1495343448403397302396918 : Int)/10^30,(-431473346583237253657404102 : Int)/10^30)
theorem v336_pb_checked : Scalar.distance (sourceCoefficient 3 52 1 1) v336_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v336_pg : Scalar.QComplex := ((-93085700095667408081536 : Int)/10^30,(-322604148970872917624 : Int)/10^30)
theorem v336_pg_checked : Scalar.distance (sourceCoefficient 3 52 1 2) v336_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v336_mb : Scalar.QComplex := ((1123000826355506388323762 : Int)/10^30,(-431474476340039217908314373 : Int)/10^30)
theorem v336_mb_checked : Scalar.distance (sourceCoefficient 3 52 3 1) v336_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v336_mg : Scalar.QComplex := ((-93085943828458046163112 : Int)/10^30,(-242275262092345747935 : Int)/10^30)
theorem v336_mg_checked : Scalar.distance (sourceCoefficient 3 52 3 2) v336_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v336_upper : Scalar.QComplex := ((999998486645495279242867312879 : Int)/10^30,(1739743291178229348244215783 : Int)/10^30)
theorem v336_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 3 52 5) 1) 14) v336_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material336 : Material (3 : Basis) (52 : Basis) where
  plus := ![v336_pa,v336_pb,v336_pg]
  minus := ![(Primitive.Addresses.material336 1).one,v336_mb,v336_mg]
  upper := v336_upper
  lower := (Primitive.Addresses.material336 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v336_pa_checked.trans (by decide +kernel)
    · exact v336_pb_checked.trans (by decide +kernel)
    · exact v336_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 3 52 Primitive.Addresses.material336
    · exact v336_mb_checked.trans (by decide +kernel)
    · exact v336_mg_checked.trans (by decide +kernel)
  upper_error := v336_upper_checked
  lower_error := reuse_lower_error 3 52 Primitive.Addresses.material336

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
