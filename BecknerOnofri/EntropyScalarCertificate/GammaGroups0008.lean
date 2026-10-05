module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0010
public import BecknerOnofri.EntropyScalarCertificate.Bessel0011
public import BecknerOnofri.EntropyScalarCertificate.Bessel0493
public import BecknerOnofri.EntropyScalarCertificate.Bessel0494
public import BecknerOnofri.EntropyScalarCertificate.Brackets0004
public import BecknerOnofri.EntropyScalarCertificate.Logs0008
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0064
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (43416922063764615709353602485671074237/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43416922063764615709353602485671074237/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (34834264969458992896787424700942658977/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (34834264969458992896787424700942658977/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (347839013102353427321351533447397591833/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (347839013102353427321351533447397591833/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0064 BracketBatch0004.bracket0065 (347839013102353427321351533447397591833/5000000000000000000000000000000000000000) (8798163757349438764990379117636513/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0064 BracketBatch0004.bracket0065
  (347839013102353427321351533447397591833/5000000000000000000000000000000000000000) (8798163757349438764990379117636513/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0064
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0065
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (696685299389179857935748494018853179537/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (696685299389179857935748494018853179537/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (139739986057602401097051108335225538679/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (139739986057602401097051108335225538679/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (348846307419297965855251008923745218233/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (348846307419297965855251008923745218233/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0065 BracketBatch0004.bracket0066 (348846307419297965855251008923745218233/5000000000000000000000000000000000000000) (4451305093737528271793795178964209/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0065 BracketBatch0004.bracket0066
  (348846307419297965855251008923745218233/5000000000000000000000000000000000000000) (4451305093737528271793795178964209/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0065
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0066
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (43668745643000750342828471354757980837/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43668745643000750342828471354757980837/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (175178661491644130681582368028382365869/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (175178661491644130681582368028382365869/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (349853644063647132052896253447414289217/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (349853644063647132052896253447414289217/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0066 BracketBatch0004.bracket0067 (349853644063647132052896253447414289217/5000000000000000000000000000000000000000) (4503982054147212779777185004641877/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0066 BracketBatch0004.bracket0067
  (349853644063647132052896253447414289217/5000000000000000000000000000000000000000) (4503982054147212779777185004641877/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0066
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0067
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (700714645966576522726329472113529463473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (700714645966576522726329472113529463473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (10722800394817767819775080216501347/152587890625000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10722800394817767819775080216501347/152587890625000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (280688818528270750912621825836432348093/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (280688818528270750912621825836432348093/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0067 BracketBatch0004.bracket0068 (280688818528270750912621825836432348093/4000000000000000000000000000000000000000) (18228461552654182374900422963662389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0067 BracketBatch0004.bracket0068
  (280688818528270750912621825836432348093/4000000000000000000000000000000000000000) (18228461552654182374900422963662389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0067
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0068
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (702729446674777231836779657068632276989/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (702729446674777231836779657068632276989/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (5505815098926372847346973626413963597/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5505815098926372847346973626413963597/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (281494755867470591259438456249923923481/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (281494755867470591259438456249923923481/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0068 BracketBatch0004.bracket0069 (281494755867470591259438456249923923481/4000000000000000000000000000000000000000) (18442830926987978975594827915103251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0068 BracketBatch0004.bracket0069
  (281494755867470591259438456249923923481/4000000000000000000000000000000000000000) (18442830926987978975594827915103251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0068
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0069
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (704744332662575724460412624180987340413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (704744332662575724460412624180987340413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (14135186083599830756360367503907870417/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14135186083599830756360367503907870417/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1411503636842567262278430999376380861263/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1411503636842567262278430999376380861263/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0069 BracketBatch0004.bracket0070 (1411503636842567262278430999376380861263/20000000000000000000000000000000000000000) (4664761728560009925187123662249907/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0069 BracketBatch0004.bracket0070
  (1411503636842567262278430999376380861263/20000000000000000000000000000000000000000) (4664761728560009925187123662249907/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0069
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0070
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0010.rows BesselBatch0010.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (706759304179991537818018375195393520847/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (706759304179991537818018375195393520847/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (708774361477102330913307262612488929291/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (708774361477102330913307262612488929291/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (707766832828546934365662818903941225069/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (707766832828546934365662818903941225069/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0070 BracketBatch0004.bracket0071 (707766832828546934365662818903941225069/10000000000000000000000000000000000000000) (18877120119873250797019775888876081/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0070 BracketBatch0004.bracket0071
  (707766832828546934365662818903941225069/10000000000000000000000000000000000000000) (18877120119873250797019775888876081/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0070
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0071
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (88596795184637791364163407826561116161/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (88596795184637791364163407826561116161/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0011.rows BesselBatch0011.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (177697376201011015208525105563316137093/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (177697376201011015208525105563316137093/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0494.rows BesselBatch0494.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (70978193314057319587370384243287673883/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (70978193314057319587370384243287673883/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0008.rows ScalarLogs0008.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0004.bracket0071 BracketBatch0004.bracket0072 (70978193314057319587370384243287673883/1000000000000000000000000000000000000000) (19097061180168762315603652163978537/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0004.bracket0071 BracketBatch0004.bracket0072
  (70978193314057319587370384243287673883/1000000000000000000000000000000000000000) (19097061180168762315603652163978537/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0071
