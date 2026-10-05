module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0232
public import BecknerOnofri.EntropyScalarCertificate.Bessel0233
public import BecknerOnofri.EntropyScalarCertificate.Bessel0605
public import BecknerOnofri.EntropyScalarCertificate.Brackets0093
public import BecknerOnofri.EntropyScalarCertificate.Logs0186
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1488
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (17490069726310671169372017807391060508379/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17490069726310671169372017807391060508379/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (8749818254305920628829318155954043324821/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8749818254305920628829318155954043324821/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (34989706234922512427030654119299147158021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34989706234922512427030654119299147158021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1488 BracketBatch0093.bracket1489 (34989706234922512427030654119299147158021/20000000000000000000000000000000000000000) (334427734081055943529681842845929936387/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1488 BracketBatch0093.bracket1489
  (34989706234922512427030654119299147158021/20000000000000000000000000000000000000000) (334427734081055943529681842845929936387/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1488
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1489
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (17499636508611841257658636311908086649639/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17499636508611841257658636311908086649639/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (17509215264501700432608211703651708859721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17509215264501700432608211703651708859721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (437610647163919271128335600194497443867/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (437610647163919271128335600194497443867/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1489 BracketBatch0093.bracket1490 (437610647163919271128335600194497443867/250000000000000000000000000000000000000) (669376491710066491643138094284086595941/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1489 BracketBatch0093.bracket1490
  (437610647163919271128335600194497443867/250000000000000000000000000000000000000) (669376491710066491643138094284086595941/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1489
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1490
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (8754607632250850216304105851825854429859/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8754607632250850216304105851825854429859/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (17518806018124348708966908923157104394009/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17518806018124348708966908923157104394009/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (35028021282626049141575120626808813253727/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35028021282626049141575120626808813253727/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1490 BracketBatch0093.bracket1491 (35028021282626049141575120626808813253727/20000000000000000000000000000000000000000) (334949026018621369803067085492114029293/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1490 BracketBatch0093.bracket1491
  (35028021282626049141575120626808813253727/20000000000000000000000000000000000000000) (334949026018621369803067085492114029293/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1490
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1491
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0232.rows BesselBatch0232.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (8759403009062174354483454461578552197003/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8759403009062174354483454461578552197003/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (17528408793686261669148588475294212750907/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17528408793686261669148588475294212750907/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (35047214811810610378115497398451317144913/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35047214811810610378115497398451317144913/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1491 BracketBatch0093.bracket1492 (35047214811810610378115497398451317144913/20000000000000000000000000000000000000000) (670420149952767730853963629803988935791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1491 BracketBatch0093.bracket1492
  (35047214811810610378115497398451317144913/20000000000000000000000000000000000000000) (670420149952767730853963629803988935791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1491
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1492
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2191051099210782708643573559411776593863/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2191051099210782708643573559411776593863/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (8769011807728241413568791731243396111889/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8769011807728241413568791731243396111889/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (17533216204571372248143085968890502487341/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17533216204571372248143085968890502487341/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1492 BracketBatch0093.bracket1493 (17533216204571372248143085968890502487341/10000000000000000000000000000000000000000) (134188557253456991590114095751799953543/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1492 BracketBatch0093.bracket1493
  (17533216204571372248143085968890502487341/10000000000000000000000000000000000000000) (134188557253456991590114095751799953543/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1492
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1493
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (701520944618259313085503338499471688951/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (701520944618259313085503338499471688951/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (17547650507766816684213492495584385527299/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17547650507766816684213492495584385527299/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (17542837061611649755675537979035588875537/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17542837061611649755675537979035588875537/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1493 BracketBatch0093.bracket1494 (17542837061611649755675537979035588875537/10000000000000000000000000000000000000000) (671465961792957297254887945507250225749/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1493 BracketBatch0093.bracket1494
  (17542837061611649755675537979035588875537/10000000000000000000000000000000000000000) (671465961792957297254887945507250225749/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1493
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1494
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (34272754897982063836354477530438252983/19531250000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (34272754897982063836354477530438252983/19531250000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (8778644747506011239710583795150476323517/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8778644747506011239710583795150476323517/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (3510494000277883916363466008588533817433/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3510494000277883916363466008588533817433/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1494 BracketBatch0093.bracket1495 (3510494000277883916363466008588533817433/2000000000000000000000000000000000000000) (134397935468694001220086870399326273961/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1494 BracketBatch0093.bracket1495
  (3510494000277883916363466008588533817433/2000000000000000000000000000000000000000) (134397935468694001220086870399326273961/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1494
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1495
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (17557289495012022479421167590300952647031/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17557289495012022479421167590300952647031/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0233.rows BesselBatch0233.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (8783470300825004318861926306426391688789/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8783470300825004318861926306426391688789/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0605.rows BesselBatch0605.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (35124230096662031117145020203153736024609/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35124230096662031117145020203153736024609/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0186.rows ScalarLogs0186.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0093.bracket1495 BracketBatch0093.bracket1496 (35124230096662031117145020203153736024609/20000000000000000000000000000000000000000) (168128483433508431509152050945761517761/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0093.bracket1495 BracketBatch0093.bracket1496
  (35124230096662031117145020203153736024609/20000000000000000000000000000000000000000) (168128483433508431509152050945761517761/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1495
