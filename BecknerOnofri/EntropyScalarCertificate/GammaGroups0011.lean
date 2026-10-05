module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0013
public import BecknerOnofri.EntropyScalarCertificate.Bessel0014
public import BecknerOnofri.EntropyScalarCertificate.Bessel0015
public import BecknerOnofri.EntropyScalarCertificate.Bessel0495
public import BecknerOnofri.EntropyScalarCertificate.Bessel0496
public import BecknerOnofri.EntropyScalarCertificate.Brackets0005
public import BecknerOnofri.EntropyScalarCertificate.Brackets0006
public import BecknerOnofri.EntropyScalarCertificate.Logs0011
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0088
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (371521851215881049910495635037528248969/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (371521851215881049910495635037528248969/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (372530173296989086987699785163913095327/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (372530173296989086987699785163913095327/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (93006503064108767112274427525180168037/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93006503064108767112274427525180168037/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0088 BracketBatch0005.bracket0089 (93006503064108767112274427525180168037/1250000000000000000000000000000000000000) (23132296945940592759469599194906351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0088 BracketBatch0005.bracket0089
  (93006503064108767112274427525180168037/1250000000000000000000000000000000000000) (23132296945940592759469599194906351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0088
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0089
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0013.rows BesselBatch0013.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (745060346593978173975399570327826190651/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (745060346593978173975399570327826190651/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (747077081298642946376767212372788795283/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (747077081298642946376767212372788795283/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (746068713946310560176083391350307492967/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (746068713946310560176083391350307492967/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0089 BracketBatch0005.bracket0090 (746068713946310560176083391350307492967/10000000000000000000000000000000000000000) (1169385667922246106463794129899751/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0089 BracketBatch0005.bracket0090
  (746068713946310560176083391350307492967/10000000000000000000000000000000000000000) (1169385667922246106463794129899751/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0089
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0090
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (9338463516233036829709590154659859941/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9338463516233036829709590154659859941/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (374546953398516831925266755977679352023/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (374546953398516831925266755977679352023/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0495.rows BesselBatch0495.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (748085494047838305113650362164073749663/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (748085494047838305113650362164073749663/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0090 BracketBatch0005.bracket0091 (748085494047838305113650362164073749663/10000000000000000000000000000000000000000) (4729041115484376238383488107642127/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0090 BracketBatch0005.bracket0091
  (748085494047838305113650362164073749663/10000000000000000000000000000000000000000) (4729041115484376238383488107642127/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0090
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0091
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (749093906797033663850533511955358704043/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (749093906797033663850533511955358704043/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (46944426458780588612654564672123598359/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (46944426458780588612654564672123598359/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1500204730137523081653006546709336277787/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1500204730137523081653006546709336277787/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0091 BracketBatch0005.bracket0092 (1500204730137523081653006546709336277787/20000000000000000000000000000000000000000) (23904784856628902881975460114545897/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0091 BracketBatch0005.bracket0092
  (1500204730137523081653006546709336277787/20000000000000000000000000000000000000000) (23904784856628902881975460114545897/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0091
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0092
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (751110823340489417802473034753977573741/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (751110823340489417802473034753977573741/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (753127831180411322590715771264001561429/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (753127831180411322590715771264001561429/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (150423865452090074039318880601797913517/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (150423865452090074039318880601797913517/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0092 BracketBatch0005.bracket0093 (150423865452090074039318880601797913517/2000000000000000000000000000000000000000) (24166462480753986536669042540293753/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0092 BracketBatch0005.bracket0093
  (150423865452090074039318880601797913517/2000000000000000000000000000000000000000) (24166462480753986536669042540293753/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0092
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0093
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (376563915590205661295357885632000780713/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (376563915590205661295357885632000780713/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (151028986113652538799952107862521117627/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (151028986113652538799952107862521117627/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1508272761748674016590476310576607149561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1508272761748674016590476310576607149561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0093 BracketBatch0005.bracket0094 (1508272761748674016590476310576607149561/20000000000000000000000000000000000000000) (24430249765421217643142467330877667/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0093 BracketBatch0005.bracket0094
  (1508272761748674016590476310576607149561/20000000000000000000000000000000000000000) (24430249765421217643142467330877667/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0093
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0094
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (188786232642065673499940134828151397033/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (188786232642065673499940134828151397033/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (94645265219446153477098925476043430587/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (94645265219446153477098925476043430587/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (378076763080957980454137985780238258207/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (378076763080957980454137985780238258207/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0094 BracketBatch0005.bracket0095 (378076763080957980454137985780238258207/5000000000000000000000000000000000000000) (12348079028598151639008658211078051/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0094 BracketBatch0005.bracket0095
  (378076763080957980454137985780238258207/5000000000000000000000000000000000000000) (12348079028598151639008658211078051/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0094
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0095
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0014.rows BesselBatch0014.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (757162121755569227816791403808347444693/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (757162121755569227816791403808347444693/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0015.rows BesselBatch0015.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (379589702496959589255303605201105303387/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (379589702496959589255303605201105303387/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0496.rows BesselBatch0496.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1516341526749488406327398614210558051467/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1516341526749488406327398614210558051467/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0011.rows ScalarLogs0011.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0005.bracket0095 BracketBatch0006.bracket0096 (1516341526749488406327398614210558051467/20000000000000000000000000000000000000000) (24964198733592123246580631593237291/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0005.bracket0095 BracketBatch0006.bracket0096
  (1516341526749488406327398614210558051467/20000000000000000000000000000000000000000) (24964198733592123246580631593237291/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0095
