import BecknerOnofri.EntropyScalarCertificate.Bessel0077
import BecknerOnofri.EntropyScalarCertificate.Bessel0078
import BecknerOnofri.EntropyScalarCertificate.Bessel0527
import BecknerOnofri.EntropyScalarCertificate.Bessel0528
import BecknerOnofri.EntropyScalarCertificate.Brackets0031
import BecknerOnofri.EntropyScalarCertificate.Logs0062
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0496
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (98516440475873898239412449955110444427/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (98516440475873898239412449955110444427/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (789169202702527085454471098835564105211/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (789169202702527085454471098835564105211/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (1577300726509518271369770698476447660627/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1577300726509518271369770698476447660627/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0496 BracketBatch0031.bracket0497 (1577300726509518271369770698476447660627/10000000000000000000000000000000000000000) (57742485165749998969885970418310141/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0496 BracketBatch0031.bracket0497
  (1577300726509518271369770698476447660627/10000000000000000000000000000000000000000) (57742485165749998969885970418310141/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0496
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0497
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1578338405405054170908942197671128210419/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1578338405405054170908942197671128210419/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (1580413963545585007444473660164518518679/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1580413963545585007444473660164518518679/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1579376184475319589176707928917823364549/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1579376184475319589176707928917823364549/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0497 BracketBatch0031.bracket0498 (1579376184475319589176707928917823364549/10000000000000000000000000000000000000000) (464331886621103334293259655470427649/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0497 BracketBatch0031.bracket0498
  (1579376184475319589176707928917823364549/10000000000000000000000000000000000000000) (464331886621103334293259655470427649/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0497
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0498
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (395103490886396251861118415041129629669/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (395103490886396251861118415041129629669/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1582489722328428047828727842323020924497/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1582489722328428047828727842323020924497/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (3162903685874013055273201502487539443173/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3162903685874013055273201502487539443173/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0498 BracketBatch0031.bracket0499 (3162903685874013055273201502487539443173/20000000000000000000000000000000000000000) (233366603862753706740519148914889119/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0498 BracketBatch0031.bracket0499
  (3162903685874013055273201502487539443173/20000000000000000000000000000000000000000) (233366603862753706740519148914889119/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0498
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0499
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0077.rows BesselBatch0077.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (791244861164214023914363921161510462247/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (791244861164214023914363921161510462247/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1584565682046583479641896774850197123203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1584565682046583479641896774850197123203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (3167055404375011527470624617173218047697/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3167055404375011527470624617173218047697/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0499 BracketBatch0031.bracket0500 (3167055404375011527470624617173218047697/20000000000000000000000000000000000000000) (58642983644553234818159450825835541/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0499 BracketBatch0031.bracket0500
  (3167055404375011527470624617173218047697/20000000000000000000000000000000000000000) (58642983644553234818159450825835541/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0499
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0500
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (495176775639557337388092742140686601/3125000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (495176775639557337388092742140686601/3125000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (63465673719727950484338522582627196087/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63465673719727950484338522582627196087/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0527.rows BesselBatch0527.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (25369660200318257934002878715327016203/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25369660200318257934002878715327016203/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0500 BracketBatch0031.bracket0501 (25369660200318257934002878715327016203/160000000000000000000000000000000000000) (471563895465665263562596275921088419/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0500 BracketBatch0031.bracket0501
  (25369660200318257934002878715327016203/160000000000000000000000000000000000000) (471563895465665263562596275921088419/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0500
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0501
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (396660460748299690527115766141419975543/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (396660460748299690527115766141419975543/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (63548728218462755072802812910779799861/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63548728218462755072802812910779799861/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (3175360048454767638928533387335174898697/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3175360048454767638928533387335174898697/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0501 BracketBatch0031.bracket0502 (3175360048454767638928533387335174898697/20000000000000000000000000000000000000000) (473993311239637801401010854215133401/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0501 BracketBatch0031.bracket0502
  (3175360048454767638928533387335174898697/20000000000000000000000000000000000000000) (473993311239637801401010854215133401/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0501
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0502
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (794359102730784438410035161384747498261/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (794359102730784438410035161384747498261/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (159079476974513657872617206010391452341/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (159079476974513657872617206010391452341/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (794878243801676363886560595718352379983/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (794878243801676363886560595718352379983/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0502 BracketBatch0031.bracket0503 (794878243801676363886560595718352379983/5000000000000000000000000000000000000000) (19057285643974970342070920711535639/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0502 BracketBatch0031.bracket0503
  (794878243801676363886560595718352379983/5000000000000000000000000000000000000000) (19057285643974970342070920711535639/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0502
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0503
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1590794769745136578726172060103914523407/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1590794769745136578726172060103914523407/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (796435768068746323696500396412146186673/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (796435768068746323696500396412146186673/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (3183666305882629226119172852928206896753/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3183666305882629226119172852928206896753/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0062.rows ScalarLogs0062.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0503 BracketBatch0031.bracket0504 (3183666305882629226119172852928206896753/20000000000000000000000000000000000000000) (478880409700536790874805828233477531/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0503 BracketBatch0031.bracket0504
  (3183666305882629226119172852928206896753/20000000000000000000000000000000000000000) (478880409700536790874805828233477531/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0503
