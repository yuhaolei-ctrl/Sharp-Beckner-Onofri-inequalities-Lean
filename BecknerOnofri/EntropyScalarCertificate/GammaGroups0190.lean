import BecknerOnofri.EntropyScalarCertificate.Bessel0237
import BecknerOnofri.EntropyScalarCertificate.Bessel0238
import BecknerOnofri.EntropyScalarCertificate.Bessel0607
import BecknerOnofri.EntropyScalarCertificate.Bessel0608
import BecknerOnofri.EntropyScalarCertificate.Brackets0095
import BecknerOnofri.EntropyScalarCertificate.Logs0190
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1520
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (17802267697073781271818554759567067458353/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17802267697073781271818554759567067458353/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1781222992612884702375862332882267612907/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1781222992612884702375862332882267612907/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (35614497623202628295577178088389743587423/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35614497623202628295577178088389743587423/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1520 BracketBatch0095.bracket1521 (35614497623202628295577178088389743587423/20000000000000000000000000000000000000000) (171449633149593431907041282936753590001/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1520 BracketBatch0095.bracket1521
  (35614497623202628295577178088389743587423/20000000000000000000000000000000000000000) (171449633149593431907041282936753590001/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1520
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1521
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (17812229926128847023758623328822676129067/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17812229926128847023758623328822676129067/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (17822204933301689129399455125926143552107/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17822204933301689129399455125926143552107/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (17817217429715268076579039227374409840587/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17817217429715268076579039227374409840587/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1521 BracketBatch0095.bracket1522 (17817217429715268076579039227374409840587/10000000000000000000000000000000000000000) (171584285509641430374542323050177471399/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1521 BracketBatch0095.bracket1522
  (17817217429715268076579039227374409840587/10000000000000000000000000000000000000000) (171584285509641430374542323050177471399/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1521
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1522
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2227775616662711141174931890740767944013/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2227775616662711141174931890740767944013/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (17832192744831377877724953769602976962453/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17832192744831377877724953769602976962453/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (35654397678133067007124408895529120514557/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35654397678133067007124408895529120514557/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1522 BracketBatch0095.bracket1523 (35654397678133067007124408895529120514557/20000000000000000000000000000000000000000) (42929769682327160336702784224511161621/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1522 BracketBatch0095.bracket1523
  (35654397678133067007124408895529120514557/20000000000000000000000000000000000000000) (42929769682327160336702784224511161621/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1522
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1523
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0237.rows BesselBatch0237.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (356643854896627557554499075392059539249/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (356643854896627557554499075392059539249/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (17842193387025872962815895631952047952459/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17842193387025872962815895631952047952459/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (35674386131857250840540849401555024914909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35674386131857250840540849401555024914909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1523 BracketBatch0095.bracket1524 (35674386131857250840540849401555024914909/20000000000000000000000000000000000000000) (2749664208374184820219230275538112481/40000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1523 BracketBatch0095.bracket1524
  (35674386131857250840540849401555024914909/20000000000000000000000000000000000000000) (2749664208374184820219230275538112481/40000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1523
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1524
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2230274173378234120351986953994005994057/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2230274173378234120351986953994005994057/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (17852206886262239512572815629105567979309/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17852206886262239512572815629105567979309/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0607.rows BesselBatch0607.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (7138880054657622495077742252211523186353/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7138880054657622495077742252211523186353/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1524 BracketBatch0095.bracket1525 (7138880054657622495077742252211523186353/4000000000000000000000000000000000000000) (343978177214140895473516218331877680141/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1524 BracketBatch0095.bracket1525
  (7138880054657622495077742252211523186353/4000000000000000000000000000000000000000) (343978177214140895473516218331877680141/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1524
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1525
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (8926103443131119756286407814552783989653/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8926103443131119756286407814552783989653/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (4465558317246716227649025278319089163693/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4465558317246716227649025278319089163693/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (17857220077624552211584458371190962317039/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17857220077624552211584458371190962317039/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1525 BracketBatch0095.bracket1526 (17857220077624552211584458371190962317039/10000000000000000000000000000000000000000) (137699444556768174551235080507380919943/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1525 BracketBatch0095.bracket1526
  (17857220077624552211584458371190962317039/10000000000000000000000000000000000000000) (137699444556768174551235080507380919943/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1525
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1526
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (17862233268986864910596101113276356654769/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17862233268986864910596101113276356654769/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1787227256171567641466666328283983001443/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1787227256171567641466666328283983001443/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (35734505830702541325262764396116186669199/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35734505830702541325262764396116186669199/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1526 BracketBatch0095.bracket1527 (35734505830702541325262764396116186669199/20000000000000000000000000000000000000000) (172259664506061150174870570169800374003/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1526 BracketBatch0095.bracket1527
  (35734505830702541325262764396116186669199/20000000000000000000000000000000000000000) (172259664506061150174870570169800374003/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1526
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1527
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (17872272561715676414666663282839830014427/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17872272561715676414666663282839830014427/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0238.rows BesselBatch0238.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (447058119775858989382212670873392072559/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (447058119775858989382212670873392072559/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0608.rows BesselBatch0608.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (35754597352750035989955170117775512916787/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (35754597352750035989955170117775512916787/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0190.rows ScalarLogs0190.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0095.bracket1527 BracketBatch0095.bracket1528 (35754597352750035989955170117775512916787/20000000000000000000000000000000000000000) (86197582626892366692702801351392444661/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0095.bracket1527 BracketBatch0095.bracket1528
  (35754597352750035989955170117775512916787/20000000000000000000000000000000000000000) (86197582626892366692702801351392444661/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1527
