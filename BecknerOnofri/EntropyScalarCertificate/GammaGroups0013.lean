import BecknerOnofri.EntropyScalarCertificate.Bessel0016
import BecknerOnofri.EntropyScalarCertificate.Bessel0017
import BecknerOnofri.EntropyScalarCertificate.Bessel0497
import BecknerOnofri.EntropyScalarCertificate.Brackets0006
import BecknerOnofri.EntropyScalarCertificate.Brackets0007
import BecknerOnofri.EntropyScalarCertificate.Logs0013
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0104
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (775321014949658383676664006134517225643/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (775321014949658383676664006134517225643/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (388669568989640649445168528420969331757/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (388669568989640649445168528420969331757/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (1552660152928939682567001062976455889157/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1552660152928939682567001062976455889157/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0104 BracketBatch0006.bracket0105 (1552660152928939682567001062976455889157/20000000000000000000000000000000000000000) (6868603686188681601763863023009093/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0104 BracketBatch0006.bracket0105
  (1552660152928939682567001062976455889157/20000000000000000000000000000000000000000) (6868603686188681601763863023009093/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0104
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0105
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (777339137979281298890337056841938663511/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (777339137979281298890337056841938663511/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (779357355579310286512832116466731411663/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (779357355579310286512832116466731411663/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (778348246779295792701584586654335037587/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (778348246779295792701584586654335037587/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0105 BracketBatch0006.bracket0106 (778348246779295792701584586654335037587/10000000000000000000000000000000000000000) (27764411842944811650791575777046789/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0105 BracketBatch0006.bracket0106
  (778348246779295792701584586654335037587/10000000000000000000000000000000000000000) (27764411842944811650791575777046789/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0105
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0106
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (38967867778965514325641605823336570583/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38967867778965514325641605823336570583/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (390687834001016784489373647666049661037/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (390687834001016784489373647666049661037/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (780366511790671927745789705899415366867/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (780366511790671927745789705899415366867/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0106 BracketBatch0006.bracket0107 (780366511790671927745789705899415366867/10000000000000000000000000000000000000000) (28056668522514072637519685279197557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0106 BracketBatch0006.bracket0107
  (780366511790671927745789705899415366867/10000000000000000000000000000000000000000) (28056668522514072637519685279197557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0106
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0107
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (781375668002033568978747295332099322071/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (781375668002033568978747295332099322071/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (391697037749902039834285732134245729099/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (391697037749902039834285732134245729099/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1564769743501837648647318759600590780269/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1564769743501837648647318759600590780269/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0107 BracketBatch0006.bracket0108 (1564769743501837648647318759600590780269/20000000000000000000000000000000000000000) (28351196532780175600542808836549663/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0107 BracketBatch0006.bracket0108
  (1564769743501837648647318759600590780269/20000000000000000000000000000000000000000) (28351196532780175600542808836549663/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0107
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0108
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0016.rows BesselBatch0016.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (156678815099960815933714292853698291639/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (156678815099960815933714292853698291639/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (785412578325039642949944597154589781357/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (785412578325039642949944597154589781357/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1532037747875823947869644591233477773/19531250000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1532037747875823947869644591233477773/19531250000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0108 BracketBatch0006.bracket0109 (1532037747875823947869644591233477773/19531250000000000000000000000000000000) (7162001913520389093234458057856919/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0108 BracketBatch0006.bracket0109
  (1532037747875823947869644591233477773/19531250000000000000000000000000000000) (7162001913520389093234458057856919/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0108
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0109
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (392706289162519821474972298577294890677/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (392706289162519821474972298577294890677/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (157486235346044630865181076363500501899/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (157486235346044630865181076363500501899/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (1572843755055262797275849978972092290849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1572843755055262797275849978972092290849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0109 BracketBatch0006.bracket0110 (1572843755055262797275849978972092290849/20000000000000000000000000000000000000000) (3618389212222899013525877688390963/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0109 BracketBatch0006.bracket0110
  (1572843755055262797275849978972092290849/20000000000000000000000000000000000000000) (3618389212222899013525877688390963/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0109
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0110
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (196857794182555788581476345454375627373/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (196857794182555788581476345454375627373/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (789449870967902760690440921953000061543/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (789449870967902760690440921953000061543/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (315376209539625183003269260754100514207/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (315376209539625183003269260754100514207/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0110 BracketBatch0006.bracket0111 (315376209539625183003269260754100514207/4000000000000000000000000000000000000000) (7312131626570597203458063128487807/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0110 BracketBatch0006.bracket0111
  (315376209539625183003269260754100514207/4000000000000000000000000000000000000000) (7312131626570597203458063128487807/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0110
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0111
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (39472493548395138034522046097650003077/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (39472493548395138034522046097650003077/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0017.rows BesselBatch0017.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (791468661290692040691653675852559977463/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (791468661290692040691653675852559977463/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0497.rows BesselBatch0497.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1580918532258594801382094597805560039003/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1580918532258594801382094597805560039003/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0013.rows ScalarLogs0013.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0006.bracket0111 BracketBatch0007.bracket0112 (1580918532258594801382094597805560039003/20000000000000000000000000000000000000000) (923508061031705772045739955050927/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0006.bracket0111 BracketBatch0007.bracket0112
  (1580918532258594801382094597805560039003/20000000000000000000000000000000000000000) (923508061031705772045739955050927/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0111
