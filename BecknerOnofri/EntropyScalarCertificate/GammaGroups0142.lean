import BecknerOnofri.EntropyScalarCertificate.Bessel0177
import BecknerOnofri.EntropyScalarCertificate.Bessel0178
import BecknerOnofri.EntropyScalarCertificate.Bessel0577
import BecknerOnofri.EntropyScalarCertificate.Bessel0578
import BecknerOnofri.EntropyScalarCertificate.Brackets0071
import BecknerOnofri.EntropyScalarCertificate.Logs0142
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1136
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (7958554022539139325949011317977282115873/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7958554022539139325949011317977282115873/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (7980348800893676273937996165925712083151/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7980348800893676273937996165925712083151/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (996181426464550974992937967743937137439/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (996181426464550974992937967743937137439/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1136 BracketBatch0071.bracket1137 (996181426464550974992937967743937137439/1250000000000000000000000000000000000000) (68778703032599472166571818130951701159/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1136 BracketBatch0071.bracket1137
  (996181426464550974992937967743937137439/1250000000000000000000000000000000000000) (68778703032599472166571818130951701159/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1136
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1137
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1995087200223419068484499041481428020787/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1995087200223419068484499041481428020787/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (500138761402317120117006555693065396977/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (500138761402317120117006555693065396977/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (799128449166537509790505052850737921739/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (799128449166537509790505052850737921739/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1137 BracketBatch0071.bracket1138 (799128449166537509790505052850737921739/1000000000000000000000000000000000000000) (69281251210297282030858719581900126327/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1137 BracketBatch0071.bracket1138
  (799128449166537509790505052850737921739/1000000000000000000000000000000000000000) (69281251210297282030858719581900126327/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1137
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1138
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (8002220182437073921872104891089046351629/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8002220182437073921872104891089046351629/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (4012084385179886420311989530316410452559/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4012084385179886420311989530316410452559/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (16026388952796846762496083951721867256747/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16026388952796846762496083951721867256747/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1138 BracketBatch0071.bracket1139 (16026388952796846762496083951721867256747/20000000000000000000000000000000000000000) (69786968395838904189914265898631200751/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1138 BracketBatch0071.bracket1139
  (16026388952796846762496083951721867256747/20000000000000000000000000000000000000000) (69786968395838904189914265898631200751/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1138
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1139
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0177.rows BesselBatch0177.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1604833754071954568124795812126564181023/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1604833754071954568124795812126564181023/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (8046195174379973136470277670626764469973/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8046195174379973136470277670626764469973/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1004397746546234123568391045703724085943/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1004397746546234123568391045703724085943/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1139 BracketBatch0071.bracket1140 (1004397746546234123568391045703724085943/1250000000000000000000000000000000000000) (35147937087048287868214993202525416469/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1139 BracketBatch0071.bracket1140
  (1004397746546234123568391045703724085943/1250000000000000000000000000000000000000) (35147937087048287868214993202525416469/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1139
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1140
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (804619517437997313647027767062676446997/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (804619517437997313647027767062676446997/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (806830001083490676691619972867933085073/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (806830001083490676691619972867933085073/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0577.rows BesselBatch0577.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (161144951852148799033864773993060953207/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (161144951852148799033864773993060953207/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1140 BracketBatch0071.bracket1141 (161144951852148799033864773993060953207/200000000000000000000000000000000000000) (141615976577021972899409868233117504321/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1140 BracketBatch0071.bracket1141
  (161144951852148799033864773993060953207/200000000000000000000000000000000000000) (141615976577021972899409868233117504321/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1140
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1141
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (8068300010834906766916199728679330850727/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8068300010834906766916199728679330850727/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (809048390277365416657709390914896489147/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (809048390277365416657709390914896489147/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (16158783913608560933493293637828295742197/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16158783913608560933493293637828295742197/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1141 BracketBatch0071.bracket1142 (16158783913608560933493293637828295742197/20000000000000000000000000000000000000000) (89154163303788862501583148733323657/6250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1141 BracketBatch0071.bracket1142
  (16158783913608560933493293637828295742197/20000000000000000000000000000000000000000) (89154163303788862501583148733323657/6250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1141
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1142
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (8090483902773654166577093909148964891467/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8090483902773654166577093909148964891467/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (8112747480051535708832401806640674924531/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8112747480051535708832401806640674924531/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (8101615691412594937704747857894819907999/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8101615691412594937704747857894819907999/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1142 BracketBatch0071.bracket1143 (8101615691412594937704747857894819907999/10000000000000000000000000000000000000000) (143683842608169451628811506651396383753/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1142 BracketBatch0071.bracket1143
  (8101615691412594937704747857894819907999/10000000000000000000000000000000000000000) (143683842608169451628811506651396383753/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1142
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1143
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (507046717503220981802025112915042182783/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (507046717503220981802025112915042182783/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (8135091379426109215762690075880325027021/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8135091379426109215762690075880325027021/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (16247838859477644924595091882520999951549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16247838859477644924595091882520999951549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0142.rows ScalarLogs0142.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1143 BracketBatch0071.bracket1144 (16247838859477644924595091882520999951549/20000000000000000000000000000000000000000) (72363780502580619650025065006535817133/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1143 BracketBatch0071.bracket1144
  (16247838859477644924595091882520999951549/20000000000000000000000000000000000000000) (72363780502580619650025065006535817133/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1143
