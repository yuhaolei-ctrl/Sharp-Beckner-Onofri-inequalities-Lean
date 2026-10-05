import BecknerOnofri.EntropyScalarCertificate.Bessel0121
import BecknerOnofri.EntropyScalarCertificate.Bessel0122
import BecknerOnofri.EntropyScalarCertificate.Bessel0549
import BecknerOnofri.EntropyScalarCertificate.Bessel0550
import BecknerOnofri.EntropyScalarCertificate.Brackets0048
import BecknerOnofri.EntropyScalarCertificate.Brackets0049
import BecknerOnofri.EntropyScalarCertificate.Logs0097
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0776
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (2670953433392726444095554232945739501631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2670953433392726444095554232945739501631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (167628615014130437688525609833888361047/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (167628615014130437688525609833888361047/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (5353011273618813447111963990287953278383/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5353011273618813447111963990287953278383/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0776 BracketBatch0048.bracket0777 (5353011273618813447111963990287953278383/20000000000000000000000000000000000000000) (3533799468309104010361134412261014077/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0776 BracketBatch0048.bracket0777
  (5353011273618813447111963990287953278383/20000000000000000000000000000000000000000) (3533799468309104010361134412261014077/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0776
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0777
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2682057840226087003016409757342213776749/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2682057840226087003016409757342213776749/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (2693171683647793902220328246546505844567/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2693171683647793902220328246546505844567/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1343807380968470226309184500972179905329/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1343807380968470226309184500972179905329/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0777 BracketBatch0048.bracket0778 (1343807380968470226309184500972179905329/5000000000000000000000000000000000000000) (224366471779029171489897743825556641/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0777 BracketBatch0048.bracket0778
  (1343807380968470226309184500972179905329/5000000000000000000000000000000000000000) (224366471779029171489897743825556641/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0777
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0778
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (673292920911948475555082061636626461141/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (673292920911948475555082061636626461141/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2704295014968741686670554583999829942161/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2704295014968741686670554583999829942161/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (215898667944661423555635313221853431469/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (215898667944661423555635313221853431469/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0778 BracketBatch0048.bracket0779 (215898667944661423555635313221853431469/800000000000000000000000000000000000000) (3646599751250143127255543050284592359/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0778 BracketBatch0048.bracket0779
  (215898667944661423555635313221853431469/800000000000000000000000000000000000000) (3646599751250143127255543050284592359/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0778
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0779
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1352147507484370843335277291999914971079/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1352147507484370843335277291999914971079/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1357713942852802158319891005018516946991/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1357713942852802158319891005018516946991/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (270986145033717300165516829701843191807/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (270986145033717300165516829701843191807/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0779 BracketBatch0048.bracket0780 (270986145033717300165516829701843191807/1000000000000000000000000000000000000000) (926003414731991162678471135636750517/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0779 BracketBatch0048.bracket0780
  (270986145033717300165516829701843191807/1000000000000000000000000000000000000000) (926003414731991162678471135636750517/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0779
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0780
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0121.rows BesselBatch0121.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2715427885705604316639782010037033893979/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2715427885705604316639782010037033893979/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (170410646723898523041983786214887940789/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (170410646723898523041983786214887940789/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (5441998233287980685311522589475240946603/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5441998233287980685311522589475240946603/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0780 BracketBatch0048.bracket0781 (5441998233287980685311522589475240946603/20000000000000000000000000000000000000000) (752422176329792957986920982546298793/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0780 BracketBatch0048.bracket0781
  (5441998233287980685311522589475240946603/20000000000000000000000000000000000000000) (752422176329792957986920982546298793/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0780
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0781
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (2726570347582376368671740579438207052621/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2726570347582376368671740579438207052621/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (2737722452531925911615656411030005703019/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2737722452531925911615656411030005703019/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0549.rows BesselBatch0549.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (136607320002857557007184924761705318891/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (136607320002857557007184924761705318891/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0781 BracketBatch0048.bracket0782 (136607320002857557007184924761705318891/500000000000000000000000000000000000000) (3820897057539268663503953740700390157/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0781 BracketBatch0048.bracket0782
  (136607320002857557007184924761705318891/500000000000000000000000000000000000000) (3820897057539268663503953740700390157/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0781
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0782
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (342215306566490738951957051378750712877/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (342215306566490738951957051378750712877/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2748884252697559174701897885101290355077/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2748884252697559174701897885101290355077/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (5486606705229485086317554296131296058093/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5486606705229485086317554296131296058093/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0782 BracketBatch0048.bracket0783 (5486606705229485086317554296131296058093/20000000000000000000000000000000000000000) (1940188926393293013524034096992834657/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0782 BracketBatch0048.bracket0783
  (5486606705229485086317554296131296058093/20000000000000000000000000000000000000000) (1940188926393293013524034096992834657/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0782
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0783
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1374442126348779587350948942550645177537/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1374442126348779587350948942550645177537/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0122.rows BesselBatch0122.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2760055800434597125902616014827199706881/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2760055800434597125902616014827199706881/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0550.rows BesselBatch0550.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (1101788010626431260120902779985698012391/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1101788010626431260120902779985698012391/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0097.rows ScalarLogs0097.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0048.bracket0783 BracketBatch0049.bracket0784 (1101788010626431260120902779985698012391/4000000000000000000000000000000000000000) (78811179234546238050156159470728211/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0048.bracket0783 BracketBatch0049.bracket0784
  (1101788010626431260120902779985698012391/4000000000000000000000000000000000000000) (78811179234546238050156159470728211/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0783
