import BecknerOnofri.EntropyScalarCertificate.Bessel0395
import BecknerOnofri.EntropyScalarCertificate.Bessel0396
import BecknerOnofri.EntropyScalarCertificate.Bessel0686
import BecknerOnofri.EntropyScalarCertificate.Bessel0687
import BecknerOnofri.EntropyScalarCertificate.Brackets0158
import BecknerOnofri.EntropyScalarCertificate.Logs0316
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2528
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (358406217993900965062628581355637518650049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (358406217993900965062628581355637518650049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (359429511098851587772749858255223250031949/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (359429511098851587772749858255223250031949/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (358917864546376276417689219805430384340999/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (358917864546376276417689219805430384340999/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2528 BracketBatch0158.bracket2529 (358917864546376276417689219805430384340999/10000000000000000000000000000000000000000) (569540960127429339254867589122629619301/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2528 BracketBatch0158.bracket2529
  (358917864546376276417689219805430384340999/10000000000000000000000000000000000000000) (569540960127429339254867589122629619301/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2528
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2529
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (179714755549425793886374929127611625015973/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (179714755549425793886374929127611625015973/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (360458685426076310461184377845423621477387/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (360458685426076310461184377845423621477387/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (719888196524927898233934236100646871509333/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (719888196524927898233934236100646871509333/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2529 BracketBatch0158.bracket2530 (719888196524927898233934236100646871509333/20000000000000000000000000000000000000000) (456048941108461385572751865152758404809/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2529 BracketBatch0158.bracket2530
  (719888196524927898233934236100646871509333/20000000000000000000000000000000000000000) (456048941108461385572751865152758404809/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2529
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2530
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (45057335678259538807648047230677952684673/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45057335678259538807648047230677952684673/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (361493791821841135290154450082639891845699/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (361493791821841135290154450082639891845699/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (721952477247917445751338827928063513323083/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (721952477247917445751338827928063513323083/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2530 BracketBatch0158.bracket2531 (721952477247917445751338827928063513323083/20000000000000000000000000000000000000000) (4564663713026444315824094816970025323507/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2530 BracketBatch0158.bracket2531
  (721952477247917445751338827928063513323083/20000000000000000000000000000000000000000) (4564663713026444315824094816970025323507/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2530
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2531
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (5648340497216267738908663282541248310089/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5648340497216267738908663282541248310089/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (362534881720230180007585353760087617981891/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (362534881720230180007585353760087617981891/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (724028673542071315297739803842727509827587/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (724028673542071315297739803842727509827587/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2531 BracketBatch0158.bracket2532 (724028673542071315297739803842727509827587/20000000000000000000000000000000000000000) (571106332118628261098234051197571985859/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2531 BracketBatch0158.bracket2532
  (724028673542071315297739803842727509827587/20000000000000000000000000000000000000000) (571106332118628261098234051197571985859/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2531
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2532
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (5664607526878596562618521152501369030967/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5664607526878596562618521152501369030967/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (22723875446979048816582132335694157391499/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22723875446979048816582132335694157391499/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (45382305554493435067056216945699633515367/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (45382305554493435067056216945699633515367/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2532 BracketBatch0158.bracket2533 (45382305554493435067056216945699633515367/1250000000000000000000000000000000000000) (4573050313524481743097997833456689041947/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2532 BracketBatch0158.bracket2533
  (45382305554493435067056216945699633515367/1250000000000000000000000000000000000000) (4573050313524481743097997833456689041947/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2532
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2533
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (363582007151664781065314117371106518263981/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (363582007151664781065314117371106518263981/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (91158805187892796436294774053305177346911/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91158805187892796436294774053305177346911/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (5825737823225887734483945708674617821213/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5825737823225887734483945708674617821213/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2533 BracketBatch0158.bracket2534 (5825737823225887734483945708674617821213/160000000000000000000000000000000000000) (4577262753998855629906106205074528737681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2533 BracketBatch0158.bracket2534
  (5825737823225887734483945708674617821213/160000000000000000000000000000000000000) (4577262753998855629906106205074528737681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2533
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2534
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0395.rows BesselBatch0395.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (364635220751571185745179096213220709387641/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (364635220751571185745179096213220709387641/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (91423643942299966430430650282838687409819/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91423643942299966430430650282838687409819/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (730329796520771051466901697344575459026917/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (730329796520771051466901697344575459026917/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2534 BracketBatch0158.bracket2535 (730329796520771051466901697344575459026917/20000000000000000000000000000000000000000) (2290744025099042566476265698578583308013/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2534 BracketBatch0158.bracket2535
  (730329796520771051466901697344575459026917/20000000000000000000000000000000000000000) (2290744025099042566476265698578583308013/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2534
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2535
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (365694575769199865721722601131354749639273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (365694575769199865721722601131354749639273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0396.rows BesselBatch0396.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (91690031519149888856061066795525467836517/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91690031519149888856061066795525467836517/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0686.rows BesselBatch0686.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0687.rows BesselBatch0687.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (732454701845799421145966868313456620985341/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (732454701845799421145966868313456620985341/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0316.rows ScalarLogs0316.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0158.bracket2535 BracketBatch0158.bracket2536 (732454701845799421145966868313456620985341/20000000000000000000000000000000000000000) (1146431568633511226677248655541020449857/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0158.bracket2535 BracketBatch0158.bracket2536
  (732454701845799421145966868313456620985341/20000000000000000000000000000000000000000) (1146431568633511226677248655541020449857/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2535
