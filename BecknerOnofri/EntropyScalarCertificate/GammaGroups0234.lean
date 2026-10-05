import BecknerOnofri.EntropyScalarCertificate.Bessel0292
import BecknerOnofri.EntropyScalarCertificate.Bessel0293
import BecknerOnofri.EntropyScalarCertificate.Bessel0635
import BecknerOnofri.EntropyScalarCertificate.Brackets0117
import BecknerOnofri.EntropyScalarCertificate.Logs0234
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1872
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (25807903392022088236094400165547350386543/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25807903392022088236094400165547350386543/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (12962092151689305937680664311825735159729/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12962092151689305937680664311825735159729/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (51732087695400700111455728789198820706001/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51732087695400700111455728789198820706001/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1872 BracketBatch0117.bracket1873 (51732087695400700111455728789198820706001/20000000000000000000000000000000000000000) (1072318892451142109009316201341382009417/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1872 BracketBatch0117.bracket1873
  (51732087695400700111455728789198820706001/20000000000000000000000000000000000000000) (1072318892451142109009316201341382009417/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1872
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1873
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (5184836860675722375072265724730294063891/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5184836860675722375072265724730294063891/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (13020816106575662483060258864332616521451/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13020816106575662483060258864332616521451/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (51965816516529936841481846352316703362357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51965816516529936841481846352316703362357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1873 BracketBatch0117.bracket1874 (51965816516529936841481846352316703362357/20000000000000000000000000000000000000000) (43093961198259287799413440197278114909/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1873 BracketBatch0117.bracket1874
  (51965816516529936841481846352316703362357/20000000000000000000000000000000000000000) (43093961198259287799413440197278114909/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1873
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1874
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (26041632213151324966120517728665233042899/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26041632213151324966120517728665233042899/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (26160264440253936582345277103867611214093/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26160264440253936582345277103867611214093/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1631309270418914423389556088516651383031/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1631309270418914423389556088516651383031/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1874 BracketBatch0117.bracket1875 (1631309270418914423389556088516651383031/625000000000000000000000000000000000000) (135301642185684479793774522610009846629/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1874 BracketBatch0117.bracket1875
  (1631309270418914423389556088516651383031/625000000000000000000000000000000000000) (135301642185684479793774522610009846629/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1874
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1875
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (2616026444025393658234527710386761121409/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2616026444025393658234527710386761121409/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (5256019728049882365066657400887558591227/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5256019728049882365066657400887558591227/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (2097614523220133936307142564332216166809/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2097614523220133936307142564332216166809/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1875 BracketBatch0117.bracket1876 (2097614523220133936307142564332216166809/800000000000000000000000000000000000000) (271877882836940224770950379352420246411/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1875 BracketBatch0117.bracket1876
  (2097614523220133936307142564332216166809/800000000000000000000000000000000000000) (271877882836940224770950379352420246411/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1875
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1876
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (6570024660062352956333321751109448239033/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6570024660062352956333321751109448239033/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (13200576406851366064789917294875053139069/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13200576406851366064789917294875053139069/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (5268125145395214395491312159418789923427/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5268125145395214395491312159418789923427/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1876 BracketBatch0117.bracket1877 (5268125145395214395491312159418789923427/2000000000000000000000000000000000000000) (546322265911764268843348893405806636059/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1876 BracketBatch0117.bracket1877
  (5268125145395214395491312159418789923427/2000000000000000000000000000000000000000) (546322265911764268843348893405806636059/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1876
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1877
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (5280230562740546425915966917950021255627/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5280230562740546425915966917950021255627/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (26523445314788587570111448227267067114551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26523445314788587570111448227267067114551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (26462299064245659849845641408508586696343/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26462299064245659849845641408508586696343/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1877 BracketBatch0117.bracket1878 (26462299064245659849845641408508586696343/10000000000000000000000000000000000000000) (1097812463243139878229707467257777833819/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1877 BracketBatch0117.bracket1878
  (26462299064245659849845641408508586696343/10000000000000000000000000000000000000000) (1097812463243139878229707467257777833819/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1877
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1878
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (6630861328697146892527862056816766778637/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6630861328697146892527862056816766778637/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (26646994860163067417912270805131607403783/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26646994860163067417912270805131607403783/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (53170440174951654988023719032398674518331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (53170440174951654988023719032398674518331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1878 BracketBatch0117.bracket1879 (53170440174951654988023719032398674518331/20000000000000000000000000000000000000000) (275753751596511201462715101369303663869/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1878 BracketBatch0117.bracket1879
  (53170440174951654988023719032398674518331/20000000000000000000000000000000000000000) (275753751596511201462715101369303663869/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1878
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1879
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1332349743008153370895613540256580370189/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1332349743008153370895613540256580370189/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0293.rows BesselBatch0293.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (6692955134527194345899663324057664679021/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6692955134527194345899663324057664679021/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (6677351924783980600188865512670283264983/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6677351924783980600188865512670283264983/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0234.rows ScalarLogs0234.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0117.bracket1879 BracketBatch0117.bracket1880 (6677351924783980600188865512670283264983/2500000000000000000000000000000000000000) (1108253082219210323659726875941143124719/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0117.bracket1879 BracketBatch0117.bracket1880
  (6677351924783980600188865512670283264983/2500000000000000000000000000000000000000) (1108253082219210323659726875941143124719/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1879
