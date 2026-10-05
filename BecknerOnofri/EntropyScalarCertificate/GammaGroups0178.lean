import BecknerOnofri.EntropyScalarCertificate.Bessel0222
import BecknerOnofri.EntropyScalarCertificate.Bessel0223
import BecknerOnofri.EntropyScalarCertificate.Bessel0600
import BecknerOnofri.EntropyScalarCertificate.Brackets0089
import BecknerOnofri.EntropyScalarCertificate.Logs0178
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1424
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1690164177347120921969063732344967917529/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1690164177347120921969063732344967917529/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (16910489752083381988785059954538296015273/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16910489752083381988785059954538296015273/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (33812131525554591208475697277987975190563/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33812131525554591208475697277987975190563/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1424 BracketBatch0089.bracket1425 (33812131525554591208475697277987975190563/20000000000000000000000000000000000000000) (318295284012951951564553531355561867431/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1424 BracketBatch0089.bracket1425
  (33812131525554591208475697277987975190563/20000000000000000000000000000000000000000) (318295284012951951564553531355561867431/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1424
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1425
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1691048975208338198878505995453829601527/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1691048975208338198878505995453829601527/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (16919348280501918431553978619664440522977/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16919348280501918431553978619664440522977/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (33829838032585300420339038574202736538247/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33829838032585300420339038574202736538247/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1425 BracketBatch0089.bracket1426 (33829838032585300420339038574202736538247/20000000000000000000000000000000000000000) (127415770705932274862981012863096050067/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1425 BracketBatch0089.bracket1426
  (33829838032585300420339038574202736538247/20000000000000000000000000000000000000000) (127415770705932274862981012863096050067/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1425
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1426
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (8459674140250959215776989309832220261487/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8459674140250959215776989309832220261487/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (16928217379249437881040064121125839934211/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16928217379249437881040064121125839934211/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (6769513131950271262518808548158056091437/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6769513131950271262518808548158056091437/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1426 BracketBatch0089.bracket1427 (6769513131950271262518808548158056091437/4000000000000000000000000000000000000000) (637567627050179958030905034908871279979/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1426 BracketBatch0089.bracket1427
  (6769513131950271262518808548158056091437/4000000000000000000000000000000000000000) (637567627050179958030905034908871279979/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1426
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1427
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0222.rows BesselBatch0222.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (66125849137693116722812750473147812243/39062500000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (66125849137693116722812750473147812243/39062500000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (8468548534449969819876589785857295649809/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8468548534449969819876589785857295649809/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (16932657224074688760396621846420215616913/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16932657224074688760396621846420215616913/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1427 BracketBatch0089.bracket1428 (16932657224074688760396621846420215616913/10000000000000000000000000000000000000000) (127611377861099145772071584779441310691/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1427 BracketBatch0089.bracket1428
  (16932657224074688760396621846420215616913/10000000000000000000000000000000000000000) (127611377861099145772071584779441310691/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1427
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1428
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (3387419413779987927950635914342918259923/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3387419413779987927950635914342918259923/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (8472993685039478266671300133757215395397/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8472993685039478266671300133757215395397/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (33883084438978896173095779839229022090409/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33883084438978896173095779839229022090409/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1428 BracketBatch0089.bracket1429 (33883084438978896173095779839229022090409/20000000000000000000000000000000000000000) (638546641014981526953661954298692579719/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1428 BracketBatch0089.bracket1429
  (33883084438978896173095779839229022090409/20000000000000000000000000000000000000000) (638546641014981526953661954298692579719/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1428
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1429
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (16945987370078956533342600267514430790791/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16945987370078956533342600267514430790791/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (16954888303463708996096162909941299118853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16954888303463708996096162909941299118853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (8475218918385666382359690794363932477411/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8475218918385666382359690794363932477411/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1429 BracketBatch0089.bracket1430 (8475218918385666382359690794363932477411/5000000000000000000000000000000000000000) (639036882899349595935265172766887421377/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1429 BracketBatch0089.bracket1430
  (8475218918385666382359690794363932477411/5000000000000000000000000000000000000000) (639036882899349595935265172766887421377/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1429
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1430
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (339097766069274179921923258198825982377/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (339097766069274179921923258198825982377/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3392759977956651938080814938554590766873/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3392759977956651938080814938554590766873/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (6783737638649393737300047520542850590643/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6783737638649393737300047520542850590643/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1430 BracketBatch0089.bracket1431 (6783737638649393737300047520542850590643/4000000000000000000000000000000000000000) (12790552313613084517829199970174865719/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1430 BracketBatch0089.bracket1431
  (6783737638649393737300047520542850590643/4000000000000000000000000000000000000000) (12790552313613084517829199970174865719/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1430
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1431
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (8481899944891629845202037346386476917181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8481899944891629845202037346386476917181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0223.rows BesselBatch0223.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (16972722149818668662335283151145070852159/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16972722149818668662335283151145070852159/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0600.rows BesselBatch0600.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (33936522039601928352739357843918024686521/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33936522039601928352739357843918024686521/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0178.rows ScalarLogs0178.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0089.bracket1431 BracketBatch0089.bracket1432 (33936522039601928352739357843918024686521/20000000000000000000000000000000000000000) (160004710020573600362790514442614992611/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0089.bracket1431 BracketBatch0089.bracket1432
  (33936522039601928352739357843918024686521/20000000000000000000000000000000000000000) (160004710020573600362790514442614992611/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1431
