import BecknerOnofri.EntropyScalarCertificate.Bessel0406
import BecknerOnofri.EntropyScalarCertificate.Bessel0407
import BecknerOnofri.EntropyScalarCertificate.Bessel0692
import BecknerOnofri.EntropyScalarCertificate.Brackets0162
import BecknerOnofri.EntropyScalarCertificate.Brackets0163
import BecknerOnofri.EntropyScalarCertificate.Logs0325
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2600
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (450900860742963214247628011527819976326057/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (450900860742963214247628011527819976326057/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (7070688629772114858582456976318573475341/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7070688629772114858582456976318573475341/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (903424933048378565196905258012208678747881/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (903424933048378565196905258012208678747881/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2600 BracketBatch0162.bracket2601 (903424933048378565196905258012208678747881/20000000000000000000000000000000000000000) (305810416789626962279481780790418885701/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2600 BracketBatch0162.bracket2601
  (903424933048378565196905258012208678747881/20000000000000000000000000000000000000000) (305810416789626962279481780790418885701/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2600
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2601
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (452524072305415350949277246484388702421821/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (452524072305415350949277246484388702421821/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (227079523277004466849001857435179179086367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (227079523277004466849001857435179179086367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (181336623771884856929456192270949412118911/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (181336623771884856929456192270949412118911/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2601 BracketBatch0162.bracket2602 (181336623771884856929456192270949412118911/4000000000000000000000000000000000000000) (97965077555819054669139897674697713943/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2601 BracketBatch0162.bracket2602
  (181336623771884856929456192270949412118911/4000000000000000000000000000000000000000) (97965077555819054669139897674697713943/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2601
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2602
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (454159046554008933698003714870358358172731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (454159046554008933698003714870358358172731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (227902955904455956250996893884936890877889/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (227902955904455956250996893884936890877889/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (909964958362920846199997502640232139928509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (909964958362920846199997502640232139928509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2602 BracketBatch0162.bracket2603 (909964958362920846199997502640232139928509/20000000000000000000000000000000000000000) (2451780299524101370079376577865807950057/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2602 BracketBatch0162.bracket2603
  (909964958362920846199997502640232139928509/20000000000000000000000000000000000000000) (2451780299524101370079376577865807950057/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2602
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2603
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (18232236472356476500079751510794951270231/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18232236472356476500079751510794951270231/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (228732399131789687359581983631617767252781/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (228732399131789687359581983631617767252781/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (913270710072491287221157755033109316261337/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (913270710072491287221157755033109316261337/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2603 BracketBatch0162.bracket2604 (913270710072491287221157755033109316261337/20000000000000000000000000000000000000000) (4908886948718495862345540101260208140669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2603 BracketBatch0162.bracket2604
  (913270710072491287221157755033109316261337/20000000000000000000000000000000000000000) (4908886948718495862345540101260208140669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2603
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2604
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0406.rows BesselBatch0406.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (457464798263579374719163967263235534505559/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (457464798263579374719163967263235534505559/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (459135838019062833279588226648779338574847/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (459135838019062833279588226648779338574847/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (458300318141321103999376096956007436540203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (458300318141321103999376096956007436540203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2604 BracketBatch0162.bracket2605 (458300318141321103999376096956007436540203/10000000000000000000000000000000000000000) (4914233054344202382196948845126069350777/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2604 BracketBatch0162.bracket2605
  (458300318141321103999376096956007436540203/10000000000000000000000000000000000000000) (4914233054344202382196948845126069350777/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2604
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2605
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (114783959504765708319897056662194834643711/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (114783959504765708319897056662194834643711/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (230409582559538168721124753515505462703469/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (230409582559538168721124753515505462703469/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (459977501569069585360918866839895131990891/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (459977501569069585360918866839895131990891/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2605 BracketBatch0162.bracket2606 (459977501569069585360918866839895131990891/10000000000000000000000000000000000000000) (4919599069736696824312124203599439196267/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2605 BracketBatch0162.bracket2606
  (459977501569069585360918866839895131990891/10000000000000000000000000000000000000000) (4919599069736696824312124203599439196267/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2605
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2606
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (92163833023815267488449901406202185081387/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (92163833023815267488449901406202185081387/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (231257457792919477503833086101114893161847/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (231257457792919477503833086101114893161847/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (923334080704915292449915679233240711730629/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (923334080704915292449915679233240711730629/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2606 BracketBatch0162.bracket2607 (923334080704915292449915679233240711730629/20000000000000000000000000000000000000000) (2462492565076700822427298492665702290691/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2606 BracketBatch0162.bracket2607
  (923334080704915292449915679233240711730629/20000000000000000000000000000000000000000) (2462492565076700822427298492665702290691/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2606
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2607
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (462514915585838955007666172202229786323691/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (462514915585838955007666172202229786323691/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (58027903432089219266906179087556313517969/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58027903432089219266906179087556313517969/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (926738143042552709142915604902680294467443/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (926738143042552709142915604902680294467443/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0325.rows ScalarLogs0325.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0162.bracket2607 BracketBatch0163.bracket2608 (926738143042552709142915604902680294467443/20000000000000000000000000000000000000000) (4930391372137209454941144101536683687083/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0162.bracket2607 BracketBatch0163.bracket2608
  (926738143042552709142915604902680294467443/20000000000000000000000000000000000000000) (4930391372137209454941144101536683687083/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2607
