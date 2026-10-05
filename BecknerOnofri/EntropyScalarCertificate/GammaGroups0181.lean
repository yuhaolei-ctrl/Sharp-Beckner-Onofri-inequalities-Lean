import BecknerOnofri.EntropyScalarCertificate.Bessel0226
import BecknerOnofri.EntropyScalarCertificate.Bessel0227
import BecknerOnofri.EntropyScalarCertificate.Bessel0602
import BecknerOnofri.EntropyScalarCertificate.Brackets0090
import BecknerOnofri.EntropyScalarCertificate.Brackets0091
import BecknerOnofri.EntropyScalarCertificate.Logs0181
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1448
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3423389419412757948758254778204584464709/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3423389419412757948758254778204584464709/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (8563027020459621094152132311259183265021/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8563027020459621094152132311259183265021/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (34243001137983031932095538513541288853587/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34243001137983031932095538513541288853587/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1448 BracketBatch0090.bracket1449 (34243001137983031932095538513541288853587/20000000000000000000000000000000000000000) (162111395091111461800822710887106549511/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1448 BracketBatch0090.bracket1449
  (34243001137983031932095538513541288853587/20000000000000000000000000000000000000000) (162111395091111461800822710887106549511/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1448
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1449
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (17126054040919242188304264622518366530039/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17126054040919242188304264622518366530039/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (8567586020810664974642407184854689629651/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8567586020810664974642407184854689629651/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (34261226082540572137589078992227745789341/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34261226082540572137589078992227745789341/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1449 BracketBatch0090.bracket1450 (34261226082540572137589078992227745789341/20000000000000000000000000000000000000000) (162236444795572030791550168245920971489/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1449 BracketBatch0090.bracket1450
  (34261226082540572137589078992227745789341/20000000000000000000000000000000000000000) (162236444795572030791550168245920971489/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1449
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1450
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (17135172041621329949284814369709379259299/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17135172041621329949284814369709379259299/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (107151882006057950087211879988304833741/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (107151882006057950087211879988304833741/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (34279473162590601963238715167838152657859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34279473162590601963238715167838152657859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1450 BracketBatch0090.bracket1451 (34279473162590601963238715167838152657859/20000000000000000000000000000000000000000) (649446483624098235687385603941391786611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1450 BracketBatch0090.bracket1451
  (34279473162590601963238715167838152657859/20000000000000000000000000000000000000000) (649446483624098235687385603941391786611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1450
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1451
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (17144301120969272013953900798128773398557/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17144301120969272013953900798128773398557/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (4288360325204375962178525139678762464353/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4288360325204375962178525139678762464353/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (34297742421786775862668001356843823255969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34297742421786775862668001356843823255969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1451 BracketBatch0090.bracket1452 (34297742421786775862668001356843823255969/20000000000000000000000000000000000000000) (81243461805091638848535952028974628183/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1451 BracketBatch0090.bracket1452
  (34297742421786775862668001356843823255969/20000000000000000000000000000000000000000) (81243461805091638848535952028974628183/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1451
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1452
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0226.rows BesselBatch0226.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (17153441300817503848714100558715049857409/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17153441300817503848714100558715049857409/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (17162592603075844327898016382396544438789/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17162592603075844327898016382396544438789/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (17158016951946674088306058470555797148099/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17158016951946674088306058470555797148099/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1452 BracketBatch0090.bracket1453 (17158016951946674088306058470555797148099/10000000000000000000000000000000000000000) (650449412384451177457080918314319353993/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1452 BracketBatch0090.bracket1453
  (17158016951946674088306058470555797148099/10000000000000000000000000000000000000000) (650449412384451177457080918314319353993/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1452
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1453
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (8581296301537922163949008191198272219393/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8581296301537922163949008191198272219393/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (17171755049709663248577481162237246405323/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17171755049709663248577481162237246405323/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (34334347652785507576475497544633790844109/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34334347652785507576475497544633790844109/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1453 BracketBatch0090.bracket1454 (34334347652785507576475497544633790844109/20000000000000000000000000000000000000000) (325475819104457565497575626685562078917/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1453 BracketBatch0090.bracket1454
  (34334347652785507576475497544633790844109/20000000000000000000000000000000000000000) (325475819104457565497575626685562078917/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1453
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1454
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (429293876242741581214437029055931160133/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (429293876242741581214437029055931160133/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (17180928662740049433832132542718908849579/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17180928662740049433832132542718908849579/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (34352683712449712682409613704956155254899/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34352683712449712682409613704956155254899/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1454 BracketBatch0090.bracket1455 (34352683712449712682409613704956155254899/20000000000000000000000000000000000000000) (651454372669194701757066698780819938403/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1454 BracketBatch0090.bracket1455
  (34352683712449712682409613704956155254899/20000000000000000000000000000000000000000) (651454372669194701757066698780819938403/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1454
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1455
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (2147616082842506179229016567839863606197/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2147616082842506179229016567839863606197/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0227.rows BesselBatch0227.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (17190113464243979426887622047223021816351/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17190113464243979426887622047223021816351/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0602.rows BesselBatch0602.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (34371042126984028860719754589941930665927/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34371042126984028860719754589941930665927/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0181.rows ScalarLogs0181.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0090.bracket1455 BracketBatch0091.bracket1456 (34371042126984028860719754589941930665927/20000000000000000000000000000000000000000) (4074735103261058933113516394011164729/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0090.bracket1455 BracketBatch0091.bracket1456
  (34371042126984028860719754589941930665927/20000000000000000000000000000000000000000) (4074735103261058933113516394011164729/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1455
