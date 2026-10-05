import BecknerOnofri.EntropyScalarCertificate.Bessel0131
import BecknerOnofri.EntropyScalarCertificate.Bessel0132
import BecknerOnofri.EntropyScalarCertificate.Bessel0554
import BecknerOnofri.EntropyScalarCertificate.Bessel0555
import BecknerOnofri.EntropyScalarCertificate.Brackets0052
import BecknerOnofri.EntropyScalarCertificate.Brackets0053
import BecknerOnofri.EntropyScalarCertificate.Logs0105
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0840
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3402940902277179703644179171793349509227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3402940902277179703644179171793349509227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (85369058625538164388311270757279238983/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (85369058625538164388311270757279238983/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (6817703247298706279176630002084519068547/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6817703247298706279176630002084519068547/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0840 BracketBatch0052.bracket0841 (6817703247298706279176630002084519068547/20000000000000000000000000000000000000000) (1745752733669932055170001085769435373/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0840 BracketBatch0052.bracket0841
  (6817703247298706279176630002084519068547/20000000000000000000000000000000000000000) (1745752733669932055170001085769435373/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0840
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0841
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3414762345021526575532450830291169559317/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3414762345021526575532450830291169559317/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (214162312233258294899784730144275268273/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (214162312233258294899784730144275268273/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1368271868150731858785801302519914770337/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1368271868150731858785801302519914770337/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0841 BracketBatch0052.bracket0842 (1368271868150731858785801302519914770337/4000000000000000000000000000000000000000) (1768072937086625503329441263818974581/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0841 BracketBatch0052.bracket0842
  (1368271868150731858785801302519914770337/4000000000000000000000000000000000000000) (1768072937086625503329441263818974581/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0841
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0842
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (685319399146426543679311136461680858473/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (685319399146426543679311136461680858473/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1719222461284346194145238925724444157147/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1719222461284346194145238925724444157147/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (6865041918300825106687033533757292606659/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6865041918300825106687033533757292606659/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0842 BracketBatch0052.bracket0843 (6865041918300825106687033533757292606659/20000000000000000000000000000000000000000) (8953057041335004507787769794562383023/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0842 BracketBatch0052.bracket0843
  (6865041918300825106687033533757292606659/20000000000000000000000000000000000000000) (8953057041335004507787769794562383023/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0842
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0843
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (3438444922568692388290477851448888314291/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3438444922568692388290477851448888314291/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1725153097012340401300907292165406343959/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1725153097012340401300907292165406343959/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (6888751116593373190892292435779701002209/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6888751116593373190892292435779701002209/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0843 BracketBatch0052.bracket0844 (6888751116593373190892292435779701002209/20000000000000000000000000000000000000000) (362673933979515126098456372065443459/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0843 BracketBatch0052.bracket0844
  (6888751116593373190892292435779701002209/20000000000000000000000000000000000000000) (362673933979515126098456372065443459/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0843
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0844
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0131.rows BesselBatch0131.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (690061238804936160520362916866162537583/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (690061238804936160520362916866162537583/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (3462180878929943907456857559461326559083/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3462180878929943907456857559461326559083/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (3456243536477312355029336071896069623499/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3456243536477312355029336071896069623499/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0844 BracketBatch0052.bracket0845 (3456243536477312355029336071896069623499/10000000000000000000000000000000000000000) (229543656474868790333577382891979971/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0844 BracketBatch0052.bracket0845
  (3456243536477312355029336071896069623499/10000000000000000000000000000000000000000) (229543656474868790333577382891979971/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0844
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0845
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (86554521973248597686421438986533163977/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (86554521973248597686421438986533163977/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1737034523226655367280946533122414401177/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1737034523226655367280946533122414401177/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0554.rows BesselBatch0554.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (3468124962691627321009375312853077680717/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3468124962691627321009375312853077680717/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0845 BracketBatch0052.bracket0846 (3468124962691627321009375312853077680717/10000000000000000000000000000000000000000) (46488792273886952062298559746833329/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0845 BracketBatch0052.bracket0846
  (3468124962691627321009375312853077680717/10000000000000000000000000000000000000000) (46488792273886952062298559746833329/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0845
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0846
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (3474069046453310734561893066244828802351/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3474069046453310734561893066244828802351/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (3485970766105228591298513306014086896157/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3485970766105228591298513306014086896157/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (1740009953139634831465101593064728924627/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1740009953139634831465101593064728924627/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0846 BracketBatch0052.bracket0847 (1740009953139634831465101593064728924627/5000000000000000000000000000000000000000) (9414892657725838902128790067538523673/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0846 BracketBatch0052.bracket0847
  (1740009953139634831465101593064728924627/5000000000000000000000000000000000000000) (9414892657725838902128790067538523673/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0846
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0847
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1742985383052614295649256653007043448077/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1742985383052614295649256653007043448077/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0132.rows BesselBatch0132.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (3497886107740421330868145358733433746867/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3497886107740421330868145358733433746867/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0555.rows BesselBatch0555.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (6983856873845649922166658664747520643021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6983856873845649922166658664747520643021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0105.rows ScalarLogs0105.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0052.bracket0847 BracketBatch0053.bracket0848 (6983856873845649922166658664747520643021/20000000000000000000000000000000000000000) (9533156624849118141225097947906753197/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0052.bracket0847 BracketBatch0053.bracket0848
  (6983856873845649922166658664747520643021/20000000000000000000000000000000000000000) (9533156624849118141225097947906753197/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0847
