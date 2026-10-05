import BecknerOnofri.EntropyScalarCertificate.Bessel0252
import BecknerOnofri.EntropyScalarCertificate.Bessel0253
import BecknerOnofri.EntropyScalarCertificate.Bessel0615
import BecknerOnofri.EntropyScalarCertificate.Brackets0101
import BecknerOnofri.EntropyScalarCertificate.Logs0202
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1616
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (36759573775499134983212357425356330149/19531250000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (36759573775499134983212357425356330149/19531250000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (18832220964037564113925680206581242965569/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18832220964037564113925680206581242965569/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (37653122737093121225330407208363684001857/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37653122737093121225330407208363684001857/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1616 BracketBatch0101.bracket1617 (37653122737093121225330407208363684001857/20000000000000000000000000000000000000000) (740202643393345186416472225826796547411/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1616 BracketBatch0101.bracket1617
  (37653122737093121225330407208363684001857/20000000000000000000000000000000000000000) (740202643393345186416472225826796547411/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1616
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1617
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (9416110482018782056962840103290621482783/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9416110482018782056962840103290621482783/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (18843555799953350922577817178409409872551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18843555799953350922577817178409409872551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (37675776763990915036503497384990652838117/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37675776763990915036503497384990652838117/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1617 BracketBatch0101.bracket1618 (37675776763990915036503497384990652838117/20000000000000000000000000000000000000000) (74079950255207207713354128323972323227/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1617 BracketBatch0101.bracket1618
  (37675776763990915036503497384990652838117/20000000000000000000000000000000000000000) (74079950255207207713354128323972323227/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1617
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1618
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (4710888949988337730644454294602352468137/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4710888949988337730644454294602352468137/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (9427453157383218465731069725724780990929/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9427453157383218465731069725724780990929/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (18849231057359893927019978314929485927203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18849231057359893927019978314929485927203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1618 BracketBatch0101.bracket1619 (18849231057359893927019978314929485927203/10000000000000000000000000000000000000000) (148279403094992004097729610551830517227/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1618 BracketBatch0101.bracket1619
  (18849231057359893927019978314929485927203/10000000000000000000000000000000000000000) (148279403094992004097729610551830517227/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1618
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1619
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0252.rows BesselBatch0252.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (3770981262953287386292427890289912396371/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3770981262953287386292427890289912396371/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (235828406781676821162010939109779468649/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (235828406781676821162010939109779468649/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1508847154292023304976920583209276778951/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1508847154292023304976920583209276778951/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1619 BracketBatch0101.bracket1620 (1508847154292023304976920583209276778951/800000000000000000000000000000000000000) (370997591595927310253620267382818884187/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1619 BracketBatch0101.bracket1620
  (1508847154292023304976920583209276778951/800000000000000000000000000000000000000) (370997591595927310253620267382818884187/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1619
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1620
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (18866272542534145692960875128782357491917/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18866272542534145692960875128782357491917/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (18877654517407915778131436397494292437759/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18877654517407915778131436397494292437759/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (9435981764985515367773077881569162482419/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9435981764985515367773077881569162482419/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1620 BracketBatch0101.bracket1621 (9435981764985515367773077881569162482419/5000000000000000000000000000000000000000) (92824250841819770562214811205915769659/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1620 BracketBatch0101.bracket1621
  (9435981764985515367773077881569162482419/5000000000000000000000000000000000000000) (92824250841819770562214811205915769659/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1620
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1621
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (4719413629351978944532859099373573109439/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4719413629351978944532859099373573109439/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (295141441775525200961026141410770911047/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (295141441775525200961026141410770911047/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (9441676697760382159909277361945907686191/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9441676697760382159909277361945907686191/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1621 BracketBatch0101.bracket1622 (9441676697760382159909277361945907686191/5000000000000000000000000000000000000000) (371596743568416802554641260093793947973/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1621 BracketBatch0101.bracket1622
  (9441676697760382159909277361945907686191/5000000000000000000000000000000000000000) (371596743568416802554641260093793947973/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1621
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1622
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (3777810454726722572301134610057867661401/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3777810454726722572301134610057867661401/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2362558230693980379512495489867730154593/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2362558230693980379512495489867730154593/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (37789518119185455897605636969231179543749/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (37789518119185455897605636969231179543749/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1622 BracketBatch0101.bracket1623 (37789518119185455897605636969231179543749/20000000000000000000000000000000000000000) (148758725086881710510146390079199223251/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1622 BracketBatch0101.bracket1623
  (37789518119185455897605636969231179543749/20000000000000000000000000000000000000000) (148758725086881710510146390079199223251/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1622
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1623
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (18900465845551843036099963918941841236741/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18900465845551843036099963918941841236741/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0253.rows BesselBatch0253.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (18911895267598267364474813801233536906711/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18911895267598267364474813801233536906711/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0615.rows BesselBatch0615.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (9453090278287527600143694430043844535863/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9453090278287527600143694430043844535863/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0202.rows ScalarLogs0202.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0101.bracket1623 BracketBatch0101.bracket1624 (9453090278287527600143694430043844535863/5000000000000000000000000000000000000000) (744394422664979277021920295029366202123/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0101.bracket1623 BracketBatch0101.bracket1624
  (9453090278287527600143694430043844535863/5000000000000000000000000000000000000000) (744394422664979277021920295029366202123/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1623
