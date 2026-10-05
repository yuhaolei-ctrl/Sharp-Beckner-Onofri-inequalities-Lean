import BecknerOnofri.EntropyScalarCertificate.Bessel0007
import BecknerOnofri.EntropyScalarCertificate.Bessel0008
import BecknerOnofri.EntropyScalarCertificate.Bessel0492
import BecknerOnofri.EntropyScalarCertificate.Bessel0493
import BecknerOnofri.EntropyScalarCertificate.Brackets0003
import BecknerOnofri.EntropyScalarCertificate.Logs0006
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0048
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (8280616294094982660920925089868679131/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8280616294094982660920925089868679131/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (166115632837784501109600508485980068059/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (166115632837784501109600508485980068059/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (331727958719684154328019010283353650679/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (331727958719684154328019010283353650679/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0048 BracketBatch0003.bracket0049 (331727958719684154328019010283353650679/5000000000000000000000000000000000000000) (2898483978426119642712910624019761/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0048 BracketBatch0003.bracket0049
  (331727958719684154328019010283353650679/5000000000000000000000000000000000000000) (2898483978426119642712910624019761/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0048
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0049
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (664462531351138004438402033943920272233/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (664462531351138004438402033943920272233/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (333237919857356659657262147865604973477/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (333237919857356659657262147865604973477/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (1330938371065851323752926329675130219187/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1330938371065851323752926329675130219187/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0049 BracketBatch0003.bracket0050 (1330938371065851323752926329675130219187/20000000000000000000000000000000000000000) (14673677708131381742818043157649557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0049 BracketBatch0003.bracket0050
  (1330938371065851323752926329675130219187/20000000000000000000000000000000000000000) (14673677708131381742818043157649557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0049
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0050
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (666475839714713319314524295731209946951/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (666475839714713319314524295731209946951/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (334244614433636576597007913530303232309/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (334244614433636576597007913530303232309/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1334965068581986472508540122791816411569/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1334965068581986472508540122791816411569/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0050 BracketBatch0003.bracket0051 (1334965068581986472508540122791816411569/20000000000000000000000000000000000000000) (18570733102417483613171591979711/12500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0050 BracketBatch0003.bracket0051
  (1334965068581986472508540122791816411569/20000000000000000000000000000000000000000) (18570733102417483613171591979711/12500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0050
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0051
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0007.rows BesselBatch0007.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (133697845773454630638803165412121292923/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (133697845773454630638803165412121292923/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (41906418691113805723954498827846477579/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41906418691113805723954498827846477579/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1338991927925094044777287808306150105879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1338991927925094044777287808306150105879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0051 BracketBatch0003.bracket0052 (1338991927925094044777287808306150105879/20000000000000000000000000000000000000000) (15041156234420121654685381745782559/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0051 BracketBatch0003.bracket0052
  (1338991927925094044777287808306150105879/20000000000000000000000000000000000000000) (15041156234420121654685381745782559/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0051
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0052
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (670502699057820891583271981245543641261/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (670502699057820891583271981245543641261/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (134503250107082976869204533859875443891/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (134503250107082976869204533859875443891/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0492.rows BesselBatch0492.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (335754737398308943982323662636230215179/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (335754737398308943982323662636230215179/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0052 BracketBatch0003.bracket0053 (335754737398308943982323662636230215179/5000000000000000000000000000000000000000) (3806849254298514078551795857133133/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0052 BracketBatch0003.bracket0053
  (335754737398308943982323662636230215179/5000000000000000000000000000000000000000) (3806849254298514078551795857133133/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0052
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0053
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (168129062633853721086505667324844304863/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (168129062633853721086505667324844304863/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (67452988354916862033608882743831683279/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (67452988354916862033608882743831683279/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (673523067042291752341055748368847026121/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (673523067042291752341055748368847026121/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0053 BracketBatch0003.bracket0054 (673523067042291752341055748368847026121/10000000000000000000000000000000000000000) (15415318912587521276212618344431741/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0053 BracketBatch0003.bracket0054
  (673523067042291752341055748368847026121/10000000000000000000000000000000000000000) (15415318912587521276212618344431741/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0053
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0054
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (674529883549168620336088827438316832787/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (674529883549168620336088827438316832787/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (42283974896765681382517463578848813359/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (42283974896765681382517463578848813359/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (1351073481897419522456368244699897846531/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1351073481897419522456368244699897846531/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0054 BracketBatch0003.bracket0055 (1351073481897419522456368244699897846531/20000000000000000000000000000000000000000) (3901233008416155084664766688627613/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0054 BracketBatch0003.bracket0055
  (1351073481897419522456368244699897846531/20000000000000000000000000000000000000000) (3901233008416155084664766688627613/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0054
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0055
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (676543598348250902120279417261581013741/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (676543598348250902120279417261581013741/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0008.rows BesselBatch0008.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (678557395181886020791727531207948886821/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (678557395181886020791727531207948886821/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0493.rows BesselBatch0493.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (677550496765068461456003474234764950281/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (677550496765068461456003474234764950281/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0006.rows ScalarLogs0006.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0003.bracket0055 BracketBatch0003.bracket0056 (677550496765068461456003474234764950281/10000000000000000000000000000000000000000) (15796246524226759375027355582535609/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0003.bracket0055 BracketBatch0003.bracket0056
  (677550496765068461456003474234764950281/10000000000000000000000000000000000000000) (15796246524226759375027355582535609/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0055
