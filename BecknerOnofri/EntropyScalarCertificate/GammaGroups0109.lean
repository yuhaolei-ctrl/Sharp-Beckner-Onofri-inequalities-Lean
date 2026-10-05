import BecknerOnofri.EntropyScalarCertificate.Bessel0136
import BecknerOnofri.EntropyScalarCertificate.Bessel0137
import BecknerOnofri.EntropyScalarCertificate.Bessel0557
import BecknerOnofri.EntropyScalarCertificate.Brackets0054
import BecknerOnofri.EntropyScalarCertificate.Brackets0055
import BecknerOnofri.EntropyScalarCertificate.Logs0109
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0872
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (3788128839048307223084384749418485751599/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3788128839048307223084384749418485751599/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (3800408497383299645508869737206576123631/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3800408497383299645508869737206576123631/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (758853733643160686859325448662506187523/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (758853733643160686859325448662506187523/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0872 BracketBatch0054.bracket0873 (758853733643160686859325448662506187523/2000000000000000000000000000000000000000) (3220094143822775230468904627921567899/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0872 BracketBatch0054.bracket0873
  (758853733643160686859325448662506187523/2000000000000000000000000000000000000000) (3220094143822775230468904627921567899/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0872
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0873
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (950102124345824911377217434301644030907/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (950102124345824911377217434301644030907/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1906351862029815516039598567582433241461/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1906351862029815516039598567582433241461/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (152262244428858613551761337447428852131/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (152262244428858613551761337447428852131/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0873 BracketBatch0054.bracket0874 (152262244428858613551761337447428852131/400000000000000000000000000000000000000) (13030859203076009604607989084670455963/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0873 BracketBatch0054.bracket0874
  (152262244428858613551761337447428852131/400000000000000000000000000000000000000) (13030859203076009604607989084670455963/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0873
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0874
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (3812703724059631032079197135164866482919/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3812703724059631032079197135164866482919/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (3825014599323961878744793307719718879837/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3825014599323961878744793307719718879837/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (1909429580845898227705997610721146340689/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1909429580845898227705997610721146340689/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0874 BracketBatch0054.bracket0875 (1909429580845898227705997610721146340689/5000000000000000000000000000000000000000) (6591347636141397076502602964895510783/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0874 BracketBatch0054.bracket0875
  (1909429580845898227705997610721146340689/5000000000000000000000000000000000000000) (6591347636141397076502602964895510783/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0874
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0875
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1912507299661980939372396653859859439917/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1912507299661980939372396653859859439917/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1918670601926067980727271213318308103569/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1918670601926067980727271213318308103569/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (1915588950794024460049833933589083771743/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1915588950794024460049833933589083771743/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0875 BracketBatch0054.bracket0876 (1915588950794024460049833933589083771743/5000000000000000000000000000000000000000) (666794680880392645908537121803867673/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0875 BracketBatch0054.bracket0876
  (1915588950794024460049833933589083771743/5000000000000000000000000000000000000000) (666794680880392645908537121803867673/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0875
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0876
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (767468240770427192290908485327323241427/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (767468240770427192290908485327323241427/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (3849683618752630302995007654628539437609/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3849683618752630302995007654628539437609/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (960878102825595783056193760158144455593/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (960878102825595783056193760158144455593/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0876 BracketBatch0054.bracket0877 (960878102825595783056193760158144455593/2500000000000000000000000000000000000000) (843153944675348189858498422923158513/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0876 BracketBatch0054.bracket0877
  (960878102825595783056193760158144455593/2500000000000000000000000000000000000000) (843153944675348189858498422923158513/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0876
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0877
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1924841809376315151497503827314269718803/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1924841809376315151497503827314269718803/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (482755240696254655011580034175756406877/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (482755240696254655011580034175756406877/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (3855862772161333771543823964017295346311/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3855862772161333771543823964017295346311/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0877 BracketBatch0054.bracket0878 (3855862772161333771543823964017295346311/10000000000000000000000000000000000000000) (13646412680880334952013818041334725889/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0877 BracketBatch0054.bracket0878
  (3855862772161333771543823964017295346311/10000000000000000000000000000000000000000) (13646412680880334952013818041334725889/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0877
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0878
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (3862041925570037240092640273406051255013/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3862041925570037240092640273406051255013/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (3874416206288578954141335403582917179947/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3874416206288578954141335403582917179947/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (96705726648232702427924695962362105437/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (96705726648232702427924695962362105437/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0878 BracketBatch0054.bracket0879 (96705726648232702427924695962362105437/250000000000000000000000000000000000000) (13803751274280147828731414142618581029/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0878 BracketBatch0054.bracket0879
  (96705726648232702427924695962362105437/250000000000000000000000000000000000000) (13803751274280147828731414142618581029/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0878
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0879
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (484302025786072369267666925447864647493/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (484302025786072369267666925447864647493/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0137.rows BesselBatch0137.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (7773613086671309667215602229097465461/20000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7773613086671309667215602229097465461/20000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (1940305687406058446937284129532912477611/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1940305687406058446937284129532912477611/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0109.rows ScalarLogs0109.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0879 BracketBatch0055.bracket0880 (1940305687406058446937284129532912477611/5000000000000000000000000000000000000000) (3490621973772965586926543806441581129/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0879 BracketBatch0055.bracket0880
  (1940305687406058446937284129532912477611/5000000000000000000000000000000000000000) (3490621973772965586926543806441581129/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0879
