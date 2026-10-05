import BecknerOnofri.EntropyScalarCertificate.Bessel0092
import BecknerOnofri.EntropyScalarCertificate.Bessel0093
import BecknerOnofri.EntropyScalarCertificate.Bessel0535
import BecknerOnofri.EntropyScalarCertificate.Brackets0037
import BecknerOnofri.EntropyScalarCertificate.Logs0074
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0592
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1776453335912185456764213585824456365637/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1776453335912185456764213585824456365637/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (889274642258500875968453068272738197473/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (889274642258500875968453068272738197473/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (3555002620429187208701119722369932760583/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3555002620429187208701119722369932760583/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0592 BracketBatch0037.bracket0593 (3555002620429187208701119722369932760583/20000000000000000000000000000000000000000) (184417804644703016260549072473779681/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0592 BracketBatch0037.bracket0593
  (3555002620429187208701119722369932760583/20000000000000000000000000000000000000000) (184417804644703016260549072473779681/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0592
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0593
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1778549284517001751936906136545476394943/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1778549284517001751936906136545476394943/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (445161365573076114145272808724576777343/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (445161365573076114145272808724576777343/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (711838949361861241703599474288756700863/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (711838949361861241703599474288756700863/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0593 BracketBatch0037.bracket0594 (711838949361861241703599474288756700863/4000000000000000000000000000000000000000) (741074326555337245212508384312452189/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0593 BracketBatch0037.bracket0594
  (711838949361861241703599474288756700863/4000000000000000000000000000000000000000) (741074326555337245212508384312452189/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0593
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0594
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1780645462292304456581091234898307109369/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1780645462292304456581091234898307109369/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (1782741869546242885888042687084145632723/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1782741869546242885888042687084145632723/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (890846832959636835617283480495613185523/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (890846832959636835617283480495613185523/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0594 BracketBatch0037.bracket0595 (890846832959636835617283480495613185523/5000000000000000000000000000000000000000) (744489263638712204803628909826533323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0594 BracketBatch0037.bracket0595
  (890846832959636835617283480495613185523/5000000000000000000000000000000000000000) (744489263638712204803628909826533323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0594
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0595
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0092.rows BesselBatch0092.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (22284273369328036073600533588551820409/125000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22284273369328036073600533588551820409/125000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (1784838506587138719003946131794566787113/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1784838506587138719003946131794566787113/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (3567580376133381604891988818878712419833/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3567580376133381604891988818878712419833/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0595 BracketBatch0037.bracket0596 (3567580376133381604891988818878712419833/20000000000000000000000000000000000000000) (747916057728551131360732876442684851/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0595 BracketBatch0037.bracket0596
  (3567580376133381604891988818878712419833/20000000000000000000000000000000000000000) (747916057728551131360732876442684851/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0595
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0596
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (178483850658713871900394613179456678711/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (178483850658713871900394613179456678711/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (893467686861743138871768628679974847507/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (893467686861743138871768628679974847507/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (892943470077656249186870847288629120531/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (892943470077656249186870847288629120531/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0596 BracketBatch0037.bracket0597 (892943470077656249186870847288629120531/5000000000000000000000000000000000000000) (751354736760389409243593139523129023/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0596 BracketBatch0037.bracket0597
  (892943470077656249186870847288629120531/5000000000000000000000000000000000000000) (751354736760389409243593139523129023/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0596
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0597
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1786935373723486277743537257359949695011/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1786935373723486277743537257359949695011/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1789032471263952805627356942468753594757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1789032471263952805627356942468753594757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (446995980623429885421361774978587911221/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (446995980623429885421361774978587911221/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0597 BracketBatch0037.bracket0598 (446995980623429885421361774978587911221/2500000000000000000000000000000000000000) (23587666522053079168522673854753219/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0597 BracketBatch0037.bracket0598
  (446995980623429885421361774978587911221/2500000000000000000000000000000000000000) (23587666522053079168522673854753219/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0597
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0598
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (894516235631976402813678471234376797377/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (894516235631976402813678471234376797377/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (223891224939672343405407724506964279701/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (223891224939672343405407724506964279701/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (1790081135390665776435309369262233916181/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1790081135390665776435309369262233916181/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0598 BracketBatch0037.bracket0599 (1790081135390665776435309369262233916181/10000000000000000000000000000000000000000) (75826786157190104603471699958804871/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0598 BracketBatch0037.bracket0599
  (1790081135390665776435309369262233916181/10000000000000000000000000000000000000000) (75826786157190104603471699958804871/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0598
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0599
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (358225959903475749448652359211142847521/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (358225959903475749448652359211142847521/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0093.rows BesselBatch0093.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1793227358792778027932829711354822861953/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1793227358792778027932829711354822861953/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0535.rows BesselBatch0535.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (1792178579155078387588045753705268549779/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1792178579155078387588045753705268549779/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0074.rows ScalarLogs0074.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0037.bracket0599 BracketBatch0037.bracket0600 (1792178579155078387588045753705268549779/10000000000000000000000000000000000000000) (761742363402385496350173982751554347/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0037.bracket0599 BracketBatch0037.bracket0600
  (1792178579155078387588045753705268549779/10000000000000000000000000000000000000000) (761742363402385496350173982751554347/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0599
