module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0446
public import BecknerOnofri.EntropyScalarCertificate.Bessel0447
public import BecknerOnofri.EntropyScalarCertificate.Bessel0712
public import BecknerOnofri.EntropyScalarCertificate.Brackets0178
public import BecknerOnofri.EntropyScalarCertificate.Brackets0179
public import BecknerOnofri.EntropyScalarCertificate.Logs0357
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2856
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (530288242618234170575427564725095909000673/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (530288242618234170575427564725095909000673/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (1062825567116579497642722455390018421225339/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1062825567116579497642722455390018421225339/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (424680410470609567758715516968042047845337/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (424680410470609567758715516968042047845337/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2856 BracketBatch0178.bracket2857 (424680410470609567758715516968042047845337/4000000000000000000000000000000000000000) (3102018506110707597157920553617473190567/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2856 BracketBatch0178.bracket2857
  (424680410470609567758715516968042047845337/4000000000000000000000000000000000000000) (3102018506110707597157920553617473190567/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2856
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2857
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (132853195889572437205340306923752302653167/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (132853195889572437205340306923752302653167/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (266271054899623344237336866310635023740619/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266271054899623344237336866310635023740619/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (531977446678768218648017480158139629046953/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (531977446678768218648017480158139629046953/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2857 BracketBatch0178.bracket2858 (531977446678768218648017480158139629046953/5000000000000000000000000000000000000000) (3103649595285220976754942789959322709559/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2857 BracketBatch0178.bracket2858
  (531977446678768218648017480158139629046953/5000000000000000000000000000000000000000) (3103649595285220976754942789959322709559/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2857
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2858
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (1065084219598493376949347465242540094962473/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1065084219598493376949347465242540094962473/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (266838125975352430712020363534655225360003/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266838125975352430712020363534655225360003/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (426487344699980619959485783876232199280497/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (426487344699980619959485783876232199280497/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2858 BracketBatch0178.bracket2859 (426487344699980619959485783876232199280497/4000000000000000000000000000000000000000) (6210568350394559021374607068282202345571/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2858 BracketBatch0178.bracket2859
  (426487344699980619959485783876232199280497/4000000000000000000000000000000000000000) (6210568350394559021374607068282202345571/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2858
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2859
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1067352503901409722848081454138620901440009/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1067352503901409722848081454138620901440009/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (534815240883884651342636991681947330731611/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (534815240883884651342636991681947330731611/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (2136982985669179025533355437502515562903231/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2136982985669179025533355437502515562903231/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2859 BracketBatch0178.bracket2860 (2136982985669179025533355437502515562903231/20000000000000000000000000000000000000000) (1553461130013321670968618251794019324259/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2859 BracketBatch0178.bracket2860
  (2136982985669179025533355437502515562903231/20000000000000000000000000000000000000000) (1553461130013321670968618251794019324259/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2859
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2860
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0446.rows BesselBatch0446.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (1069630481767769302685273983363894661463219/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1069630481767769302685273983363894661463219/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (33497444233401751864464495772864073447223/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (33497444233401751864464495772864073447223/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (428309739447325072469627569619109002354871/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (428309739447325072469627569619109002354871/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2860 BracketBatch0178.bracket2861 (428309739447325072469627569619109002354871/4000000000000000000000000000000000000000) (1554281932018077916775143031051393465521/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2860 BracketBatch0178.bracket2861
  (428309739447325072469627569619109002354871/4000000000000000000000000000000000000000) (1554281932018077916775143031051393465521/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2860
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2861
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (1071918215468856059662863864731650350311133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1071918215468856059662863864731650350311133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (134276970976308924480138314050396717292881/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (134276970976308924480138314050396717292881/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (2146133983279327455503970377134824088654181/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2146133983279327455503970377134824088654181/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2861 BracketBatch0178.bracket2862 (2146133983279327455503970377134824088654181/20000000000000000000000000000000000000000) (3110209001572356051114121798505644401557/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2861 BracketBatch0178.bracket2862
  (2146133983279327455503970377134824088654181/20000000000000000000000000000000000000000) (3110209001572356051114121798505644401557/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2861
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2862
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (214843153562094279168221302480634747668609/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (214843153562094279168221302480634747668609/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (269130800534670417924043799717265884555103/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (269130800534670417924043799717265884555103/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (2150738969949153067537281711272237276563457/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2150738969949153067537281711272237276563457/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2862 BracketBatch0178.bracket2863 (2150738969949153067537281711272237276563457/20000000000000000000000000000000000000000) (6223715374132192701800289613230162397041/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2862 BracketBatch0178.bracket2863
  (2150738969949153067537281711272237276563457/20000000000000000000000000000000000000000) (6223715374132192701800289613230162397041/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2862
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2863
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (1076523202138681671696175198869063538220409/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1076523202138681671696175198869063538220409/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0447.rows BesselBatch0447.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (1078840582345640026792731295541480547072699/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1078840582345640026792731295541480547072699/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0712.rows BesselBatch0712.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (538840946121080424622226623602636021323277/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (538840946121080424622226623602636021323277/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0357.rows ScalarLogs0357.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0178.bracket2863 BracketBatch0179.bracket2864 (538840946121080424622226623602636021323277/5000000000000000000000000000000000000000) (622701987006633022935072105544072735957/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0178.bracket2863 BracketBatch0179.bracket2864
  (538840946121080424622226623602636021323277/5000000000000000000000000000000000000000) (622701987006633022935072105544072735957/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2863
