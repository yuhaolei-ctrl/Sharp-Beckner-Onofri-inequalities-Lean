module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0271
public import BecknerOnofri.EntropyScalarCertificate.Bessel0272
public import BecknerOnofri.EntropyScalarCertificate.Bessel0624
public import BecknerOnofri.EntropyScalarCertificate.Bessel0625
public import BecknerOnofri.EntropyScalarCertificate.Brackets0108
public import BecknerOnofri.EntropyScalarCertificate.Brackets0109
public import BecknerOnofri.EntropyScalarCertificate.Logs0217
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1736
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (20301282484975882939364812733133784127079/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20301282484975882939364812733133784127079/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (20314750721807725715760773835300928281069/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20314750721807725715760773835300928281069/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (10154008301695902163781396642108678102037/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10154008301695902163781396642108678102037/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1736 BracketBatch0108.bracket1737 (10154008301695902163781396642108678102037/5000000000000000000000000000000000000000) (408399854250074021327330861961200176343/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1736 BracketBatch0108.bracket1737
  (10154008301695902163781396642108678102037/5000000000000000000000000000000000000000) (408399854250074021327330861961200176343/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1736
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1737
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (10157375360903862857880386917650464140533/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10157375360903862857880386917650464140533/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (20328239447559261246680336550815480408719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20328239447559261246680336550815480408719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (8128598033873397392488222077223281737957/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8128598033873397392488222077223281737957/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1737 BracketBatch0108.bracket1738 (8128598033873397392488222077223281737957/4000000000000000000000000000000000000000) (408741478341500273257097710682845827161/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1737 BracketBatch0108.bracket1738
  (8128598033873397392488222077223281737957/4000000000000000000000000000000000000000) (408741478341500273257097710682845827161/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1737
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1738
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (5082059861889815311670084137703870102179/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5082059861889815311670084137703870102179/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2034174871006882113675019517131877875549/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2034174871006882113675019517131877875549/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (20334994078814041191715265861067129582103/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20334994078814041191715265861067129582103/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1738 BracketBatch0108.bracket1739 (20334994078814041191715265861067129582103/10000000000000000000000000000000000000000) (818166997395259205319172439439050677597/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1738 BracketBatch0108.bracket1739
  (20334994078814041191715265861067129582103/10000000000000000000000000000000000000000) (818166997395259205319172439439050677597/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1738
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1739
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (20341748710068821136750195171318778755487/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20341748710068821136750195171318778755487/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (20355278557316537490473541549906914518007/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20355278557316537490473541549906914518007/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (20348513633692679313611868360612846636747/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20348513633692679313611868360612846636747/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1739 BracketBatch0108.bracket1740 (20348513633692679313611868360612846636747/10000000000000000000000000000000000000000) (818851831933374331902420126854020967439/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1739 BracketBatch0108.bracket1740
  (20348513633692679313611868360612846636747/10000000000000000000000000000000000000000) (818851831933374331902420126854020967439/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1739
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1740
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (5088819639329134372618385387476728629501/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5088819639329134372618385387476728629501/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (20368829037424853605385166377838840321591/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20368829037424853605385166377838840321591/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (8144821518948278219171741585549150967919/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8144821518948278219171741585549150967919/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1740 BracketBatch0108.bracket1741 (8144821518948278219171741585549150967919/4000000000000000000000000000000000000000) (819537461596321984530691458954910198537/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1740 BracketBatch0108.bracket1741
  (8144821518948278219171741585549150967919/4000000000000000000000000000000000000000) (819537461596321984530691458954910198537/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1740
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1741
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (5092207259356213401346291594459710080397/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5092207259356213401346291594459710080397/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (10191200099329518449959525760895399307517/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10191200099329518449959525760895399307517/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (20375614618041945252652108949814819468311/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20375614618041945252652108949814819468311/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1741 BracketBatch0108.bracket1742 (20375614618041945252652108949814819468311/10000000000000000000000000000000000000000) (410111943842804843120662415976679982069/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1741 BracketBatch0108.bracket1742
  (20375614618041945252652108949814819468311/10000000000000000000000000000000000000000) (410111943842804843120662415976679982069/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1741
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1742
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (20382400198659036899919051521790798615031/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20382400198659036899919051521790798615031/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (20395992089427694087894277606101348937057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20395992089427694087894277606101348937057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (5097299036010841373476666140986518444011/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5097299036010841373476666140986518444011/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1742 BracketBatch0108.bracket1743 (5097299036010841373476666140986518444011/2500000000000000000000000000000000000000) (164182222301056432928085233001568387243/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1742 BracketBatch0108.bracket1743
  (5097299036010841373476666140986518444011/2500000000000000000000000000000000000000) (164182222301056432928085233001568387243/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1742
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1743
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (10197996044713847043947138803050674468527/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10197996044713847043947138803050674468527/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0272.rows BesselBatch0272.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (20409604758283288611599999432719006916841/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20409604758283288611599999432719006916841/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0625.rows BesselBatch0625.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (8161119369542196539898855407764071170779/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8161119369542196539898855407764071170779/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0217.rows ScalarLogs0217.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1743 BracketBatch0109.bracket1744 (8161119369542196539898855407764071170779/4000000000000000000000000000000000000000) (821599134361927112294395711490076994889/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1743 BracketBatch0109.bracket1744
  (8161119369542196539898855407764071170779/4000000000000000000000000000000000000000) (821599134361927112294395711490076994889/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1743
