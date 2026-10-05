module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0311
public import BecknerOnofri.EntropyScalarCertificate.Bessel0312
public import BecknerOnofri.EntropyScalarCertificate.Bessel0644
public import BecknerOnofri.EntropyScalarCertificate.Bessel0645
public import BecknerOnofri.EntropyScalarCertificate.Brackets0124
public import BecknerOnofri.EntropyScalarCertificate.Brackets0125
public import BecknerOnofri.EntropyScalarCertificate.Logs0249
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1992
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (10559045059528156203556571964854555583529/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10559045059528156203556571964854555583529/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (52901035903466700475300282458904279894761/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52901035903466700475300282458904279894761/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (52848130600553740746541571141588528906203/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (52848130600553740746541571141588528906203/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1992 BracketBatch0124.bracket1993 (52848130600553740746541571141588528906203/10000000000000000000000000000000000000000) (77517405335905191033788364672486292611/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1992 BracketBatch0124.bracket1993
  (52848130600553740746541571141588528906203/10000000000000000000000000000000000000000) (77517405335905191033788364672486292611/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1992
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1993
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (26450517951733350237650141229452139947379/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26450517951733350237650141229452139947379/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (53007284981027009070691095101688298387433/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53007284981027009070691095101688298387433/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (105908320884493709545991377560592578282191/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (105908320884493709545991377560592578282191/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1993 BracketBatch0124.bracket1994 (105908320884493709545991377560592578282191/20000000000000000000000000000000000000000) (970229168593214191350728534187407097301/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1993 BracketBatch0124.bracket1994
  (105908320884493709545991377560592578282191/20000000000000000000000000000000000000000) (970229168593214191350728534187407097301/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1993
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1994
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (5300728498102700907069109510168829838743/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5300728498102700907069109510168829838743/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (53113975252059954732679464656232623521401/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53113975252059954732679464656232623521401/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (106121260233086963803370559757920921908831/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (106121260233086963803370559757920921908831/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1994 BracketBatch0124.bracket1995 (106121260233086963803370559757920921908831/20000000000000000000000000000000000000000) (194298739623289503210347708869256062651/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1994 BracketBatch0124.bracket1995
  (106121260233086963803370559757920921908831/20000000000000000000000000000000000000000) (194298739623289503210347708869256062651/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1994
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1995
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (26556987626029977366339732328116311760699/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26556987626029977366339732328116311760699/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (13305277365224243946158918634388011518143/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13305277365224243946158918634388011518143/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (10633508471295693051731513919378466959397/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10633508471295693051731513919378466959397/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1995 BracketBatch0124.bracket1996 (10633508471295693051731513919378466959397/2000000000000000000000000000000000000000) (121595145942877339176271226245467882547/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1995 BracketBatch0124.bracket1996
  (10633508471295693051731513919378466959397/2000000000000000000000000000000000000000) (121595145942877339176271226245467882547/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1995
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1996
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0311.rows BesselBatch0311.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (53221109460896975784635674537552046072569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (53221109460896975784635674537552046072569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (53328690374697525212368953229269273152479/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53328690374697525212368953229269273152479/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (13318724979449312624625578470852664903131/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13318724979449312624625578470852664903131/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1996 BracketBatch0124.bracket1997 (13318724979449312624625578470852664903131/2500000000000000000000000000000000000000) (1948063178453276964117510268114260237679/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1996 BracketBatch0124.bracket1997
  (13318724979449312624625578470852664903131/2500000000000000000000000000000000000000) (1948063178453276964117510268114260237679/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1996
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1997
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (13332172593674381303092238307317318288119/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13332172593674381303092238307317318288119/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (53436720783686830183285006258302069143813/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53436720783686830183285006258302069143813/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0644.rows BesselBatch0644.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (106765411158384355395653959487571342296289/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (106765411158384355395653959487571342296289/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1997 BracketBatch0124.bracket1998 (106765411158384355395653959487571342296289/20000000000000000000000000000000000000000) (1950609951201791593711939910367504196641/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1997 BracketBatch0124.bracket1998
  (106765411158384355395653959487571342296289/20000000000000000000000000000000000000000) (1950609951201791593711939910367504196641/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1997
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1998
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (5343672078368683018328500625830206914381/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5343672078368683018328500625830206914381/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (53545203501396629718187886064791781491377/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53545203501396629718187886064791781491377/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (106981924285083459901472892323093850635187/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (106981924285083459901472892323093850635187/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1998 BracketBatch0124.bracket1999 (106981924285083459901472892323093850635187/20000000000000000000000000000000000000000) (244145334794984091148537015508673128653/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1998 BracketBatch0124.bracket1999
  (106981924285083459901472892323093850635187/20000000000000000000000000000000000000000) (244145334794984091148537015508673128653/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1998
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1999
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (26772601750698314859093943032395890745687/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26772601750698314859093943032395890745687/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0312.rows BesselBatch0312.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (26827070682454467067476931767043377125819/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26827070682454467067476931767043377125819/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0645.rows BesselBatch0645.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (26799836216576390963285437399719633935753/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26799836216576390963285437399719633935753/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0249.rows ScalarLogs0249.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0124.bracket1999 BracketBatch0125.bracket2000 (26799836216576390963285437399719633935753/5000000000000000000000000000000000000000) (1955721385118296388386593382514285408249/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0124.bracket1999 BracketBatch0125.bracket2000
  (26799836216576390963285437399719633935753/5000000000000000000000000000000000000000) (1955721385118296388386593382514285408249/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1999
