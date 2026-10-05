module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0376
public import BecknerOnofri.EntropyScalarCertificate.Bessel0377
public import BecknerOnofri.EntropyScalarCertificate.Bessel0677
public import BecknerOnofri.EntropyScalarCertificate.Brackets0150
public import BecknerOnofri.EntropyScalarCertificate.Brackets0151
public import BecknerOnofri.EntropyScalarCertificate.Logs0301
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2408
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (267225501110466390072055072078141870188071/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (267225501110466390072055072078141870188071/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (53558507039866416846154003667652502950821/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53558507039866416846154003667652502950821/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (16719313634681202321963284075512637029443/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16719313634681202321963284075512637029443/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2408 BracketBatch0150.bracket2409 (16719313634681202321963284075512637029443/625000000000000000000000000000000000000) (2065547118169015291864385844333165039159/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2408 BracketBatch0150.bracket2409
  (16719313634681202321963284075512637029443/625000000000000000000000000000000000000) (2065547118169015291864385844333165039159/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2408
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2409
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (133896267599666042115385009169131257377051/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (133896267599666042115385009169131257377051/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (268361992683178839839893600835329656452421/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (268361992683178839839893600835329656452421/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (536154527882510924070663619173592171206523/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (536154527882510924070663619173592171206523/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2409 BracketBatch0150.bracket2410 (536154527882510924070663619173592171206523/20000000000000000000000000000000000000000) (258383696653167278273131049568545807307/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2409 BracketBatch0150.bracket2410
  (536154527882510924070663619173592171206523/20000000000000000000000000000000000000000) (258383696653167278273131049568545807307/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2409
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2410
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (134180996341589419919946800417664828226209/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (134180996341589419919946800417664828226209/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (268933889129826634282776733821842769067917/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (268933889129826634282776733821842769067917/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (107459176362601094824534066931434485104067/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (107459176362601094824534066931434485104067/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2410 BracketBatch0150.bracket2411 (107459176362601094824534066931434485104067/4000000000000000000000000000000000000000) (1034297739177342766958781014010616633253/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2410 BracketBatch0150.bracket2411
  (107459176362601094824534066931434485104067/4000000000000000000000000000000000000000) (1034297739177342766958781014010616633253/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2410
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2411
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (134466944564913317141388366910921384533957/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (134466944564913317141388366910921384533957/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (269508240240724810102357837856183297668223/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (269508240240724810102357837856183297668223/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (538442129370551444385134571678026066736137/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (538442129370551444385134571678026066736137/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2411 BracketBatch0150.bracket2412 (538442129370551444385134571678026066736137/20000000000000000000000000000000000000000) (4140249696558466027604217306212986409511/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2411 BracketBatch0150.bracket2412
  (538442129370551444385134571678026066736137/20000000000000000000000000000000000000000) (4140249696558466027604217306212986409511/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2411
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2412
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (13475412012036240505117891892809164883411/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (13475412012036240505117891892809164883411/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (27008506185238894989025371584328488146859/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (27008506185238894989025371584328488146859/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (53959330209311375999261155369946817913681/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (53959330209311375999261155369946817913681/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2412 BracketBatch0150.bracket2413 (53959330209311375999261155369946817913681/2000000000000000000000000000000000000000) (2071657697812610760769404106834910743973/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2412 BracketBatch0150.bracket2413
  (53959330209311375999261155369946817913681/2000000000000000000000000000000000000000) (2071657697812610760769404106834910743973/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2412
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2413
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (270085061852388949890253715843284881468587/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (270085061852388949890253715843284881468587/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (270664369937856331454592986156349955607907/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (270664369937856331454592986156349955607907/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (270374715895122640672423350999817418538247/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (270374715895122640672423350999817418538247/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2413 BracketBatch0150.bracket2414 (270374715895122640672423350999817418538247/10000000000000000000000000000000000000000) (2073194041860639537181402034709579496343/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2413 BracketBatch0150.bracket2414
  (270374715895122640672423350999817418538247/10000000000000000000000000000000000000000) (2073194041860639537181402034709579496343/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2413
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2414
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (8458261560558010357956030817385936112747/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8458261560558010357956030817385936112747/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (271246180608160244177933747840646924919471/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (271246180608160244177933747840646924919471/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (4335284404368132605060213871975975044219/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4335284404368132605060213871975975044219/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2414 BracketBatch0150.bracket2415 (4335284404368132605060213871975975044219/160000000000000000000000000000000000000) (2074733895422074288099558700089584537583/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2414 BracketBatch0150.bracket2415
  (4335284404368132605060213871975975044219/160000000000000000000000000000000000000) (2074733895422074288099558700089584537583/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2414
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2415
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (67811545152040061044483436960161731229867/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (67811545152040061044483436960161731229867/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0377.rows BesselBatch0377.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (135915255056911726170436404809275905896711/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (135915255056911726170436404809275905896711/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (54307669072198369651880655745919873671289/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54307669072198369651880655745919873671289/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0301.rows ScalarLogs0301.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2415 BracketBatch0151.bracket2416 (54307669072198369651880655745919873671289/2000000000000000000000000000000000000000) (4152554547178709758517319738844919925997/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2415 BracketBatch0151.bracket2416
  (54307669072198369651880655745919873671289/2000000000000000000000000000000000000000) (4152554547178709758517319738844919925997/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2415
