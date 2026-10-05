module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0368
public import BecknerOnofri.EntropyScalarCertificate.Bessel0369
public import BecknerOnofri.EntropyScalarCertificate.Bessel0370
public import BecknerOnofri.EntropyScalarCertificate.Bessel0673
public import BecknerOnofri.EntropyScalarCertificate.Brackets0147
public import BecknerOnofri.EntropyScalarCertificate.Brackets0148
public import BecknerOnofri.EntropyScalarCertificate.Logs0295
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2360
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (213137214752689451324606364373476240893007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (213137214752689451324606364373476240893007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (26868477794150130724978986224278128049367/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26868477794150130724978986224278128049367/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (428085037105890497124438254167701265287943/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (428085037105890497124438254167701265287943/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2360 BracketBatch0147.bracket2361 (428085037105890497124438254167701265287943/20000000000000000000000000000000000000000) (3773812606444709827999103254512696460357/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2360 BracketBatch0147.bracket2361
  (428085037105890497124438254167701265287943/20000000000000000000000000000000000000000) (3773812606444709827999103254512696460357/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2360
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2361
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0368.rows BesselBatch0368.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (214947822353201045799831889794225024394933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (214947822353201045799831889794225024394933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (54197412717444713008327567910581071580383/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54197412717444713008327567910581071580383/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (86347494644595979566628432287309862143293/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (86347494644595979566628432287309862143293/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2361 BracketBatch0147.bracket2362 (86347494644595979566628432287309862143293/4000000000000000000000000000000000000000) (378504024713438362321771912250426864217/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2361 BracketBatch0147.bracket2362
  (86347494644595979566628432287309862143293/4000000000000000000000000000000000000000) (378504024713438362321771912250426864217/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2361
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2362
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (216789650869778852033310271642324286321529/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (216789650869778852033310271642324286321529/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (109331757379082421402158395200904942224201/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (109331757379082421402158395200904942224201/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (435453165627943694837627062044134170769931/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (435453165627943694837627062044134170769931/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2362 BracketBatch0147.bracket2363 (435453165627943694837627062044134170769931/20000000000000000000000000000000000000000) (759271039392953676305995632410484286879/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2362 BracketBatch0147.bracket2363
  (435453165627943694837627062044134170769931/20000000000000000000000000000000000000000) (759271039392953676305995632410484286879/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2362
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2363
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (218663514758164842804316790401809884448399/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (218663514758164842804316790401809884448399/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (55142564262875104288461827954985463252137/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (55142564262875104288461827954985463252137/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (439233771809665259958164102221751737456947/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (439233771809665259958164102221751737456947/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2363 BracketBatch0147.bracket2364 (439233771809665259958164102221751737456947/20000000000000000000000000000000000000000) (3807758462267156801879510431716650254809/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2363 BracketBatch0147.bracket2364
  (439233771809665259958164102221751737456947/20000000000000000000000000000000000000000) (3807758462267156801879510431716650254809/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2363
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2364
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (44114051410300083430769462363988370601709/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44114051410300083430769462363988370601709/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (111255375312406543123334292990064337616667/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (111255375312406543123334292990064337616667/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (443081007676313503400515897800070528241879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (443081007676313503400515897800070528241879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2364 BracketBatch0147.bracket2365 (443081007676313503400515897800070528241879/20000000000000000000000000000000000000000) (3819251053152429058947937735438434619171/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2364 BracketBatch0147.bracket2365
  (443081007676313503400515897800070528241879/20000000000000000000000000000000000000000) (3819251053152429058947937735438434619171/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2364
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2365
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (222510750624813086246668585980128675233331/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (222510750624813086246668585980128675233331/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (56121474881810879367052864518657848206127/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56121474881810879367052864518657848206127/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (446996650152056603714880044054760068057839/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (446996650152056603714880044054760068057839/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2365 BracketBatch0147.bracket2366 (446996650152056603714880044054760068057839/20000000000000000000000000000000000000000) (191541699123406908385018158752249065833/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2365 BracketBatch0147.bracket2366
  (446996650152056603714880044054760068057839/20000000000000000000000000000000000000000) (191541699123406908385018158752249065833/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2365
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2366
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (44897179905448703493642291614926278564901/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44897179905448703493642291614926278564901/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (56624160096571212809797038264180458373501/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (56624160096571212809797038264180458373501/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (450982539913528368707399611131353226318509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (450982539913528368707399611131353226318509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2366 BracketBatch0147.bracket2367 (450982539913528368707399611131353226318509/20000000000000000000000000000000000000000) (3842508264637172510302899341728362501077/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2366 BracketBatch0147.bracket2367
  (450982539913528368707399611131353226318509/20000000000000000000000000000000000000000) (3842508264637172510302899341728362501077/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2366
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2367
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0369.rows BesselBatch0369.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (226496640386284851239188153056721833494001/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (226496640386284851239188153056721833494001/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0370.rows BesselBatch0370.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (45708788777723377944096443069182150177297/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (45708788777723377944096443069182150177297/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0673.rows BesselBatch0673.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (227520292137450870479835184201316292190243/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (227520292137450870479835184201316292190243/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0295.rows ScalarLogs0295.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0147.bracket2367 BracketBatch0148.bracket2368 (227520292137450870479835184201316292190243/10000000000000000000000000000000000000000) (3854274868107982215161469564738703986843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0147.bracket2367 BracketBatch0148.bracket2368
  (227520292137450870479835184201316292190243/10000000000000000000000000000000000000000) (3854274868107982215161469564738703986843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2367
