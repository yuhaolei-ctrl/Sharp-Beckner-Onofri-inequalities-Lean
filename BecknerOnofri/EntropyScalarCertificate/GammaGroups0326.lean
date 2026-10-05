module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0407
public import BecknerOnofri.EntropyScalarCertificate.Bessel0408
public import BecknerOnofri.EntropyScalarCertificate.Bessel0692
public import BecknerOnofri.EntropyScalarCertificate.Bessel0693
public import BecknerOnofri.EntropyScalarCertificate.Brackets0163
public import BecknerOnofri.EntropyScalarCertificate.Logs0326
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2608
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (464223227456713754135249432700450508143749/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (464223227456713754135249432700450508143749/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (232972120410832005760452588884488564092659/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (232972120410832005760452588884488564092659/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (930167468278377765656154610469427636329067/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (930167468278377765656154610469427636329067/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2608 BracketBatch0163.bracket2609 (930167468278377765656154610469427636329067/20000000000000000000000000000000000000000) (616977241691364606706142348099679760281/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2608 BracketBatch0163.bracket2609
  (930167468278377765656154610469427636329067/20000000000000000000000000000000000000000) (616977241691364606706142348099679760281/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2608
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2609
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (93188848164332802304181035553795425637063/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (93188848164332802304181035553795425637063/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (467678097861547992399513458093659951339409/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (467678097861547992399513458093659951339409/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (233405584670803000980104658965659269881181/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (233405584670803000980104658965659269881181/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2609 BracketBatch0163.bracket2610 (233405584670803000980104658965659269881181/5000000000000000000000000000000000000000) (1235316238372952283951317385277813493177/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2609 BracketBatch0163.bracket2610
  (233405584670803000980104658965659269881181/5000000000000000000000000000000000000000) (1235316238372952283951317385277813493177/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2609
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2610
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (233839048930773996199756729046829975669703/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (233839048930773996199756729046829975669703/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (117356235721818571850350563812118897156831/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (117356235721818571850350563812118897156831/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (93710304074882227980091571334213553996673/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (93710304074882227980091571334213553996673/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2610 BracketBatch0163.bracket2611 (93710304074882227980091571334213553996673/2000000000000000000000000000000000000000) (4946732572506395811272330044895432203389/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2610 BracketBatch0163.bracket2611
  (93710304074882227980091571334213553996673/2000000000000000000000000000000000000000) (4946732572506395811272330044895432203389/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2610
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2611
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0407.rows BesselBatch0407.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (469424942887274287401402255248475588627321/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (469424942887274287401402255248475588627321/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (58898115297480044061976922610673025520961/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58898115297480044061976922610673025520961/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (940609865267114639897217636133859792795009/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (940609865267114639897217636133859792795009/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2611 BracketBatch0163.bracket2612 (940609865267114639897217636133859792795009/20000000000000000000000000000000000000000) (619027616550662094563899311341410744083/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2611 BracketBatch0163.bracket2612
  (940609865267114639897217636133859792795009/20000000000000000000000000000000000000000) (619027616550662094563899311341410744083/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2611
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2612
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (94236984475968070499163076177076840833537/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (94236984475968070499163076177076840833537/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (47295818503127758191423849491895019097119/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47295818503127758191423849491895019097119/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0692.rows BesselBatch0692.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (7553144859288943475280431006434675161111/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7553144859288943475280431006434675161111/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2612 BracketBatch0163.bracket2613 (7553144859288943475280431006434675161111/160000000000000000000000000000000000000) (309858136023642418470173586822646656033/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2612 BracketBatch0163.bracket2613
  (7553144859288943475280431006434675161111/160000000000000000000000000000000000000) (309858136023642418470173586822646656033/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2612
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2613
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (472958185031277581914238494918950190971187/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (472958185031277581914238494918950190971187/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (474744881786526950912897655882585709499873/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (474744881786526950912897655882585709499873/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (47385153340890226641356807540076795023553/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (47385153340890226641356807540076795023553/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2613 BracketBatch0163.bracket2614 (47385153340890226641356807540076795023553/1000000000000000000000000000000000000000) (620407556123680196929062552777794514137/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2613 BracketBatch0163.bracket2614
  (47385153340890226641356807540076795023553/1000000000000000000000000000000000000000) (620407556123680196929062552777794514137/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2613
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2614
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (47474488178652695091289765588258570949987/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47474488178652695091289765588258570949987/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (476545165886269996392963506017188134179413/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (476545165886269996392963506017188134179413/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (951290047672796947305861161899773843679283/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (951290047672796947305861161899773843679283/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2614 BracketBatch0163.bracket2615 (951290047672796947305861161899773843679283/20000000000000000000000000000000000000000) (2484405948096277130752938563153256254069/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2614 BracketBatch0163.bracket2615
  (951290047672796947305861161899773843679283/20000000000000000000000000000000000000000) (2484405948096277130752938563153256254069/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2614
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2615
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (47654516588626999639296350601718813417941/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (47654516588626999639296350601718813417941/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (5979489911384258245904615627867663170631/125000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5979489911384258245904615627867663170631/125000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (95490435879701065606533275624660118782989/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95490435879701065606533275624660118782989/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0326.rows ScalarLogs0326.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2615 BracketBatch0163.bracket2616 (95490435879701065606533275624660118782989/2000000000000000000000000000000000000000) (1243596166336634706697688245447433583791/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2615 BracketBatch0163.bracket2616
  (95490435879701065606533275624660118782989/2000000000000000000000000000000000000000) (1243596166336634706697688245447433583791/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2615
