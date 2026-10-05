import BecknerOnofri.EntropyScalarCertificate.Bessel0270
import BecknerOnofri.EntropyScalarCertificate.Bessel0271
import BecknerOnofri.EntropyScalarCertificate.Bessel0623
import BecknerOnofri.EntropyScalarCertificate.Bessel0624
import BecknerOnofri.EntropyScalarCertificate.Brackets0108
import BecknerOnofri.EntropyScalarCertificate.Logs0216
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1728
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (5048567124305944424578336807928294828671/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5048567124305944424578336807928294828671/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (5051893632007183811343533488380419078261/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5051893632007183811343533488380419078261/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (2525115189078282058980467574077178476733/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2525115189078282058980467574077178476733/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1728 BracketBatch0108.bracket1729 (2525115189078282058980467574077178476733/1250000000000000000000000000000000000000) (405681049675456497120322947976850424999/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1728 BracketBatch0108.bracket1729
  (2525115189078282058980467574077178476733/1250000000000000000000000000000000000000) (405681049675456497120322947976850424999/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1728
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1729
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (20207574528028735245374133953521676313041/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20207574528028735245374133953521676313041/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (10110450335045497839696065284479433605631/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10110450335045497839696065284479433605631/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0623.rows BesselBatch0623.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (40428475198119730924766264522480543524303/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40428475198119730924766264522480543524303/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1729 BracketBatch0108.bracket1730 (40428475198119730924766264522480543524303/20000000000000000000000000000000000000000) (162407810733901893379410984389192604359/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1729 BracketBatch0108.bracket1730
  (40428475198119730924766264522480543524303/20000000000000000000000000000000000000000) (162407810733901893379410984389192604359/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1729
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1730
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (20220900670090995679392130568958867211259/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20220900670090995679392130568958867211259/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (809369878805304290581406048578406730713/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (809369878805304290581406048578406730713/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (10113786910055900735981820445854758869771/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10113786910055900735981820445854758869771/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1730 BracketBatch0108.bracket1731 (10113786910055900735981820445854758869771/5000000000000000000000000000000000000000) (162543358047231351324183649880459479831/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1730 BracketBatch0108.bracket1731
  (10113786910055900735981820445854758869771/5000000000000000000000000000000000000000) (162543358047231351324183649880459479831/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1730
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1731
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (10117123485066303632267575607230084133911/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10117123485066303632267575607230084133911/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (20247613475013412264873721487358260536423/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20247613475013412264873721487358260536423/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (8096372089029203905881774540363685760849/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8096372089029203905881774540363685760849/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1731 BracketBatch0108.bracket1732 (8096372089029203905881774540363685760849/4000000000000000000000000000000000000000) (813395310327302696245194182756664982887/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1731 BracketBatch0108.bracket1732
  (8096372089029203905881774540363685760849/4000000000000000000000000000000000000000) (813395310327302696245194182756664982887/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1731
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1732
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1012380673750670613243686074367913026821/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1012380673750670613243686074367913026821/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2532625028966442522453138173079564583473/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2532625028966442522453138173079564583473/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (10127153426686238111124706717998694301051/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10127153426686238111124706717998694301051/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1732 BracketBatch0108.bracket1733 (10127153426686238111124706717998694301051/5000000000000000000000000000000000000000) (407037307610937915229340229354215305009/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1732 BracketBatch0108.bracket1733
  (10127153426686238111124706717998694301051/5000000000000000000000000000000000000000) (407037307610937915229340229354215305009/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1732
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1733
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (20261000231731540179625105384636516667781/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20261000231731540179625105384636516667781/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (20274407287423903120498778687391134087909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20274407287423903120498778687391134087909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (4053540751915544330012388407202765075569/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4053540751915544330012388407202765075569/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1733 BracketBatch0108.bracket1734 (4053540751915544330012388407202765075569/2000000000000000000000000000000000000000) (407377353100645488040167107571281512037/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1733 BracketBatch0108.bracket1734
  (4053540751915544330012388407202765075569/2000000000000000000000000000000000000000) (407377353100645488040167107571281512037/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1733
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1734
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0270.rows BesselBatch0270.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (10137203643711951560249389343695567043953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10137203643711951560249389343695567043953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (811513387574667733698729128277869294163/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (811513387574667733698729128277869294163/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (40562241976790596462967006894337866441981/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (40562241976790596462967006894337866441981/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1734 BracketBatch0108.bracket1735 (40562241976790596462967006894337866441981/20000000000000000000000000000000000000000) (815435584549454801775135508043521016441/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1734 BracketBatch0108.bracket1735
  (40562241976790596462967006894337866441981/20000000000000000000000000000000000000000) (815435584549454801775135508043521016441/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1734
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1735
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (2535979336170836667808528525868341544259/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2535979336170836667808528525868341544259/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0271.rows BesselBatch0271.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (10150641242487941469682406366566892063541/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10150641242487941469682406366566892063541/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0624.rows BesselBatch0624.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (20294558587171288140916520470040258240577/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20294558587171288140916520470040258240577/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0216.rows ScalarLogs0216.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0108.bracket1735 BracketBatch0108.bracket1736 (20294558587171288140916520470040258240577/10000000000000000000000000000000000000000) (204029312888192856833921338616208759087/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0108.bracket1735 BracketBatch0108.bracket1736
  (20294558587171288140916520470040258240577/10000000000000000000000000000000000000000) (204029312888192856833921338616208759087/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1735
