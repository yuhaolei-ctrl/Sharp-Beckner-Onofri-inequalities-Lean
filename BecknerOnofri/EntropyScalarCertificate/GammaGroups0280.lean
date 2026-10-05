import BecknerOnofri.EntropyScalarCertificate.Bessel0350
import BecknerOnofri.EntropyScalarCertificate.Bessel0351
import BecknerOnofri.EntropyScalarCertificate.Bessel0663
import BecknerOnofri.EntropyScalarCertificate.Bessel0664
import BecknerOnofri.EntropyScalarCertificate.Brackets0140
import BecknerOnofri.EntropyScalarCertificate.Logs0280
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2240
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (26584890774676518191674218320383585634083/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26584890774676518191674218320383585634083/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (53391282547637229188126157201075588293389/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (53391282547637229188126157201075588293389/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (21312212819398053114294918768368551912311/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21312212819398053114294918768368551912311/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2240 BracketBatch0140.bracket2241 (21312212819398053114294918768368551912311/2000000000000000000000000000000000000000) (1422713975210068874232979537320130391153/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2240 BracketBatch0140.bracket2241
  (21312212819398053114294918768368551912311/2000000000000000000000000000000000000000) (1422713975210068874232979537320130391153/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2240
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2241
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (4271302603810978335050092576086047063471/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4271302603810978335050092576086047063471/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (107229323279437741078697036363783861085643/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (107229323279437741078697036363783861085643/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0663.rows BesselBatch0663.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (107005944187356099727474675382967518836209/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (107005944187356099727474675382967518836209/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2241 BracketBatch0140.bracket2242 (107005944187356099727474675382967518836209/10000000000000000000000000000000000000000) (2850946173219586677382855600797020889439/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2241 BracketBatch0140.bracket2242
  (107005944187356099727474675382967518836209/10000000000000000000000000000000000000000) (2850946173219586677382855600797020889439/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2241
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2242
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (2680733081985943526967425909094596527141/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2680733081985943526967425909094596527141/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (26919971400184586375027463100831547811263/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (26919971400184586375027463100831547811263/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (53727302220044021644701722191777513082673/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (53727302220044021644701722191777513082673/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2242 BracketBatch0140.bracket2243 (53727302220044021644701722191777513082673/5000000000000000000000000000000000000000) (142824465912287574591085455986242464011/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2242 BracketBatch0140.bracket2243
  (53727302220044021644701722191777513082673/5000000000000000000000000000000000000000) (142824465912287574591085455986242464011/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2242
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2243
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (107679885600738345500109852403326191245049/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (107679885600738345500109852403326191245049/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (54067150414186273886926727791961789862939/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54067150414186273886926727791961789862939/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (215814186429110893273963307987249770970927/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (215814186429110893273963307987249770970927/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2243 BracketBatch0140.bracket2244 (215814186429110893273963307987249770970927/20000000000000000000000000000000000000000) (2862057593745208124880359552777298729287/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2243 BracketBatch0140.bracket2244
  (215814186429110893273963307987249770970927/20000000000000000000000000000000000000000) (2862057593745208124880359552777298729287/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2243
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2244
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (865074406626980382190827644671388637807/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (865074406626980382190827644671388637807/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (10859261856877960124430592377569413244603/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10859261856877960124430592377569413244603/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (43345383879430429803631875871923542434381/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43345383879430429803631875871923542434381/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2244 BracketBatch0140.bracket2245 (43345383879430429803631875871923542434381/4000000000000000000000000000000000000000) (2867651210430525896007886868216793081611/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2244 BracketBatch0140.bracket2245
  (43345383879430429803631875871923542434381/4000000000000000000000000000000000000000) (2867651210430525896007886868216793081611/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2244
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2245
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (108592618568779601244305923775694132446027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (108592618568779601244305923775694132446027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (109054889283685753426488205012526944620319/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (109054889283685753426488205012526944620319/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (108823753926232677335397064394110538533173/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (108823753926232677335397064394110538533173/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2245 BracketBatch0140.bracket2246 (108823753926232677335397064394110538533173/10000000000000000000000000000000000000000) (359158797689510507058975240175904587203/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2245 BracketBatch0140.bracket2246
  (108823753926232677335397064394110538533173/10000000000000000000000000000000000000000) (359158797689510507058975240175904587203/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2245
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2246
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0350.rows BesselBatch0350.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (27263722320921438356622051253131736155079/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (27263722320921438356622051253131736155079/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (13690145538577117350555277420418940547647/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (13690145538577117350555277420418940547647/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (54644013398075673057732606093969617250373/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (54644013398075673057732606093969617250373/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2246 BracketBatch0140.bracket2247 (54644013398075673057732606093969617250373/5000000000000000000000000000000000000000) (575783064550889869769616320868700333133/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2246 BracketBatch0140.bracket2247
  (54644013398075673057732606093969617250373/5000000000000000000000000000000000000000) (575783064550889869769616320868700333133/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2246
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2247
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (109521164308616938804442219363351524381173/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (109521164308616938804442219363351524381173/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0351.rows BesselBatch0351.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (54995747935947205757487271162603726410071/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (54995747935947205757487271162603726410071/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0664.rows BesselBatch0664.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (43902532036102270063883352337711795440263/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43902532036102270063883352337711795440263/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0280.rows ScalarLogs0280.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0140.bracket2247 BracketBatch0140.bracket2248 (43902532036102270063883352337711795440263/4000000000000000000000000000000000000000) (360573281559165196276113757768496782809/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0140.bracket2247 BracketBatch0140.bracket2248
  (43902532036102270063883352337711795440263/4000000000000000000000000000000000000000) (360573281559165196276113757768496782809/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2247
