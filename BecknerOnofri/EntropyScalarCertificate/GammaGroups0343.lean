module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0428
public import BecknerOnofri.EntropyScalarCertificate.Bessel0429
public import BecknerOnofri.EntropyScalarCertificate.Bessel0430
public import BecknerOnofri.EntropyScalarCertificate.Bessel0703
public import BecknerOnofri.EntropyScalarCertificate.Brackets0171
public import BecknerOnofri.EntropyScalarCertificate.Brackets0172
public import BecknerOnofri.EntropyScalarCertificate.Logs0343
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2744
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (428709949483642541095602369470428860969423/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (428709949483642541095602369470428860969423/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (858888438996256794013238162234981133831649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (858888438996256794013238162234981133831649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (343261667592708375240888580235167771154099/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (343261667592708375240888580235167771154099/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2744 BracketBatch0171.bracket2745 (343261667592708375240888580235167771154099/4000000000000000000000000000000000000000) (5877012587360760778082483952567999987383/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2744 BracketBatch0171.bracket2745
  (343261667592708375240888580235167771154099/4000000000000000000000000000000000000000) (5877012587360760778082483952567999987383/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2744
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2745
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0428.rows BesselBatch0428.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (429444219498128397006619081117490566915823/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (429444219498128397006619081117490566915823/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (860362025587474082202663565715692316563201/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (860362025587474082202663565715692316563201/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (1719250464583730876215901727950673450394847/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1719250464583730876215901727950673450394847/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2745 BracketBatch0171.bracket2746 (1719250464583730876215901727950673450394847/20000000000000000000000000000000000000000) (5879639408279815840677134340424574928069/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2745 BracketBatch0171.bracket2746
  (1719250464583730876215901727950673450394847/20000000000000000000000000000000000000000) (5879639408279815840677134340424574928069/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2745
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2746
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (430181012793737041101331782857846158281599/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (430181012793737041101331782857846158281599/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (107730085599864537055616866106651540505697/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (107730085599864537055616866106651540505697/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (861101355193195189323799247284452320304387/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (861101355193195189323799247284452320304387/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2746 BracketBatch0171.bracket2747 (861101355193195189323799247284452320304387/10000000000000000000000000000000000000000) (1470567712522965891358884289761021789077/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2746 BracketBatch0171.bracket2747
  (861101355193195189323799247284452320304387/10000000000000000000000000000000000000000) (1470567712522965891358884289761021789077/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2746
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2747
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (861840684798916296444934928853212324045573/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (861840684798916296444934928853212324045573/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (863324442868272988933637689413899665071799/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (863324442868272988933637689413899665071799/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (431291281916797321344643154566777997279343/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (431291281916797321344643154566777997279343/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2747 BracketBatch0171.bracket2748 (431291281916797321344643154566777997279343/5000000000000000000000000000000000000000) (5884906928340783251623124496103555393079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2747 BracketBatch0171.bracket2748
  (431291281916797321344643154566777997279343/5000000000000000000000000000000000000000) (5884906928340783251623124496103555393079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2747
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2748
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (215831110717068247233409422353474916267949/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (215831110717068247233409422353474916267949/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (864813326214495815946539702223723743873203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (864813326214495815946539702223723743873203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (1728137769082768804880177391637623408944999/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1728137769082768804880177391637623408944999/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2748 BracketBatch0171.bracket2749 (1728137769082768804880177391637623408944999/20000000000000000000000000000000000000000) (5887547658647315188852694174844313548911/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2748 BracketBatch0171.bracket2749
  (1728137769082768804880177391637623408944999/20000000000000000000000000000000000000000) (5887547658647315188852694174844313548911/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2748
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2749
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (2162033315536239539866349255559309359683/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2162033315536239539866349255559309359683/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (866307361439366549126583905745576081232659/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (866307361439366549126583905745576081232659/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1731120687653862365073123607969299825105859/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1731120687653862365073123607969299825105859/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2749 BracketBatch0171.bracket2750 (1731120687653862365073123607969299825105859/20000000000000000000000000000000000000000) (5890193056709554917340988004853478130547/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2749 BracketBatch0171.bracket2750
  (1731120687653862365073123607969299825105859/20000000000000000000000000000000000000000) (5890193056709554917340988004853478130547/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2749
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2750
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (54144210089960409320411494109098505077041/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (54144210089960409320411494109098505077041/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (173561315065816278381236841531289063685041/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (173561315065816278381236841531289063685041/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (1734113936768447941032768113402021399657861/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1734113936768447941032768113402021399657861/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2750 BracketBatch0171.bracket2751 (1734113936768447941032768113402021399657861/20000000000000000000000000000000000000000) (1178568627660690264979983866754280349039/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2750 BracketBatch0171.bracket2751
  (1734113936768447941032768113402021399657861/20000000000000000000000000000000000000000) (1178568627660690264979983866754280349039/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2750
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2751
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0429.rows BesselBatch0429.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (433903287664540695953092103828222659212601/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (433903287664540695953092103828222659212601/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0430.rows BesselBatch0430.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (43465549742792589961380389413292184772481/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43465549742792589961380389413292184772481/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0703.rows BesselBatch0703.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (868558785092466595566895997961144506937411/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (868558785092466595566895997961144506937411/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0343.rows ScalarLogs0343.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0171.bracket2751 BracketBatch0172.bracket2752 (868558785092466595566895997961144506937411/10000000000000000000000000000000000000000) (5895497919283308614563367443728802310121/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0171.bracket2751 BracketBatch0172.bracket2752
  (868558785092466595566895997961144506937411/10000000000000000000000000000000000000000) (5895497919283308614563367443728802310121/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2751
