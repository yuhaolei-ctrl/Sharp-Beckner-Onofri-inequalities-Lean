module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0156
public import BecknerOnofri.EntropyScalarCertificate.Bessel0157
public import BecknerOnofri.EntropyScalarCertificate.Bessel0567
public import BecknerOnofri.EntropyScalarCertificate.Brackets0062
public import BecknerOnofri.EntropyScalarCertificate.Brackets0063
public import BecknerOnofri.EntropyScalarCertificate.Logs0125
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1000
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1379891731019276822803230768017474376637/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1379891731019276822803230768017474376637/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (5534685924694426609616418211120373461551/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5534685924694426609616418211120373461551/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (11054252848771533900829341283190270968099/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11054252848771533900829341283190270968099/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1000 BracketBatch0062.bracket1001 (11054252848771533900829341283190270968099/20000000000000000000000000000000000000000) (46654126493759688060012093395967468543/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1000 BracketBatch0062.bracket1001
  (11054252848771533900829341283190270968099/20000000000000000000000000000000000000000) (46654126493759688060012093395967468543/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1000
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1001
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (1383671481173606652404104552780093365387/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1383671481173606652404104552780093365387/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (554983590401182818143118907741406734301/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (554983590401182818143118907741406734301/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (5542260914353127395523803644267220402279/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5542260914353127395523803644267220402279/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1001 BracketBatch0062.bracket1002 (5542260914353127395523803644267220402279/10000000000000000000000000000000000000000) (47066147739268674228622472352532941301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1001 BracketBatch0062.bracket1002
  (5542260914353127395523803644267220402279/10000000000000000000000000000000000000000) (47066147739268674228622472352532941301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1001
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1002
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (5549835904011828181431189077414067343007/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5549835904011828181431189077414067343007/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2782508520923897518829949810983339111233/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2782508520923897518829949810983339111233/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (11114852945859623219091088699380745565473/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11114852945859623219091088699380745565473/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1002 BracketBatch0062.bracket1003 (11114852945859623219091088699380745565473/20000000000000000000000000000000000000000) (47481073815328566871112171031035715151/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1002 BracketBatch0062.bracket1003
  (11114852945859623219091088699380745565473/20000000000000000000000000000000000000000) (47481073815328566871112171031035715151/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1002
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1003
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (5565017041847795037659899621966678222463/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5565017041847795037659899621966678222463/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (697528689919204501333934046980434352699/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (697528689919204501333934046980434352699/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (2229049312240286209666274399562030608811/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2229049312240286209666274399562030608811/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1003 BracketBatch0062.bracket1004 (2229049312240286209666274399562030608811/4000000000000000000000000000000000000000) (23949460577787301649034408330108247279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1003 BracketBatch0062.bracket1004
  (2229049312240286209666274399562030608811/4000000000000000000000000000000000000000) (23949460577787301649034408330108247279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1003
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1004
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0156.rows BesselBatch0156.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (5580229519353636010671472375843474821589/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5580229519353636010671472375843474821589/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (5595473519026797568670071748202251347459/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5595473519026797568670071748202251347459/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (1396962879797554197417693015505715771131/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1396962879797554197417693015505715771131/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1004 BracketBatch0062.bracket1005 (1396962879797554197417693015505715771131/2500000000000000000000000000000000000000) (9663941256244811188075799757389150049/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1004 BracketBatch0062.bracket1005
  (1396962879797554197417693015505715771131/2500000000000000000000000000000000000000) (9663941256244811188075799757389150049/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1004
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1005
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (10928659216849214001308733883207522163/19531250000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10928659216849214001308733883207522163/19531250000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (5610749224724336676131731358767727648657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5610749224724336676131731358767727648657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (11206222743751134244801803106969978996113/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11206222743751134244801803106969978996113/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1005 BracketBatch0062.bracket1006 (11206222743751134244801803106969978996113/20000000000000000000000000000000000000000) (487434458017322783643114480216653521/100000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1005 BracketBatch0062.bracket1006
  (11206222743751134244801803106969978996113/20000000000000000000000000000000000000000) (487434458017322783643114480216653521/100000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1005
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1006
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (2805374612362168338065865679383863824327/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2805374612362168338065865679383863824327/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (5626056821676556985691375450572764580909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5626056821676556985691375450572764580909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (11236806046400893661823106809340492229563/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11236806046400893661823106809340492229563/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1006 BracketBatch0062.bracket1007 (11236806046400893661823106809340492229563/20000000000000000000000000000000000000000) (24585078207728089433251949909933666143/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1006 BracketBatch0062.bracket1007
  (11236806046400893661823106809340492229563/20000000000000000000000000000000000000000) (24585078207728089433251949909933666143/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1006
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1007
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (2813028410838278492845687725286382290453/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2813028410838278492845687725286382290453/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0157.rows BesselBatch0157.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (352587281031300669053693749080881713259/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (352587281031300669053693749080881713259/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0567.rows BesselBatch0567.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (225349066363547353811009508717337439861/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (225349066363547353811009508717337439861/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0125.rows ScalarLogs0125.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0062.bracket1007 BracketBatch0063.bracket1008 (225349066363547353811009508717337439861/400000000000000000000000000000000000000) (49599854910325225805210938958812622131/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0062.bracket1007 BracketBatch0063.bracket1008
  (225349066363547353811009508717337439861/400000000000000000000000000000000000000) (49599854910325225805210938958812622131/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1007
