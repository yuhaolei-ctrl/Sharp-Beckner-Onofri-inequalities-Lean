module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0065
public import BecknerOnofri.EntropyScalarCertificate.Bessel0066
public import BecknerOnofri.EntropyScalarCertificate.Bessel0521
public import BecknerOnofri.EntropyScalarCertificate.Bessel0522
public import BecknerOnofri.EntropyScalarCertificate.Brackets0026
public import BecknerOnofri.EntropyScalarCertificate.Logs0052
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0416
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (1410857884050133571691151567137083410157/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1410857884050133571691151567137083410157/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (706459075080384463069293376650810263129/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (706459075080384463069293376650810263129/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (564755206842180499565947664087740787283/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (564755206842180499565947664087740787283/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0416 BracketBatch0026.bracket0417 (564755206842180499565947664087740787283/4000000000000000000000000000000000000000) (74663375744058957739738946014912421/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0416 BracketBatch0026.bracket0417
  (564755206842180499565947664087740787283/4000000000000000000000000000000000000000) (74663375744058957739738946014912421/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0416
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0417
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (282583630032153785227717350660324105251/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (282583630032153785227717350660324105251/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (707489296823626538144511409226094537143/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (707489296823626538144511409226094537143/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2827896743808022002427609571753809600541/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2827896743808022002427609571753809600541/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0417 BracketBatch0026.bracket0418 (2827896743808022002427609571753809600541/20000000000000000000000000000000000000000) (150188329399709864547035819738045501/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0417 BracketBatch0026.bracket0418
  (2827896743808022002427609571753809600541/20000000000000000000000000000000000000000) (150188329399709864547035819738045501/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0417
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0418
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1414978593647253076289022818452189074283/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1414978593647253076289022818452189074283/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (354259803697866567486566471735258255187/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (354259803697866567486566471735258255187/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (2832017808438719346235288705393222095031/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2832017808438719346235288705393222095031/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0418 BracketBatch0026.bracket0419 (2832017808438719346235288705393222095031/20000000000000000000000000000000000000000) (151053640131887773344963545157535517/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0418 BracketBatch0026.bracket0419
  (2832017808438719346235288705393222095031/20000000000000000000000000000000000000000) (151053640131887773344963545157535517/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0418
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0419
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (283407842958293253989253177388206604149/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (283407842958293253989253177388206604149/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (14191000138754165592047762534609324987/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14191000138754165592047762534609324987/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (567227845733376565830208428080393103889/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (567227845733376565830208428080393103889/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0419 BracketBatch0026.bracket0420 (567227845733376565830208428080393103889/4000000000000000000000000000000000000000) (303845389159953410188867056176687107/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0419 BracketBatch0026.bracket0420
  (567227845733376565830208428080393103889/4000000000000000000000000000000000000000) (303845389159953410188867056176687107/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0419
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0420
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1419100013875416559204776253460932498697/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1419100013875416559204776253460932498697/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (14211609911812400312022446486229393419/100000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14211609911812400312022446486229393419/100000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (2840261005056656590407020902083871840597/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2840261005056656590407020902083871840597/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0420 BracketBatch0026.bracket0421 (2840261005056656590407020902083871840597/20000000000000000000000000000000000000000) (305591007312240367387873762077746457/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0420 BracketBatch0026.bracket0421
  (2840261005056656590407020902083871840597/20000000000000000000000000000000000000000) (305591007312240367387873762077746457/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0420
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0421
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1421160991181240031202244648622939341897/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1421160991181240031202244648622939341897/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (355805536747800259774722430230678368909/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (355805536747800259774722430230678368909/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (2844383138172441070301134369545652817533/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2844383138172441070301134369545652817533/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0421 BracketBatch0026.bracket0422 (2844383138172441070301134369545652817533/20000000000000000000000000000000000000000) (30734415657857159286473238725506901/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0421 BracketBatch0026.bracket0422
  (2844383138172441070301134369545652817533/20000000000000000000000000000000000000000) (30734415657857159286473238725506901/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0421
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0422
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0065.rows BesselBatch0065.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1423222146991201039098889720922713475633/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1423222146991201039098889720922713475633/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (89080217599230777080246984299470321997/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89080217599230777080246984299470321997/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (569701125715778694476568293942847725517/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (569701125715778694476568293942847725517/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0422 BracketBatch0026.bracket0423 (569701125715778694476568293942847725517/4000000000000000000000000000000000000000) (309104858850541612882335322981211233/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0422 BracketBatch0026.bracket0423
  (569701125715778694476568293942847725517/4000000000000000000000000000000000000000) (309104858850541612882335322981211233/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0422
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0423
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1425283481587692433283951748791525151949/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1425283481587692433283951748791525151949/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0066.rows BesselBatch0066.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1427344995253235792809858342947420301271/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1427344995253235792809858342947420301271/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0521.rows BesselBatch0521.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0522.rows BesselBatch0522.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (142631423842046411304690504586947272661/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (142631423842046411304690504586947272661/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0052.rows ScalarLogs0052.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0026.bracket0423 BracketBatch0026.bracket0424 (142631423842046411304690504586947272661/1000000000000000000000000000000000000000) (310873136053415549787522061441071627/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0026.bracket0423 BracketBatch0026.bracket0424
  (142631423842046411304690504586947272661/1000000000000000000000000000000000000000) (310873136053415549787522061441071627/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0423
