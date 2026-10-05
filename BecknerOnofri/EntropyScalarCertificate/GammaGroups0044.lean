module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0055
public import BecknerOnofri.EntropyScalarCertificate.Bessel0056
public import BecknerOnofri.EntropyScalarCertificate.Bessel0516
public import BecknerOnofri.EntropyScalarCertificate.Bessel0517
public import BecknerOnofri.EntropyScalarCertificate.Brackets0022
public import BecknerOnofri.EntropyScalarCertificate.Logs0044
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0352
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (255871398295096375560520750437467060507/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (255871398295096375560520750437467060507/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (80087905385559083132395546968281281159/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (80087905385559083132395546968281281159/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (2560763477644427207920932503679835801079/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2560763477644427207920932503679835801079/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0352 BracketBatch0022.bracket0353 (2560763477644427207920932503679835801079/20000000000000000000000000000000000000000) (202928591316651383360824242706018157/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0352 BracketBatch0022.bracket0353
  (2560763477644427207920932503679835801079/20000000000000000000000000000000000000000) (202928591316651383360824242706018157/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0352
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0353
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1281406486168945330118328751492500498541/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1281406486168945330118328751492500498541/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (641728070226682159192349820817863774349/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (641728070226682159192349820817863774349/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2564862626622309648503028393128228047239/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2564862626622309648503028393128228047239/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0353 BracketBatch0022.bracket0354 (2564862626622309648503028393128228047239/20000000000000000000000000000000000000000) (4084354796383832356613947166291217/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0353 BracketBatch0022.bracket0354
  (2564862626622309648503028393128228047239/20000000000000000000000000000000000000000) (4084354796383832356613947166291217/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0353
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0354
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (256691228090672863676939928327145509739/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (256691228090672863676939928327145509739/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1285505954602909562920076865308500689837/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1285505954602909562920076865308500689837/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (642240523764068470326194126736057059633/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (642240523764068470326194126736057059633/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0354 BracketBatch0022.bracket0355 (642240523764068470326194126736057059633/5000000000000000000000000000000000000000) (12844564301755908677333973686282937/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0354 BracketBatch0022.bracket0355
  (642240523764068470326194126736057059633/5000000000000000000000000000000000000000) (12844564301755908677333973686282937/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0354
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0355
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (642752977301454781460038432654250344917/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (642752977301454781460038432654250344917/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (160944491111483158820717803793190570367/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (160944491111483158820717803793190570367/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (257306188349477483348581929565402525277/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (257306188349477483348581929565402525277/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0355 BracketBatch0022.bracket0356 (257306188349477483348581929565402525277/2000000000000000000000000000000000000000) (206814478003675488249981345324758077/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0355 BracketBatch0022.bracket0356
  (257306188349477483348581929565402525277/2000000000000000000000000000000000000000) (206814478003675488249981345324758077/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0355
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0356
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1287555928891865270565742430345524562933/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1287555928891865270565742430345524562933/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (322401515898657337970885961824735986233/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (322401515898657337970885961824735986233/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (515432398497298924489857255528893701573/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (515432398497298924489857255528893701573/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0356 BracketBatch0022.bracket0357 (515432398497298924489857255528893701573/4000000000000000000000000000000000000000) (104061053519604686036251007071664711/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0356 BracketBatch0022.bracket0357
  (515432398497298924489857255528893701573/4000000000000000000000000000000000000000) (104061053519604686036251007071664711/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0356
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0357
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1289606063594629351883543847298943944929/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1289606063594629351883543847298943944929/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1291656358985713638551330639800693158203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1291656358985713638551330639800693158203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (645315605645085747608718621774909275783/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (645315605645085747608718621774909275783/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0357 BracketBatch0022.bracket0358 (645315605645085747608718621774909275783/5000000000000000000000000000000000000000) (209435935660940651838135789171775637/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0357 BracketBatch0022.bracket0358
  (645315605645085747608718621774909275783/5000000000000000000000000000000000000000) (209435935660940651838135789171775637/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0357
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0358
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0055.rows BesselBatch0055.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (6458281794928568192756653199003465791/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6458281794928568192756653199003465791/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (323426703834936025239153571148713353527/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (323426703834936025239153571148713353527/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (646340793581364434876986231098886643077/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (646340793581364434876986231098886643077/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0358 BracketBatch0022.bracket0359 (646340793581364434876986231098886643077/5000000000000000000000000000000000000000) (5268899590702333862553503486058577/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0358 BracketBatch0022.bracket0359
  (646340793581364434876986231098886643077/5000000000000000000000000000000000000000) (5268899590702333862553503486058577/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0358
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0359
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (258741363067948820191322856918970682821/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (258741363067948820191322856918970682821/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0056.rows BesselBatch0056.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1295757432931461065988883075657001918837/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1295757432931461065988883075657001918837/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0516.rows BesselBatch0516.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0517.rows BesselBatch0517.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (1294732124135602583472748680125927666471/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1294732124135602583472748680125927666471/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0044.rows ScalarLogs0044.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0022.bracket0359 BracketBatch0022.bracket0360 (1294732124135602583472748680125927666471/10000000000000000000000000000000000000000) (212082270732881100846808976741909617/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0022.bracket0359 BracketBatch0022.bracket0360
  (1294732124135602583472748680125927666471/10000000000000000000000000000000000000000) (212082270732881100846808976741909617/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0359
