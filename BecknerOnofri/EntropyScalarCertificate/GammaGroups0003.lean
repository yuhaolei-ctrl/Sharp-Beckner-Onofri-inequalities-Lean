module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0003
public import BecknerOnofri.EntropyScalarCertificate.Bessel0004
public import BecknerOnofri.EntropyScalarCertificate.Bessel0005
public import BecknerOnofri.EntropyScalarCertificate.Bessel0490
public import BecknerOnofri.EntropyScalarCertificate.Bessel0491
public import BecknerOnofri.EntropyScalarCertificate.Brackets0001
public import BecknerOnofri.EntropyScalarCertificate.Brackets0002
public import BecknerOnofri.EntropyScalarCertificate.Logs0003
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0024
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (79787095153083237019430820508057528671/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (79787095153083237019430820508057528671/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (159699956038158866498440314110901941571/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (159699956038158866498440314110901941571/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (319274146344325340537301955127016998913/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (319274146344325340537301955127016998913/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0024 BracketBatch0001.bracket0025 (319274146344325340537301955127016998913/5000000000000000000000000000000000000000) (12823477972784583291382849779116679/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0024 BracketBatch0001.bracket0025
  (319274146344325340537301955127016998913/5000000000000000000000000000000000000000) (12823477972784583291382849779116679/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0024
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0025
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0003.rows BesselBatch0003.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (638799824152635465993761256443607766281/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (638799824152635465993761256443607766281/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (159825722979067896944215024405733430657/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (159825722979067896944215024405733430657/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (1278102716068907053770621354066541488909/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1278102716068907053770621354066541488909/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0025 BracketBatch0001.bracket0026 (1278102716068907053770621354066541488909/20000000000000000000000000000000000000000) (803993748954245027946771006514677/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0025 BracketBatch0001.bracket0026
  (1278102716068907053770621354066541488909/20000000000000000000000000000000000000000) (803993748954245027946771006514677/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0025
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0026
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (5114423135330172702214880780983469781/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5114423135330172702214880780983469781/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (63980596451945309895711739934205358539/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (63980596451945309895711739934205358539/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0490.rows BesselBatch0490.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (255821771287144937346795499392997461603/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (255821771287144937346795499392997461603/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0026 BracketBatch0001.bracket0027 (255821771287144937346795499392997461603/4000000000000000000000000000000000000000) (6452208686908497700369012840575217/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0026 BracketBatch0001.bracket0027
  (255821771287144937346795499392997461603/4000000000000000000000000000000000000000) (6452208686908497700369012840575217/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0026
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0027
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (639805964519453098957117399342053585387/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (639805964519453098957117399342053585387/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (40019315122878690114932382191568763309/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (40019315122878690114932382191568763309/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (1280115006485512140796035514407153798331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1280115006485512140796035514407153798331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0027 BracketBatch0001.bracket0028 (1280115006485512140796035514407153798331/20000000000000000000000000000000000000000) (12945030294720854688583906541539323/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0027 BracketBatch0001.bracket0028
  (1280115006485512140796035514407153798331/20000000000000000000000000000000000000000) (12945030294720854688583906541539323/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0027
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0028
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (640309041966059041838918115065100212941/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (640309041966059041838918115065100212941/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (12816242485199373274958448497030872043/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12816242485199373274958448497030872043/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1281121166226027705586840539916643815091/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1281121166226027705586840539916643815091/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0028 BracketBatch0001.bracket0029 (1281121166226027705586840539916643815091/20000000000000000000000000000000000000000) (6492869448194151395274268981562409/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0028 BracketBatch0001.bracket0029
  (1281121166226027705586840539916643815091/20000000000000000000000000000000000000000) (6492869448194151395274268981562409/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0028
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0029
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (640812124259968663747922424851543602147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (640812124259968663747922424851543602147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (320657605702530708600175611769345499281/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (320657605702530708600175611769345499281/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (1282127335665030080948273648390234600709/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1282127335665030080948273648390234600709/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0029 BracketBatch0001.bracket0030 (1282127335665030080948273648390234600709/20000000000000000000000000000000000000000) (1302654332934790670469600269530579/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0029 BracketBatch0001.bracket0030
  (1282127335665030080948273648390234600709/20000000000000000000000000000000000000000) (1302654332934790670469600269530579/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0029
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0030
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (641315211405061417200351223538690998559/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (641315211405061417200351223538690998559/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (128363660681043392014458506041935805173/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128363660681043392014458506041935805173/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (160391689351284797159080469218546253053/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (160391689351284797159080469218546253053/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0030 BracketBatch0001.bracket0031 (160391689351284797159080469218546253053/2500000000000000000000000000000000000000) (13067443744248000525804290979760581/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0030 BracketBatch0001.bracket0031
  (160391689351284797159080469218546253053/2500000000000000000000000000000000000000) (13067443744248000525804290979760581/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0030
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0031
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0004.rows BesselBatch0004.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (320909151702608480036146265104839512931/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (320909151702608480036146265104839512931/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0005.rows BesselBatch0005.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (642321400264315155769028836924654583859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (642321400264315155769028836924654583859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0491.rows BesselBatch0491.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (1284139703669532115841321367134333609721/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1284139703669532115841321367134333609721/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0003.rows ScalarLogs0003.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0001.bracket0031 BracketBatch0002.bracket0032 (1284139703669532115841321367134333609721/20000000000000000000000000000000000000000) (3277110072964172506904809240459653/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0001.bracket0031 BracketBatch0002.bracket0032
  (1284139703669532115841321367134333609721/20000000000000000000000000000000000000000) (3277110072964172506904809240459653/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0031
