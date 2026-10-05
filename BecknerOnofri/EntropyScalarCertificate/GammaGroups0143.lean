module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0178
public import BecknerOnofri.EntropyScalarCertificate.Bessel0179
public import BecknerOnofri.EntropyScalarCertificate.Bessel0180
public import BecknerOnofri.EntropyScalarCertificate.Bessel0578
public import BecknerOnofri.EntropyScalarCertificate.Brackets0071
public import BecknerOnofri.EntropyScalarCertificate.Brackets0072
public import BecknerOnofri.EntropyScalarCertificate.Logs0143
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1144
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4067545689713054607881345037940162513509/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4067545689713054607881345037940162513509/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (2039379061163701358232713332641798058207/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2039379061163701358232713332641798058207/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (8146303812040457324346771703223758629923/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8146303812040457324346771703223758629923/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1144 BracketBatch0071.bracket1145 (8146303812040457324346771703223758629923/10000000000000000000000000000000000000000) (145777857271884685221272136149358660509/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1144 BracketBatch0071.bracket1145
  (8146303812040457324346771703223758629923/10000000000000000000000000000000000000000) (145777857271884685221272136149358660509/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1144
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1145
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0178.rows BesselBatch0178.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (326300649786192217317234133222687689313/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (326300649786192217317234133222687689313/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (4090011363297117053675282100360202590407/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4090011363297117053675282100360202590407/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (16337538971249039540281417531287597413639/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16337538971249039540281417531287597413639/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1145 BracketBatch0071.bracket1146 (16337538971249039540281417531287597413639/20000000000000000000000000000000000000000) (146834772540349640259790059228752827227/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1145 BracketBatch0071.bracket1146
  (16337538971249039540281417531287597413639/20000000000000000000000000000000000000000) (146834772540349640259790059228752827227/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1145
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1146
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (8180022726594234107350564200720405180811/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8180022726594234107350564200720405180811/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1025326435412649255873734909700959248229/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1025326435412649255873734909700959248229/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (16382634209895428154340443478328079166643/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16382634209895428154340443478328079166643/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1146 BracketBatch0071.bracket1147 (16382634209895428154340443478328079166643/20000000000000000000000000000000000000000) (36974587070981997326324876784189439907/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1146 BracketBatch0071.bracket1147
  (16382634209895428154340443478328079166643/20000000000000000000000000000000000000000) (36974587070981997326324876784189439907/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1146
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1147
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (8202611483301194046989879277607673985829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8202611483301194046989879277607673985829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (822528318013542129889153191831431151367/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (822528318013542129889153191831431151367/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (16427894663436615345881411195921985499499/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16427894663436615345881411195921985499499/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1147 BracketBatch0071.bracket1148 (16427894663436615345881411195921985499499/20000000000000000000000000000000000000000) (148968626321620516232313232116421341199/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1147 BracketBatch0071.bracket1148
  (16427894663436615345881411195921985499499/20000000000000000000000000000000000000000) (148968626321620516232313232116421341199/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1147
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1148
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (8225283180135421298891531918314311513667/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8225283180135421298891531918314311513667/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8248038489864110360975067837131207482057/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8248038489864110360975067837131207482057/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (4118330417499882914966649938861379748931/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4118330417499882914966649938861379748931/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1148 BracketBatch0071.bracket1149 (4118330417499882914966649938861379748931/5000000000000000000000000000000000000000) (150045648822392566046231824750914418919/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1148 BracketBatch0071.bracket1149
  (4118330417499882914966649938861379748931/5000000000000000000000000000000000000000) (150045648822392566046231824750914418919/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1148
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1149
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (4124019244932055180487533918565603741027/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4124019244932055180487533918565603741027/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (8270878092768244140356575509867115320337/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8270878092768244140356575509867115320337/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (16518916582632354501331643346998322802391/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16518916582632354501331643346998322802391/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1149 BracketBatch0071.bracket1150 (16518916582632354501331643346998322802391/20000000000000000000000000000000000000000) (151129458309579787715636015174580836757/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1149 BracketBatch0071.bracket1150
  (16518916582632354501331643346998322802391/20000000000000000000000000000000000000000) (151129458309579787715636015174580836757/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1149
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1150
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (4135439046384122070178287754933557660167/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4135439046384122070178287754933557660167/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (4146901338375384594566283389654705782283/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4146901338375384594566283389654705782283/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (165646807695190133294891422891765268849/200000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (165646807695190133294891422891765268849/200000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1150 BracketBatch0071.bracket1151 (165646807695190133294891422891765268849/200000000000000000000000000000000000000) (152220097665365267688981684514754905293/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1150 BracketBatch0071.bracket1151
  (165646807695190133294891422891765268849/200000000000000000000000000000000000000) (152220097665365267688981684514754905293/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1150
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1151
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0179.rows BesselBatch0179.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (8293802676750769189132566779309411564563/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8293802676750769189132566779309411564563/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0180.rows BesselBatch0180.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (8316812937446653587595607272972971042351/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8316812937446653587595607272972971042351/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0578.rows BesselBatch0578.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (8305307807098711388364087026141191303457/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8305307807098711388364087026141191303457/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0143.rows ScalarLogs0143.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0071.bracket1151 BracketBatch0072.bracket1152 (8305307807098711388364087026141191303457/10000000000000000000000000000000000000000) (38329402533832347794270756514348972427/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0071.bracket1151 BracketBatch0072.bracket1152
  (8305307807098711388364087026141191303457/10000000000000000000000000000000000000000) (38329402533832347794270756514348972427/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1151
