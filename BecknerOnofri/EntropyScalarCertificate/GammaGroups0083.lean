module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0103
public import BecknerOnofri.EntropyScalarCertificate.Bessel0104
public import BecknerOnofri.EntropyScalarCertificate.Bessel0105
public import BecknerOnofri.EntropyScalarCertificate.Bessel0540
public import BecknerOnofri.EntropyScalarCertificate.Bessel0541
public import BecknerOnofri.EntropyScalarCertificate.Brackets0041
public import BecknerOnofri.EntropyScalarCertificate.Brackets0042
public import BecknerOnofri.EntropyScalarCertificate.Logs0083
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0664
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (192796595452484260403717775234971100049/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (192796595452484260403717775234971100049/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (482519800401370862897358621431028325067/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (482519800401370862897358621431028325067/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1929022578065163027813306119036912150379/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1929022578065163027813306119036912150379/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0664 BracketBatch0041.bracket0665 (1929022578065163027813306119036912150379/10000000000000000000000000000000000000000) (1014631290640578217904588181767750649/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0664 BracketBatch0041.bracket0665
  (1929022578065163027813306119036912150379/10000000000000000000000000000000000000000) (1014631290640578217904588181767750649/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0664
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0665
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0103.rows BesselBatch0103.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (386015840321096690317886897144822660053/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (386015840321096690317886897144822660053/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1932192700500888201741605396190989915811/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1932192700500888201741605396190989915811/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (965567975526592913332759970478775804019/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (965567975526592913332759970478775804019/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0665 BracketBatch0041.bracket0666 (965567975526592913332759970478775804019/5000000000000000000000000000000000000000) (1018959563732148694267031079718892957/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0665 BracketBatch0041.bracket0666
  (965567975526592913332759970478775804019/5000000000000000000000000000000000000000) (1018959563732148694267031079718892957/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0665
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0666
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (60381021890652756304425168630968434869/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (60381021890652756304425168630968434869/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1934306451532348740245236309297564252013/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1934306451532348740245236309297564252013/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0540.rows BesselBatch0540.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (3866499152033236941986841705488554167821/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3866499152033236941986841705488554167821/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0666 BracketBatch0041.bracket0667 (3866499152033236941986841705488554167821/20000000000000000000000000000000000000000) (1023301767430761481998200575447517579/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0666 BracketBatch0041.bracket0667
  (3866499152033236941986841705488554167821/20000000000000000000000000000000000000000) (1023301767430761481998200575447517579/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0666
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0667
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (193430645153234874024523630929756425201/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (193430645153234874024523630929756425201/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1936420455021350250643578667469853780963/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1936420455021350250643578667469853780963/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (3870726906553698990888814976767418032973/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3870726906553698990888814976767418032973/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0667 BracketBatch0041.bracket0668 (3870726906553698990888814976767418032973/20000000000000000000000000000000000000000) (256914483065467349517718208610414767/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0667 BracketBatch0041.bracket0668
  (3870726906553698990888814976767418032973/20000000000000000000000000000000000000000) (256914483065467349517718208610414767/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0667
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0668
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (12102627843883439066522366671686586131/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12102627843883439066522366671686586131/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (969267355644785758994217834065616803209/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (969267355644785758994217834065616803209/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1937477583155460884316007167800543693689/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1937477583155460884316007167800543693689/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0668 BracketBatch0041.bracket0669 (1937477583155460884316007167800543693689/10000000000000000000000000000000000000000) (1032028088787980327090797926341547157/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0668 BracketBatch0041.bracket0669
  (1937477583155460884316007167800543693689/10000000000000000000000000000000000000000) (1032028088787980327090797926341547157/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0668
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0669
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (387706942257914303597687133626246721283/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (387706942257914303597687133626246721283/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (970324610329442616464838516162103548017/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (970324610329442616464838516162103548017/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (3879183931948456750918112700455440702449/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3879183931948456750918112700455440702449/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0669 BracketBatch0041.bracket0670 (3879183931948456750918112700455440702449/20000000000000000000000000000000000000000) (129551533451084231183406833220315273/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0669 BracketBatch0041.bracket0670
  (3879183931948456750918112700455440702449/20000000000000000000000000000000000000000) (129551533451084231183406833220315273/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0669
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0670
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (1940649220658885232929677032324207096031/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1940649220658885232929677032324207096031/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (97138199172567914808907513746287261803/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (97138199172567914808907513746287261803/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (3883413204110243529107827307249952332091/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3883413204110243529107827307249952332091/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0670 BracketBatch0041.bracket0671 (3883413204110243529107827307249952332091/20000000000000000000000000000000000000000) (1040810499360617894335006863224616627/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0670 BracketBatch0041.bracket0671
  (3883413204110243529107827307249952332091/20000000000000000000000000000000000000000) (1040810499360617894335006863224616627/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0670
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0671
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0104.rows BesselBatch0104.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1942763983451358296178150274925745236057/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1942763983451358296178150274925745236057/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1944878999989252123342717700509077241207/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1944878999989252123342717700509077241207/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (242977686465038151220054248464676404829/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (242977686465038151220054248464676404829/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0083.rows ScalarLogs0083.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0041.bracket0671 BracketBatch0042.bracket0672 (242977686465038151220054248464676404829/1250000000000000000000000000000000000000) (522611407358792708627346679973192981/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0041.bracket0671 BracketBatch0042.bracket0672
  (242977686465038151220054248464676404829/1250000000000000000000000000000000000000) (522611407358792708627346679973192981/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0671
