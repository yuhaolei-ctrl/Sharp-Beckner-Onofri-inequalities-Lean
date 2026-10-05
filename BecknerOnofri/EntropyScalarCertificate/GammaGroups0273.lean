module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0341
public import BecknerOnofri.EntropyScalarCertificate.Bessel0342
public import BecknerOnofri.EntropyScalarCertificate.Bessel0659
public import BecknerOnofri.EntropyScalarCertificate.Bessel0660
public import BecknerOnofri.EntropyScalarCertificate.Brackets0136
public import BecknerOnofri.EntropyScalarCertificate.Brackets0137
public import BecknerOnofri.EntropyScalarCertificate.Logs0273
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2184
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (86343709657172305410086466632408013615229/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (86343709657172305410086466632408013615229/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (86633707507586334831732783557590483677263/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (86633707507586334831732783557590483677263/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (43244354291189660060454812547499624323123/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43244354291189660060454812547499624323123/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2184 BracketBatch0136.bracket2185 (43244354291189660060454812547499624323123/5000000000000000000000000000000000000000) (2570633612060908861639731863217317627037/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2184 BracketBatch0136.bracket2185
  (43244354291189660060454812547499624323123/5000000000000000000000000000000000000000) (2570633612060908861639731863217317627037/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2184
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2185
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (4331685375379316741586639177879524183863/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4331685375379316741586639177879524183863/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (695405546341954997423338171591553372629/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (695405546341954997423338171591553372629/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (34711880160066141901930011001306931051177/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (34711880160066141901930011001306931051177/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2185 BracketBatch0136.bracket2186 (34711880160066141901930011001306931051177/4000000000000000000000000000000000000000) (2575029543779988655821576279583800383227/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2185 BracketBatch0136.bracket2186
  (34711880160066141901930011001306931051177/4000000000000000000000000000000000000000) (2575029543779988655821576279583800383227/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2185
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2186
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (43462846646372187338958635724472085789311/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43462846646372187338958635724472085789311/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (17443937501039250685856549370609632272189/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (17443937501039250685856549370609632272189/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (174145380797940628107200018301992332939567/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (174145380797940628107200018301992332939567/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2186 BracketBatch0136.bracket2187 (174145380797940628107200018301992332939567/20000000000000000000000000000000000000000) (515888368720386514056777496743319193009/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2186 BracketBatch0136.bracket2187
  (174145380797940628107200018301992332939567/20000000000000000000000000000000000000000) (515888368720386514056777496743319193009/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2186
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2187
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (43609843752598126714641373426524080680471/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (43609843752598126714641373426524080680471/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (43757855460075607332382452410566958046087/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43757855460075607332382452410566958046087/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (43683849606336867023511912918545519363279/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (43683849606336867023511912918545519363279/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2187 BracketBatch0136.bracket2188 (43683849606336867023511912918545519363279/5000000000000000000000000000000000000000) (2583870626079482008328763585520304110301/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2187 BracketBatch0136.bracket2188
  (43683849606336867023511912918545519363279/5000000000000000000000000000000000000000) (2583870626079482008328763585520304110301/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2187
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2188
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (87515710920151214664764904821133916092171/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (87515710920151214664764904821133916092171/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (87813784600368203622214182331890723621047/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (87813784600368203622214182331890723621047/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (87664747760259709143489543576512319856609/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (87664747760259709143489543576512319856609/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2188 BracketBatch0136.bracket2189 (87664747760259709143489543576512319856609/10000000000000000000000000000000000000000) (2588316006946012718366436465326837825279/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2188 BracketBatch0136.bracket2189
  (87664747760259709143489543576512319856609/10000000000000000000000000000000000000000) (2588316006946012718366436465326837825279/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2188
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2189
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (21953446150092050905553545582972680905261/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21953446150092050905553545582972680905261/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (44056964950574017417878667191805186841657/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44056964950574017417878667191805186841657/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (87963857250758119228985758357750548652179/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (87963857250758119228985758357750548652179/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2189 BracketBatch0136.bracket2190 (87963857250758119228985758357750548652179/10000000000000000000000000000000000000000) (2592778103131355801401922338716054803967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2189 BracketBatch0136.bracket2190
  (87963857250758119228985758357750548652179/10000000000000000000000000000000000000000) (2592778103131355801401922338716054803967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2189
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2190
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (88113929901148034835757334383610373683311/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (88113929901148034835757334383610373683311/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (88416168475429925752922663116218783100259/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (88416168475429925752922663116218783100259/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (17653009837657796058867999749982915678357/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (17653009837657796058867999749982915678357/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2190 BracketBatch0136.bracket2191 (17653009837657796058867999749982915678357/2000000000000000000000000000000000000000) (1298628516388938982020151392220468028241/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2190 BracketBatch0136.bracket2191
  (17653009837657796058867999749982915678357/2000000000000000000000000000000000000000) (1298628516388938982020151392220468028241/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2190
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2191
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (2763005264857185179778833222381836971883/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2763005264857185179778833222381836971883/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (88720522278994950742351186174238587731757/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (88720522278994950742351186174238587731757/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (177136690754424876495273849290457370832013/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (177136690754424876495273849290457370832013/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0273.rows ScalarLogs0273.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2191 BracketBatch0137.bracket2192 (177136690754424876495273849290457370832013/20000000000000000000000000000000000000000) (2601752915256825989940197464291148807317/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2191 BracketBatch0137.bracket2192
  (177136690754424876495273849290457370832013/20000000000000000000000000000000000000000) (2601752915256825989940197464291148807317/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2191
