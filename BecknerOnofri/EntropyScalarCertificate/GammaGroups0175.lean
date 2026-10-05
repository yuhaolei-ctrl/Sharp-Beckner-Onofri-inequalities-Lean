module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0218
public import BecknerOnofri.EntropyScalarCertificate.Bessel0219
public import BecknerOnofri.EntropyScalarCertificate.Bessel0220
public import BecknerOnofri.EntropyScalarCertificate.Bessel0598
public import BecknerOnofri.EntropyScalarCertificate.Brackets0087
public import BecknerOnofri.EntropyScalarCertificate.Brackets0088
public import BecknerOnofri.EntropyScalarCertificate.Logs0175
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1400
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (8346201378376731637877632833726305669833/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8346201378376731637877632833726305669833/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (16701003565854381377396723937542057338203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16701003565854381377396723937542057338203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (33393406322607844653151989604994668677869/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33393406322607844653151989604994668677869/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1400 BracketBatch0087.bracket1401 (33393406322607844653151989604994668677869/20000000000000000000000000000000000000000) (625016277273636131171979143303209355661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1400 BracketBatch0087.bracket1401
  (33393406322607844653151989604994668677869/20000000000000000000000000000000000000000) (625016277273636131171979143303209355661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1400
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1401
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0218.rows BesselBatch0218.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (83505017829271906886983619687710286691/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (83505017829271906886983619687710286691/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (3341922889448535726966007661436014155817/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3341922889448535726966007661436014155817/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (6682123602619412002445352448944425623457/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6682123602619412002445352448944425623457/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1401 BracketBatch0087.bracket1402 (6682123602619412002445352448944425623457/4000000000000000000000000000000000000000) (625493062356160314772535775580955551331/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1401 BracketBatch0087.bracket1402
  (6682123602619412002445352448944425623457/4000000000000000000000000000000000000000) (625493062356160314772535775580955551331/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1401
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1402
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (8354807223621339317415019153590035389541/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8354807223621339317415019153590035389541/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (3343647084050515001976776924034717262721/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3343647084050515001976776924034717262721/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (33427849867495253644713922927353657092687/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33427849867495253644713922927353657092687/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1402 BracketBatch0087.bracket1403 (33427849867495253644713922927353657092687/20000000000000000000000000000000000000000) (31298515930841947429129652148420965653/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1402 BracketBatch0087.bracket1403
  (33427849867495253644713922927353657092687/20000000000000000000000000000000000000000) (31298515930841947429129652148420965653/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1402
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1403
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (8359117710126287504941942310086793156801/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8359117710126287504941942310086793156801/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (16726866504266139308681048172033993582059/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16726866504266139308681048172033993582059/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (33445101924518714318564932792207579895661/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33445101924518714318564932792207579895661/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1403 BracketBatch0087.bracket1404 (33445101924518714318564932792207579895661/20000000000000000000000000000000000000000) (626448046742404100496030754385798101441/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1403 BracketBatch0087.bracket1404
  (33445101924518714318564932792207579895661/20000000000000000000000000000000000000000) (626448046742404100496030754385798101441/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1403
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1404
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2090858313033267413585131021504249197757/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2090858313033267413585131021504249197757/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (8367753859356715293659739141927210039771/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8367753859356715293659739141927210039771/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (16731187111489784948000263227944206830799/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16731187111489784948000263227944206830799/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1404 BracketBatch0087.bracket1405 (16731187111489784948000263227944206830799/10000000000000000000000000000000000000000) (62692624742086278828513488851934899817/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1404 BracketBatch0087.bracket1405
  (16731187111489784948000263227944206830799/10000000000000000000000000000000000000000) (62692624742086278828513488851934899817/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1404
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1405
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (16735507718713430587319478283854420079539/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16735507718713430587319478283854420079539/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (8372079541536320020490945998618584786247/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8372079541536320020490945998618584786247/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (33479666801786070628301370281091589652033/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33479666801786070628301370281091589652033/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1405 BracketBatch0087.bracket1406 (33479666801786070628301370281091589652033/20000000000000000000000000000000000000000) (31370246067074974950539548345236597437/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1405 BracketBatch0087.bracket1406
  (33479666801786070628301370281091589652033/20000000000000000000000000000000000000000) (31370246067074974950539548345236597437/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1405
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1406
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (16744159083072640040981891997237169572491/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16744159083072640040981891997237169572491/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (16752820616870233378383975433697852422719/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16752820616870233378383975433697852422719/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (3349697969994287341936586743093502199521/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3349697969994287341936586743093502199521/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1406 BracketBatch0087.bracket1407 (3349697969994287341936586743093502199521/2000000000000000000000000000000000000000) (125576813838975742648814395104695664113/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1406 BracketBatch0087.bracket1407
  (3349697969994287341936586743093502199521/2000000000000000000000000000000000000000) (125576813838975742648814395104695664113/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1406
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1407
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0219.rows BesselBatch0219.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (4188205154217558344595993858424463105679/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4188205154217558344595993858424463105679/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0220.rows BesselBatch0220.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (16761492339681093683480121274195888124253/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16761492339681093683480121274195888124253/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0598.rows BesselBatch0598.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (33514312956551327061864096707893740546969/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (33514312956551327061864096707893740546969/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0175.rows ScalarLogs0175.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0087.bracket1407 BracketBatch0088.bracket1408 (33514312956551327061864096707893740546969/20000000000000000000000000000000000000000) (628363691672847434109717907669031178153/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0087.bracket1407 BracketBatch0088.bracket1408
  (33514312956551327061864096707893740546969/20000000000000000000000000000000000000000) (628363691672847434109717907669031178153/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1407
