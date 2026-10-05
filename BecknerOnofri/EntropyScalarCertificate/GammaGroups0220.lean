module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0275
public import BecknerOnofri.EntropyScalarCertificate.Bessel0276
public import BecknerOnofri.EntropyScalarCertificate.Bessel0626
public import BecknerOnofri.EntropyScalarCertificate.Bessel0627
public import BecknerOnofri.EntropyScalarCertificate.Brackets0110
public import BecknerOnofri.EntropyScalarCertificate.Logs0220
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1760
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (4126054692868410191436796994064722924747/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4126054692868410191436796994064722924747/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (20644246931153492956507788528793050583669/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20644246931153492956507788528793050583669/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (10318630098873885978422943374779166301851/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10318630098873885978422943374779166301851/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1760 BracketBatch0110.bracket1761 (10318630098873885978422943374779166301851/5000000000000000000000000000000000000000) (416709527052303066972295946652503402963/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1760 BracketBatch0110.bracket1761
  (10318630098873885978422943374779166301851/5000000000000000000000000000000000000000) (416709527052303066972295946652503402963/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1760
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1761
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (10322123465576746478253894264396525291833/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10322123465576746478253894264396525291833/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (1032912103759971475171445436875437764721/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1032912103759971475171445436875437764721/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (20651244503176461229968348633150902939043/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20651244503176461229968348633150902939043/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1761 BracketBatch0110.bracket1762 (20651244503176461229968348633150902939043/10000000000000000000000000000000000000000) (83412168598726291180424812835442542127/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1761 BracketBatch0110.bracket1762
  (20651244503176461229968348633150902939043/10000000000000000000000000000000000000000) (83412168598726291180424812835442542127/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1761
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1762
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (20658242075199429503428908737508755294417/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20658242075199429503428908737508755294417/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (10336129473933504168375640519424759670517/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10336129473933504168375640519424759670517/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (41330501023066437840180189776358274635451/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41330501023066437840180189776358274635451/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1762 BracketBatch0110.bracket1763 (41330501023066437840180189776358274635451/20000000000000000000000000000000000000000) (834825142223038191243514470704790374933/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1762 BracketBatch0110.bracket1763
  (41330501023066437840180189776358274635451/20000000000000000000000000000000000000000) (834825142223038191243514470704790374933/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1762
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1763
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (20672258947867008336751281038849519341031/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20672258947867008336751281038849519341031/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (10343148800349038014003822624953906801163/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10343148800349038014003822624953906801163/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (41358556548565084364758926288757332943357/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41358556548565084364758926288757332943357/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1763 BracketBatch0110.bracket1764 (41358556548565084364758926288757332943357/20000000000000000000000000000000000000000) (835529424170621569888708632388571468743/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1763 BracketBatch0110.bracket1764
  (41358556548565084364758926288757332943357/20000000000000000000000000000000000000000) (835529424170621569888708632388571468743/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1763
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1764
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (20686297600698076028007645249907813602323/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20686297600698076028007645249907813602323/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (10350179042694872875569749022179219264019/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10350179042694872875569749022179219264019/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (41386655686087821779147143294266252130361/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41386655686087821779147143294266252130361/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1764 BracketBatch0110.bracket1765 (41386655686087821779147143294266252130361/20000000000000000000000000000000000000000) (836234533191371579774761961390333797941/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1764 BracketBatch0110.bracket1765
  (41386655686087821779147143294266252130361/20000000000000000000000000000000000000000) (836234533191371579774761961390333797941/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1764
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1765
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (4140071617077949150227899608871687705607/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4140071617077949150227899608871687705607/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (20714440453794967594417637048107434318859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20714440453794967594417637048107434318859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (20707399269592356672778567546232936423447/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20707399269592356672778567546232936423447/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1765 BracketBatch0110.bracket1766 (20707399269592356672778567546232936423447/10000000000000000000000000000000000000000) (10461755883116524202464352058700717467/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1765 BracketBatch0110.bracket1766
  (20707399269592356672778567546232936423447/10000000000000000000000000000000000000000) (10461755883116524202464352058700717467/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1765
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1766
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0275.rows BesselBatch0275.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (2589305056724370949302204631013429289857/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2589305056724370949302204631013429289857/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (5182136189480775357115228677636631903503/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5182136189480775357115228677636631903503/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (10360746302929517255719637939663490483217/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10360746302929517255719637939663490483217/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1766 BracketBatch0110.bracket1767 (10360746302929517255719637939663490483217/5000000000000000000000000000000000000000) (418823618955593905236588974132427132569/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1766 BracketBatch0110.bracket1767
  (10360746302929517255719637939663490483217/5000000000000000000000000000000000000000) (418823618955593905236588974132427132569/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1766
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1767
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (20728544757923101428460914710546527614009/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20728544757923101428460914710546527614009/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0276.rows BesselBatch0276.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (20742671049940492344299525297514041665721/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20742671049940492344299525297514041665721/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0626.rows BesselBatch0626.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0627.rows BesselBatch0627.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (4147121580786359377276044000806056927973/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4147121580786359377276044000806056927973/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0220.rows ScalarLogs0220.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0110.bracket1767 BracketBatch0110.bracket1768 (4147121580786359377276044000806056927973/2000000000000000000000000000000000000000) (419177418173186063384925751526959537801/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0110.bracket1767 BracketBatch0110.bracket1768
  (4147121580786359377276044000806056927973/2000000000000000000000000000000000000000) (419177418173186063384925751526959537801/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1767
