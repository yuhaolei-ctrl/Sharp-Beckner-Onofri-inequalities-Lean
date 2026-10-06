module

public import BecknerOnofri.SpinPressureCertificateInterval

@[expose] public section

/-!
# Soundness of the first-order Taylor models

Lemma 5.20 (lem:section5-scalar-pressure). A model `⟨c₀, c₁, r, ok⟩` encloses `f` at the
offset `s` if `ok` implies `f = a₀ + a₁ s + ρ s²` for some `a₀ ∈ c₀`, `a₁ ∈ c₁`, `ρ ∈ r`.
The statements are pointwise in `s`, so they compose freely; the remainders of the
reciprocal, logarithm and exponential come from the exact identity
`1/(1+q) = 1 - q + q²/(1+q)`, `Real.abs_log_sub_add_sum_range_le` and `Real.exp_bound`.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Real

/-- The offset `s` is admissible for the cell: `s ∈ s1` and `s² ∈ s2`. -/
def Ctx.Adm (x : Ctx) (s : ℝ) : Prop := x.s1.Mem s ∧ x.s2.Mem (s ^ 2)

/-- The model `X` encloses the value `f` at the offset `s`. -/
def TM.Mem (X : TM) (s f : ℝ) : Prop :=
  X.ok = true → ∃ a₀ a₁ ρ : ℝ, X.c0.Mem a₀ ∧ X.c1.Mem a₁ ∧ X.r.Mem ρ ∧
    f = a₀ + a₁ * s + ρ * s ^ 2

namespace TM

variable {x : Ctx} {s : ℝ}

theorem mem_congr {X : TM} {f g : ℝ} (h : X.Mem s f) (hfg : f = g) : X.Mem s g := hfg ▸ h

theorem mem_const {a : Iv} {c : ℝ} (h : a.Mem c) : (const a).Mem s c :=
  fun _ => ⟨c, 0, 0, h, Iv.mem_zero, Iv.mem_zero, by ring⟩

theorem mem_var {t₀ : ℝ} (h : x.mid.Mem t₀) : (var x).Mem s (t₀ + s) :=
  fun _ => ⟨t₀, 1, 0, h, Iv.mem_one, Iv.mem_zero, by ring⟩

theorem mem_add {X Y : TM} {f g : ℝ} (hX : X.Mem s f) (hY : Y.Mem s g) :
    (add X Y).Mem s (f + g) := by
  intro hok
  simp only [add, Bool.and_eq_true] at hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok.1
  obtain ⟨b₀, b₁, σ, k₀, k₁, kr, rfl⟩ := hY hok.2
  exact ⟨a₀ + b₀, a₁ + b₁, ρ + σ, Iv.mem_add h₀ k₀, Iv.mem_add h₁ k₁, Iv.mem_add hr kr,
    by ring⟩

theorem mem_neg {X : TM} {f : ℝ} (hX : X.Mem s f) : (neg X).Mem s (-f) := by
  intro hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  exact ⟨-a₀, -a₁, -ρ, Iv.mem_neg h₀, Iv.mem_neg h₁, Iv.mem_neg hr, by ring⟩

theorem mem_sub {X Y : TM} {f g : ℝ} (hX : X.Mem s f) (hY : Y.Mem s g) :
    (sub X Y).Mem s (f - g) :=
  mem_congr (mem_add hX (mem_neg hY)) (by ring)

theorem mem_scal {a : Iv} {k : ℝ} (ha : a.Mem k) {X : TM} {f : ℝ} (hX : X.Mem s f) :
    (scal a X).Mem s (k * f) := by
  intro hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  exact ⟨k * a₀, k * a₁, k * ρ, Iv.mem_mul ha h₀, Iv.mem_mul ha h₁, Iv.mem_mul ha hr,
    by ring⟩

theorem mem_lin {X : TM} {a₀ a₁ : ℝ} (hx : x.Adm s) (h₀ : X.c0.Mem a₀) (h₁ : X.c1.Mem a₁) :
    (lin x X).Mem (a₀ + a₁ * s) :=
  Iv.mem_add h₀ (Iv.mem_mul h₁ hx.1)

theorem mem_range {X : TM} {f : ℝ} (hx : x.Adm s) (hX : X.Mem s f) (hok : X.ok = true) :
    (range x X).Mem f := by
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  exact Iv.mem_add (mem_lin hx h₀ h₁) (Iv.mem_mul hr hx.2)

theorem mem_mul {X Y : TM} {f g : ℝ} (hx : x.Adm s) (hX : X.Mem s f) (hY : Y.Mem s g) :
    (mul x X Y).Mem s (f * g) := by
  intro hok
  simp only [mul, Bool.and_eq_true] at hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok.1
  obtain ⟨b₀, b₁, σ, k₀, k₁, kr, rfl⟩ := hY hok.2
  refine ⟨a₀ * b₀, a₀ * b₁ + a₁ * b₀,
    a₁ * b₁ + ρ * (b₀ + b₁ * s) + σ * (a₀ + a₁ * s) + ρ * σ * s ^ 2,
    Iv.mem_mul h₀ k₀, Iv.mem_add (Iv.mem_mul h₀ k₁) (Iv.mem_mul h₁ k₀), ?_, by ring⟩
  exact Iv.mem_add (Iv.mem_add (Iv.mem_add (Iv.mem_mul h₁ k₁)
    (Iv.mem_mul hr (mem_lin hx k₀ k₁))) (Iv.mem_mul kr (mem_lin hx h₀ h₁)))
    (Iv.mem_mul (Iv.mem_mul hr kr) hx.2)

/-- The deviation `q = (f - a₀)/a₀ = s u` and its enclosures. -/
theorem deviation {X : TM} {a₁ ρ i : ℝ} (hx : x.Adm s) (h₁ : X.c1.Mem a₁)
    (hr : X.r.Mem ρ) {I : Iv} (hi : I.Mem i) :
    ((X.c1.mul I).add ((X.r.mul I).mul x.s1)).Mem (a₁ * i + ρ * i * s) ∧
      (((X.c1.mul I).mul x.s1).add ((X.r.mul I).mul x.s2)).Mem
        (a₁ * i * s + ρ * i * s ^ 2) :=
  ⟨Iv.mem_add (Iv.mem_mul h₁ hi) (Iv.mem_mul (Iv.mem_mul hr hi) hx.1),
    Iv.mem_add (Iv.mem_mul (Iv.mem_mul h₁ hi) hx.1) (Iv.mem_mul (Iv.mem_mul hr hi) hx.2)⟩

theorem mem_inv {X : TM} {f : ℝ} (hx : x.Adm s) (hX : X.Mem s f) : (inv x X).Mem s f⁻¹ := by
  intro hok
  simp only [inv, scal, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨hok, hlo⟩, hV⟩ := hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  have ha₀ := Iv.lo_pos_of_mem h₀ hlo
  have hi := Iv.mem_inv h₀ hlo
  obtain ⟨hU, hq⟩ := deviation hx h₁ hr hi
  set u := a₁ * a₀⁻¹ + ρ * a₀⁻¹ * s
  set q := a₁ * a₀⁻¹ * s + ρ * a₀⁻¹ * s ^ 2
  have h1q := Iv.mem_add Iv.mem_one hq
  have h1qlo : 0 < (Iv.one.add (((X.c1.mul X.c0.inv).mul x.s1).add
      ((X.r.mul X.c0.inv).mul x.s2))).lo := by
    simpa [Iv.add, Iv.one] using hV
  have hqpos := Iv.lo_pos_of_mem h1q h1qlo
  have hR := Iv.mem_mul (Iv.mem_sq hU) (Iv.mem_inv h1q h1qlo)
  refine ⟨a₀⁻¹ * 1, a₀⁻¹ * -(a₁ * a₀⁻¹), a₀⁻¹ * (-(ρ * a₀⁻¹) + u ^ 2 * (1 + q)⁻¹),
    Iv.mem_mul hi Iv.mem_one, Iv.mem_mul hi (Iv.mem_neg (Iv.mem_mul h₁ hi)),
    Iv.mem_mul hi (Iv.mem_add (Iv.mem_neg (Iv.mem_mul hr hi)) hR), ?_⟩
  have hf : a₀ + a₁ * s + ρ * s ^ 2 = a₀ * (1 + q) := by
    simp only [q]; field_simp; ring
  have hq2 : q ^ 2 = s ^ 2 * u ^ 2 := by simp only [q, u]; ring
  rw [hf]
  have hne : 1 + q ≠ 0 := hqpos.ne'
  have key : (1 + q)⁻¹ = 1 - q + q ^ 2 * (1 + q)⁻¹ := by field_simp; ring
  calc (a₀ * (1 + q))⁻¹ = a₀⁻¹ * (1 - q + q ^ 2 * (1 + q)⁻¹) := by rw [mul_inv, ← key]
    _ = _ := by simp only [q, u]; ring

theorem log_remainder {q : ℝ} (hq : |q| < 1) :
    |Real.log (1 + q) - q + q ^ 2 / 2| ≤ |q| ^ 3 / (1 - |q|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -q) (by rwa [abs_neg]) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at h
  convert h using 2
  push_cast
  ring

theorem exp_remainder {q : ℝ} (hq : |q| ≤ 1) :
    |Real.exp q - (1 + q + q ^ 2 / 2)| ≤ |q| ^ 3 * (2 / 9) := by
  have h := Real.exp_bound hq (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  convert h using 2
  · push_cast; ring
  · norm_num

/-- A remainder `E` with `|E| ≤ c |q|³`, `q = s u`, is `θ s²` with `|θ| ≤ c u² |q|`. -/
theorem remainder_quot {E q u c : ℝ} (hc : 0 ≤ c) (hqu : q = s * u)
    (hE : |E| ≤ c * |q| ^ 3) : ∃ θ : ℝ, E = θ * s ^ 2 ∧ |θ| ≤ c * (u ^ 2 * |q|) := by
  by_cases hs : s = 0
  · refine ⟨0, ?_, by simp only [abs_zero]; positivity⟩
    have : q = 0 := by rw [hqu, hs, zero_mul]
    rw [this] at hE
    simp only [abs_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      abs_nonpos_iff] at hE
    rw [hE]; ring
  · refine ⟨E / s ^ 2, by field_simp, ?_⟩
    have hs2 : 0 < s ^ 2 := by positivity
    rw [abs_div, abs_of_pos hs2, div_le_iff₀ hs2]
    calc |E| ≤ c * |q| ^ 3 := hE
      _ = c * (u ^ 2 * |q|) * s ^ 2 := by
        rw [show |q| ^ 3 = |q| ^ 2 * |q| by ring, sq_abs, hqu]; ring

theorem mem_log {X : TM} {f : ℝ} (hx : x.Adm s) (hX : X.Mem s f) :
    (log x X).Mem s (Real.log f) := by
  intro hok
  simp only [log, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨hok, hL⟩, hlo⟩, hmV⟩ := hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  have ha₀ := Iv.lo_pos_of_mem h₀ hlo
  have hi := Iv.mem_inv h₀ hlo
  obtain ⟨hU, hq⟩ := deviation hx h₁ hr hi
  set V := ((X.c1.mul X.c0.inv).mul x.s1).add ((X.r.mul X.c0.inv).mul x.s2)
  set u := a₁ * a₀⁻¹ + ρ * a₀⁻¹ * s
  set q := a₁ * a₀⁻¹ * s + ρ * a₀⁻¹ * s ^ 2
  have hS := scale_pos
  have hqm := Iv.abs_le_mag hq
  have hmV' : (V.mag : ℝ) / scale < 1 := by
    rw [div_lt_one hS]; exact_mod_cast hmV
  have hq1 : |q| < 1 := lt_of_le_of_lt hqm hmV'
  have hqu : q = s * u := by simp only [q, u]; ring
  have hrem := log_remainder hq1
  have hden : 0 < 1 - |q| := by linarith
  obtain ⟨θ, hθ, hθb⟩ := remainder_quot (E := Real.log (1 + q) - q + q ^ 2 / 2)
    (c := (1 - |q|)⁻¹) (by positivity) hqu (by rw [← div_eq_inv_mul]; exact hrem)
  -- the bound on θ
  have hSm : 0 < ((scale - V.mag : ℤ) : ℝ) / scale := by
    push_cast; apply div_pos _ hS; rw [div_lt_one hS] at hmV'; linarith
  have hSlo : 0 < (⟨scale - V.mag, scale - V.mag⟩ : Iv).lo := by
    show 0 < scale - V.mag; omega
  have hw := Iv.mem_mul (Iv.mem_mul (Iv.mem_sq hU) (Iv.mem_point V.mag))
    (Iv.mem_inv (Iv.mem_point (scale - V.mag)) hSlo)
  have hθB : |θ| ≤ ((((Iv.sq ((X.c1.mul X.c0.inv).add ((X.r.mul X.c0.inv).mul x.s1))).mul
      ⟨V.mag, V.mag⟩).mul (Iv.inv ⟨scale - V.mag, scale - V.mag⟩)).hi : ℝ) / scale := by
    refine hθb.trans (le_trans ?_ hw.2)
    have h1 : ((scale - V.mag : ℤ) : ℝ) / scale = 1 - (V.mag : ℝ) / scale := by
      push_cast; field_simp
    rw [h1]
    have hmq : |q| ≤ (V.mag : ℝ) / scale := hqm
    have hfrac : |q| / (1 - |q|) ≤ ((V.mag : ℝ) / scale) / (1 - (V.mag : ℝ) / scale) := by
      rw [div_le_div_iff₀ hden (by linarith)]
      nlinarith [abs_nonneg q]
    calc (1 - |q|)⁻¹ * (u ^ 2 * |q|) = u ^ 2 * (|q| / (1 - |q|)) := by ring
      _ ≤ u ^ 2 * (((V.mag : ℝ) / scale) / (1 - (V.mag : ℝ) / scale)) :=
        mul_le_mul_of_nonneg_left hfrac (sq_nonneg u)
      _ = _ := by ring
  have hR := Iv.mem_add (Iv.mem_neg (Iv.mem_divNat (Iv.mem_sq hU) (n := 2) (by norm_num)))
    (Iv.mem_symm hθB)
  refine ⟨Real.log a₀, a₁ * a₀⁻¹, ρ * a₀⁻¹ + (-(u ^ 2 / 2) + θ), mem_logIv h₀ hL, ?_, ?_, ?_⟩
  · exact Iv.mem_mul h₁ hi
  · exact Iv.mem_add (Iv.mem_mul hr hi) (by exact_mod_cast hR)
  · have hf : a₀ + a₁ * s + ρ * s ^ 2 = a₀ * (1 + q) := by
      simp only [q]; field_simp; ring
    have hpos : 0 < 1 + q := by linarith [neg_abs_le q]
    rw [hf, Real.log_mul ha₀.ne' hpos.ne']
    have hq2 : q ^ 2 = s ^ 2 * u ^ 2 := by rw [hqu]; ring
    have : Real.log (1 + q) = q - q ^ 2 / 2 + θ * s ^ 2 := by linarith
    rw [this, hq2]
    simp only [q]
    ring

theorem mem_exp {X : TM} {f : ℝ} (hx : x.Adm s) (hX : X.Mem s f) :
    (exp x X).Mem s (Real.exp f) := by
  intro hok
  simp only [exp, scal, Bool.and_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨hok, hE⟩, hmV⟩ := hok
  obtain ⟨a₀, a₁, ρ, h₀, h₁, hr, rfl⟩ := hX hok
  have hU := Iv.mem_add h₁ (Iv.mem_mul hr hx.1)
  have hq := Iv.mem_add (Iv.mem_mul h₁ hx.1) (Iv.mem_mul hr hx.2)
  set V := (X.c1.mul x.s1).add (X.r.mul x.s2)
  set u := a₁ + ρ * s
  set q := a₁ * s + ρ * s ^ 2
  have hS := scale_pos
  have hqm := Iv.abs_le_mag hq
  have hq1 : |q| ≤ 1 := by
    refine hqm.trans ?_
    rw [div_le_one hS]; exact_mod_cast hmV
  have hqu : q = s * u := by simp only [q, u]; ring
  have hrem := exp_remainder hq1
  obtain ⟨θ, hθ, hθb⟩ := remainder_quot (E := Real.exp q - (1 + q + q ^ 2 / 2))
    (c := 2 / 9) (by norm_num) hqu (by rw [mul_comm]; exact hrem)
  have hw := Iv.mem_mul (Iv.mem_mul (Iv.mem_sq hU) (Iv.mem_point V.mag))
    (Iv.mem_ofRat 2 9 (by norm_num))
  have hθB : |θ| ≤ ((((Iv.sq (X.c1.add (X.r.mul x.s1))).mul ⟨V.mag, V.mag⟩).mul
      (Iv.ofRat 2 9)).hi : ℝ) / scale := by
    refine hθb.trans (le_trans ?_ hw.2)
    push_cast
    have hmq : |q| ≤ (V.mag : ℝ) / scale := hqm
    calc 2 / 9 * (u ^ 2 * |q|) ≤ 2 / 9 * (u ^ 2 * ((V.mag : ℝ) / scale)) := by gcongr
      _ = _ := by ring
  have hR := Iv.mem_add (Iv.mem_divNat (Iv.mem_sq hU) (n := 2) (by norm_num))
    (Iv.mem_symm hθB)
  have he := mem_expIv h₀ hE
  refine ⟨Real.exp a₀ * 1, Real.exp a₀ * a₁, Real.exp a₀ * (ρ + (u ^ 2 / 2 + θ)),
    Iv.mem_mul he Iv.mem_one, Iv.mem_mul he h₁, Iv.mem_mul he (Iv.mem_add hr ?_), ?_⟩
  · exact_mod_cast hR
  · have hf : a₀ + a₁ * s + ρ * s ^ 2 = a₀ + q := by simp only [q]; ring
    rw [hf, Real.exp_add]
    have : Real.exp q = 1 + q + q ^ 2 / 2 + θ * s ^ 2 := by linarith
    rw [this, hqu]
    simp only [u]
    ring

theorem mem_sum {Xs : List TM} {fs : List ℝ} (h : List.Forall₂ (fun X f => X.Mem s f) Xs fs) :
    (sum Xs).Mem s fs.sum := by
  induction h with
  | nil => exact mem_const Iv.mem_zero
  | cons hX _ ih => exact mem_congr (mem_add hX ih) (by simp)

end TM

end BecknerOnofri.HighDim.Spin.PressureCertificate
