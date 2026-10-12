module

public import DedekindZetaZeroFree.Nonvanishing.Mellin.PositiveProfileTransform

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical Topology
open NumberField MeasureTheory Filter
namespace DedekindZetaZeroFree.GaussianSmoothing
open MomentSources ThetaProfileHaarSheets
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

lemma bessel_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : KThird b ≤ KThird a := by
  rw [KThird_eq_integral _ (ha.trans_le hab), KThird_eq_integral _ ha]
  apply integral_mono (thirdBesselSchlafliIntegrand_integrable b (ha.trans_le hab))
    (thirdBesselSchlafliIntegrand_integrable a ha)
  intro u
  unfold thirdBesselSchlafliIntegrand
  apply mul_le_mul_of_nonneg_right _ (Real.cosh_pos _).le
  apply Real.exp_le_exp.mpr
  nlinarith [Real.cosh_pos u]

lemma profile_scale_le (c a b t : ℝ) (hc : 0 < c) (ha : 0 < a)
    (hab : a ≤ b) (ht : 0 < t) :
    thirdBesselRadialProfile c (b*t) ≤ (b/a) * thirdBesselRadialProfile c (a*t) := by
  have hk : KThird (c * Real.sqrt (b*t)) ≤ KThird (c * Real.sqrt (a*t)) := by
    apply bessel_antitone (mul_pos hc (Real.sqrt_pos.mpr (mul_pos ha ht)))
    gcongr
  unfold thirdBesselRadialProfile
  calc
    _ ≤ (b*t) * KThird (c * Real.sqrt (a*t)) :=
      mul_le_mul_of_nonneg_left hk (mul_pos (ha.trans_le hab) ht).le
    _ = _ := by field_simp

lemma section_norm_sq (A : SArithmeticData F) (w v : InfinitePlace F)
    (x : PositiveAxis) (z : A.G) :
    ‖((normSection A w x * z).1 v : v.Completion)‖ ^ 2 =
      (if v = w then x.val else 1) * ‖(z.1 v : v.Completion)‖ ^ 2 := by
  simp only [Prod.fst_mul, Pi.mul_apply, Units.val_mul, norm_mul, mul_pow]
  by_cases hv : v = w
  · subst v
    simp [normSection, norm_sq_sqrtUnit]
  · simp [normSection_at_other_place A w v hv, hv]

lemma radial_section_le (P : Packet R Q) (w : InfinitePlace F)
    (x y : PositiveAxis) (hxy : x.val ≤ y.val) (z : R.A.G) :
    radial P (normSection R.A w y * z) ≤ (y.val/x.val) * radial P (normSection R.A w x * z) := by
  have hfin (a : PositiveAxis) : (normSection R.A w a * z).2 = z.2 := by
    simp [normSection]
  unfold radial
  simp_rw [hfin, section_norm_sq]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ w),
    Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ w)]
  simp only [ite_true]
  have heq : (∏ v ∈ Finset.univ \ {w}, thirdBesselRadialProfile (P.scale v)
      ((if v = w then y.val else 1) * ‖(z.1 v : v.Completion)‖ ^ 2)) =
    ∏ v ∈ Finset.univ \ {w}, thirdBesselRadialProfile (P.scale v)
      ((if v = w then x.val else 1) * ‖(z.1 v : v.Completion)‖ ^ 2) := by
    apply Finset.prod_congr rfl
    intro v hv
    have hne : v ≠ w := (Finset.mem_sdiff.mp hv).2 ∘ Finset.mem_singleton.mpr
    simp [hne]
  rw [heq]
  have hrest : 0 ≤ ∏ v ∈ Finset.univ \ {w}, thirdBesselRadialProfile (P.scale v)
      ((if v = w then x.val else 1) * ‖(z.1 v : v.Completion)‖ ^ 2) := by
    apply Finset.prod_nonneg
    intro v hv
    have ht : 0 < (if v = w then x.val else 1) * ‖(z.1 v : v.Completion)‖ ^ 2 := by
      apply mul_pos
      · split_ifs
        · exact x.property
        · exact zero_lt_one
      · exact sq_pos_of_pos (norm_pos_iff.mpr (z.1 v).ne_zero)
    exact (mul_pos ht (KThird_pos _ (mul_pos (P.scale_pos v) (Real.sqrt_pos.mpr ht)))).le
  have hb := profile_scale_le (P.scale w) x.val y.val (‖(z.1 w : w.Completion)‖ ^ 2)
    (P.scale_pos w) x.property hxy (sq_pos_of_pos (norm_pos_iff.mpr (z.1 w).ne_zero))
  have hi : 0 ≤ (if ∀ p : R.A.Sf, z.2 p ∈ P.cutoff p then (1 : ℝ) else 0) := by
    split_ifs <;> norm_num
  calc
    _ ≤ (if ∀ p : R.A.Sf, z.2 p ∈ P.cutoff p then (1 : ℝ) else 0) *
      (((y.val/x.val) * thirdBesselRadialProfile (P.scale w)
        (x.val * ‖(z.1 w : w.Completion)‖ ^ 2)) * _) := by gcongr
    _ = _ := by ring

def sheet (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) : ℝ :=
  ∫ z : R.A.G1, radial P (normSection R.A P.v₀ x * z.val) ∂probeHaar R

lemma global_radial_integrable (N : TraceHaarTransport R) (P : Packet R Q) :
    Integrable (radial P) N.groupHaar := by
  have h := Complex.reCLM.integrable_comp ((global_mellin N P 0 (by norm_num)).1)
  simpa using h

theorem sheet_integrable (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    Integrable (fun z : R.A.G1 => radial P (normSection R.A P.v₀ x * z.val)) (probeHaar R) := by
  letI := N.groupHaar_isHaar
  have hae := (integral_disintegration R.A P.v₀ N.groupHaar
    (fun y => (radial P y : ℂ)) (Complex.ofRealCLM.integrable_comp (global_radial_integrable N P))).1
  have hker (a : PositiveAxis) :
    Integrable (fun y : Sheet R.A a => radial P y.val) (sheetHaar R.A P.v₀ N.groupHaar a) ↔
    Integrable (fun z : R.A.G1 => radial P (normSection R.A P.v₀ a * z.val)) (probeHaar R) := by
    rw [← kernelHaar_eq_probe N P.v₀]
    exact (sheetTranslation R.A P.v₀ a).toMeasurableEquiv.measurableEmbedding.integrable_map_iff
  let t : Set PositiveAxis := {y | y.val < x.val}
  have ht : IsOpen t := isOpen_lt continuous_subtype_val continuous_const
  have hne : t.Nonempty := ⟨⟨x.val/2, half_pos x.property⟩, by dsimp [t]; linarith [x.property]⟩
  obtain ⟨a, ha, hint⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ht.measure_ne_zero positiveHaar hne) (ae_restrict_of_ae hae)
  have hintR := Complex.reCLM.integrable_comp hint
  simp only [Complex.reCLM_apply, Complex.ofReal_re] at hintR
  have hi := (hker a).mp hintR
  refine (hi.const_mul (x.val/a.val)).mono'
    (((continuous_radial P).comp (sheetTranslation R.A P.v₀ x).continuous.subtype_val).aestronglyMeasurable) ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (radial_nonneg P _)]
  exact radial_section_le P P.v₀ a x (le_of_lt ha) z.val

theorem sheet_pos (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    0 < sheet N P x := by
  letI := probeHaar_isHaar R
  have hc : Continuous (fun z : R.A.G1 => radial P (normSection R.A P.v₀ x * z.val)) :=
    (continuous_radial P).comp (sheetTranslation R.A P.v₀ x).continuous.subtype_val
  have hpos : 0 < radial P (normSection R.A P.v₀ x * (1 : R.A.G1).val) := by
    rw [Subgroup.coe_one, mul_one]
    unfold radial
    have hcut : ∀ p : R.A.Sf, (normSection R.A P.v₀ x).2 p ∈ P.cutoff p := by
      intro p
      rw [normSection_at_finite_place]
      exact (P.cutoff p).one_mem
    rw [if_pos hcut, one_mul]
    apply Finset.prod_pos
    intro w _
    have ht : 0 < ‖((normSection R.A P.v₀ x).1 w : w.Completion)‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr ((normSection R.A P.v₀ x).1 w).ne_zero)
    exact mul_pos ht (KThird_pos _ (mul_pos (P.scale_pos w) (Real.sqrt_pos.mpr ht)))
  exact integral_pos_of_integrable_nonneg_nonzero hc (sheet_integrable N P x)
    (fun z => radial_nonneg P _) hpos.ne'

theorem positiveSheet_eq (N : TraceHaarTransport R) (P : Packet R Q) :
    P.positiveSheet = sheet N P := by
  funext x
  rw [sheet, integral_uniform_eq N P.v₀ x (radial P) (sheet_integrable N P x),
    probeHaar_integral]
  rfl

theorem positive_sheet_integrable (N : TraceHaarTransport R) (P : Packet R Q) (x : PositiveAxis) :
    letI : MeasurableSpace R.A.G1 := borel _
    Integrable (fun z : R.A.G1 =>
      let y := z.val * R.A.radialSection x.val x.property
      (if ∀ p : R.A.Sf, y.2 p ∈ P.cutoff p then 1 else 0) *
        ∏ w : InfinitePlace F, ‖(y.1 w : w.Completion)‖ ^ 2 *
          KThird (P.scale w * Real.sqrt (‖(y.1 w : w.Completion)‖ ^ 2))) R.probe.domain.measure := by
  exact (probeHaar_integrable _).mp
    ((integrable_uniform_iff N P.v₀ x (radial P)).mp (sheet_integrable N P x))

theorem continuous_sheet (N : TraceHaarTransport R) (P : Packet R Q) : Continuous (sheet N P) := by
  apply continuous_iff_continuousAt.mpr
  intro x₀
  let a : PositiveAxis := ⟨x₀.val/2, half_pos x₀.property⟩
  have ha : a.val < x₀.val := by dsimp [a]; linarith [x₀.property]
  refine continuousAt_of_dominated
    (bound := fun z : R.A.G1 => (2*x₀.val/a.val) * radial P (normSection R.A P.v₀ a * z.val)) ?_ ?_ ?_ ?_
  · filter_upwards with x
    exact ((continuous_radial P).comp (sheetTranslation R.A P.v₀ x).continuous.subtype_val).aestronglyMeasurable
  · have hlo : ∀ᶠ x : PositiveAxis in 𝓝 x₀, a.val < x.val :=
      continuous_subtype_val.continuousAt.eventually (Ioi_mem_nhds ha)
    have hup : ∀ᶠ x : PositiveAxis in 𝓝 x₀, x.val < 2*x₀.val :=
      continuous_subtype_val.continuousAt.eventually (Iio_mem_nhds (by linarith [x₀.property]))
    filter_upwards [hlo, hup] with x hx hx'
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (radial_nonneg P _)]
    refine (radial_section_le P P.v₀ a x hx.le z.val).trans ?_
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hx'.le a.property.le) (radial_nonneg P _)
  · exact (sheet_integrable N P a).const_mul _
  · filter_upwards with z
    exact ((continuous_radial P).comp
      ((normSplit R.A P.v₀).continuous.comp (continuous_id.prodMk continuous_const))).continuousAt

theorem sheet_mellin (N : TraceHaarTransport R) (P : Packet R Q)
    (s : ℂ) (hs : -(5/6 : ℝ) < s.re) :
    Integrable (fun x : PositiveAxis => (P.positiveSheet x : ℂ) * (x.val : ℂ)^s) positiveHaar ∧
    (∫ x : PositiveAxis, (P.positiveSheet x : ℂ) * (x.val : ℂ)^s ∂positiveHaar) =
      (polarC0 N P : ℂ) * (P.A₀ : ℂ)^s *
        (Complex.Gamma (s+5/6) * Complex.Gamma (s+7/6))^Fintype.card (InfinitePlace F) := by
  letI := N.groupHaar_isHaar
  have h := global_mellin N P s hs
  have hd := integral_disintegration R.A P.v₀ N.groupHaar
    (fun y => (radial P y : ℂ) * (R.A.norm y : ℂ)^s) h.1
  have heq (x : PositiveAxis) :
    (∫ y : Sheet R.A x, (radial P y.val : ℂ) * (R.A.norm y.val : ℂ)^s
      ∂sheetHaar R.A P.v₀ N.groupHaar x) = (P.positiveSheet x : ℂ) * (x.val : ℂ)^s := by
    simp_rw [show ∀ y : Sheet R.A x, R.A.norm y.val = x.val from fun y => y.property]
    rw [integral_mul_const]
    congr 1
    rw [integral_complex_ofReal (f := fun y : Sheet R.A x => radial P y.val)]
    congr 1
    have ht := (sheetTranslation R.A P.v₀ x).toMeasurableEquiv.measurableEmbedding.integral_map
      (μ := kernelHaar R.A P.v₀ N.groupHaar) (fun y : Sheet R.A x => radial P y.val)
    change (∫ y : Sheet R.A x, radial P y.val ∂sheetHaar R.A P.v₀ N.groupHaar x) = _
    calc
      _ = ∫ z : R.A.G1, radial P (normSection R.A P.v₀ x * z.val)
          ∂kernelHaar R.A P.v₀ N.groupHaar := ht
      _ = P.positiveSheet x := by
        rw [kernelHaar_eq_probe N P.v₀, positiveSheet_eq N P]
        rfl
  simp_rw [heq] at hd
  exact ⟨hd.2.1, hd.2.2.symm.trans h.2⟩

theorem C0_exact (N : TraceHaarTransport R) (P : Packet R Q) : P.C₀ = polarC0 N P := by
  have h := congrArg Complex.re ((sheet_mellin N P 0 (by norm_num)).2)
  simp only [Complex.cpow_zero, mul_one, zero_add] at h
  rw [integral_complex_ofReal (f := P.positiveSheet), Complex.ofReal_re] at h
  have hg1 : Complex.Gamma (5/6) = (Real.Gamma (5/6) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; congr 1; norm_num
  have hg2 : Complex.Gamma (7/6) = (Real.Gamma (7/6) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; congr 1; norm_num
  rw [hg1, hg2, ← Complex.ofReal_mul, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re] at h
  have hn : (Real.Gamma (5/6) * Real.Gamma (7/6))^Fintype.card (InfinitePlace F) ≠ 0 := by
    exact (pow_pos (mul_pos (Real.Gamma_pos_of_pos (by norm_num))
      (Real.Gamma_pos_of_pos (by norm_num))) _).ne'
  unfold Packet.C₀
  rw [h, mul_div_cancel_right₀ _ hn]
end DedekindZetaZeroFree.GaussianSmoothing

end
