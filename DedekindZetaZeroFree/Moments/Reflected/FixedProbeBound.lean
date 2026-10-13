module

public import DedekindZetaZeroFree.Moments.Reflected.GeneralSupportMoment

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.ReflectedProbe

open DedekindZetaZeroFree PoissonProbe
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

private theorem norm_continuous (A : SArithmeticData F) : Continuous A.norm := by
  unfold SArithmeticData.norm
  fun_prop

private theorem normalizeShape_continuous (A : SArithmeticData F) :
    Continuous (normalizeShape A) := by
  exact continuous_id.div' (A.continuous_radialSection.comp
    ((norm_continuous A).subtype_mk (norm_pos A)))

private theorem localPoint_injective (A : SArithmeticData F) :
    Function.Injective (NormalizedProbe.asLocalPoint A) := by
  intro x y h
  apply Prod.ext
  · funext w
    apply Units.ext
    exact congrFun (congrArg Prod.fst h) w
  · funext v
    apply Units.ext
    exact congrFun (congrArg Prod.snd h) v

private theorem scaled_row_shape (A : SArithmeticData F) (T : ℝ) (hT : 0 < T)
    (K : Set A.G) (m : ThetaReflectionData.Row A)
    (hm : m.val ∈ NormalizedProbe.scaledIntegralRows A T K) :
    ∃ k ∈ K, ActualRowTransfer.rowShape A m = normalizeShape A k ∧
      A.exteriorNorm (ActualRowTransfer.rowIdeal A m) = T * A.norm k := by
  obtain ⟨k, hk, he⟩ := hm
  have hd : NormalizedProbe.asLocalPoint A (A.diagonal (ThetaReflectionData.rowUnit A m)) =
      sLocalDiagonal F A.Sf (m.val : F) := by
    ext w <;> rfl
  have hg : A.diagonal (ThetaReflectionData.rowUnit A m) =
      A.radialSection T hT * k := by
    apply localPoint_injective A
    rw [hd, he]
    simp only [NormalizedProbe.radialSection, dif_pos hT]
  have hn : A.exteriorNorm (ActualRowTransfer.rowIdeal A m) = T * A.norm k := by
    rw [← A.generator_norm (ActualRowTransfer.rowIdeal A m) m.val
      ⟨m.property, ActualRowTransfer.span_rowIdeal A m⟩
      (ThetaReflectionData.rowUnit A m) (by rfl), hg]
    have hmul (x y : A.G) : A.norm (x * y) = A.norm x * A.norm y := by
      simp [SArithmeticData.norm, norm_mul, mul_pow, Finset.prod_mul_distrib,
        mul_mul_mul_comm]
    rw [hmul, A.norm_radialSection]
  refine ⟨k, hk, ?_, hn⟩
  unfold ActualRowTransfer.rowShape normalizeShape
  rw [hg]
  simp only [hn, A.radialSection_mul T (A.norm k) hT (norm_pos A k)]
  simp only [mul_div_mul_left_eq_div]

private theorem integrand_eq_rows (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (P : NormalizedProbe.DomainData A)
    (W0 : SLocalProduct F A.Sf → ℂ) (W1 : ProbeRealAnnularWeight)
    (X Y Z : ℝ) (hY : 0 < Y) (t : A.G1) (rs : Finset A.R)
    (hterm : ∀ (s : A.Exterior) (m : A.R), W1 (A.exteriorNorm s / Y) ≠ 0 →
      W0 (sLocalDiagonal F A.Sf (m : F) *
        NormalizedProbe.asLocalPoint A (((t : A.G) *
          NormalizedProbe.radialSection A (A.exteriorNorm s * X))⁻¹)) ≠ 0 → m ∈ rs) :
    NormalizedProbe.integrand A D P W0 W1 X Y Z t =
      ∑ m ∈ rs, NormalizedProbe.additiveCoefficient A D W0 W1 X Y t m *
        NormalizedProbe.rowB A D m Z := by
  classical
  let ss := (NormalizedProbe.exterior_weight_finite A W1 Y hY).toFinset
  let c : A.Exterior → A.R → ℂ := fun s m =>
    (W1 (A.exteriorNorm s / Y) : ℂ) *
      (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹ * NormalizedProbe.gaussRow A D s m *
      W0 (sLocalDiagonal F A.Sf (m : F) *
        NormalizedProbe.asLocalPoint A (((t : A.G) *
          NormalizedProbe.radialSection A (A.exteriorNorm s * X))⁻¹))
  have hcs (s : A.Exterior) (hs : s ∉ ss) (m : A.R) : c s m = 0 := by
    have hw : W1 (A.exteriorNorm s / Y) = 0 := by
      simpa only [ss, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hs
    simp [c, hw]
  have hcm (s : A.Exterior) (m : A.R) (hm : m ∉ rs) : c s m = 0 := by
    by_cases hw : W1 (A.exteriorNorm s / Y) = 0
    · simp [c, hw]
    · have hw0 : W0 (sLocalDiagonal F A.Sf (m : F) *
        NormalizedProbe.asLocalPoint A (((t : A.G) *
          NormalizedProbe.radialSection A (A.exteriorNorm s * X))⁻¹)) = 0 := by
        by_contra hh
        exact hm (hterm s m hw hh)
      simp only [c, hw0, mul_zero]
  have hinner (s : A.Exterior) :
      ((W1 (A.exteriorNorm s / Y) : ℂ) *
        (Real.sqrt (A.exteriorNorm s * X) : ℂ)⁻¹) *
      (∑' m : A.R, NormalizedProbe.gaussRow A D s m *
        W0 (sLocalDiagonal F A.Sf (m : F) *
          NormalizedProbe.asLocalPoint A (((t : A.G) *
            NormalizedProbe.radialSection A (A.exteriorNorm s * X))⁻¹)) *
        NormalizedProbe.rowB A D m Z) =
      ∑ m ∈ rs, c s m * NormalizedProbe.rowB A D m Z := by
    rw [← tsum_mul_left]
    simp only [← mul_assoc]
    change (∑' m, c s m * NormalizedProbe.rowB A D m Z) = _
    exact tsum_eq_sum (fun m hm => by rw [hcm s m hm, zero_mul])
  unfold NormalizedProbe.integrand
  simp_rw [hinner]
  rw [tsum_eq_sum (s := ss) (fun s hs => by simp [hcs s hs])]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  unfold NormalizedProbe.additiveCoefficient
  change _ = (Y⁻¹ : ℂ) * (∑' s, c s m) * NormalizedProbe.rowB A D m Z
  rw [tsum_eq_sum (s := ss) (fun s hs => hcs s hs m), mul_assoc, Finset.sum_mul]

private theorem general_bound (A : SArithmeticData F) (σ : F →+* ℂ)
    (η : RayClassCharacter F A.modulus) (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (hmoment : ∀ Kshape : Set A.G, IsCompact Kshape → ∀ Cstar : ℝ, 0 < Cstar →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 2 ≤ Z →
        ∀ rows : Finset (ThetaReflectionData.Row A),
          (∀ r ∈ rows, ActualRowTransfer.rowShape A r ∈ Kshape ∧
            A.exteriorNorm (ActualRowTransfer.rowIdeal A r) ≤ Cstar * Z ^ Scales.supportExponent) →
          (∑ r ∈ rows, ‖ThetaReflectionData.forwardB A P.coefficients r Z‖ ^ 2) ≤
            C * Z ^ (2 * Scales.supportExponent - 1 + ε))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖NormalizedProbe.probe A P.coefficients P.domain P.W0 P.W1
        (Scales.xScale Z) (Scales.yScale Z) Z‖ ≤ Cε * Z ^ (Scales.reflectedExponent + ε) := by
  classical
  letI : MeasurableSpace A.G1 := borel _
  letI : BorelSpace A.G1 := ⟨rfl⟩
  letI : MeasureTheory.Measure.IsHaarMeasure P.domain.measure := P.domain.haar
  obtain ⟨Kbox, hKbox, hsupport⟩ := NormalizedProbe.additiveCoefficient_uniform_support A
    P.domain.domain P.domain.relativelyCompact P.W0 P.compactSupport P.supportUnits P.W1
  let Kshape := normalizeShape A '' Kbox
  have hKshape : IsCompact Kshape := hKbox.image (normalizeShape_continuous A)
  obtain ⟨Cstar, hCstar⟩ := hKbox.exists_bound_of_continuousOn (norm_continuous A).continuousOn
  let Cnorm := max Cstar 1
  have hCnorm : 0 < Cnorm := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨KB, hKB, hmomentB⟩ := hmoment Kshape hKshape Cnorm hCnorm (2 * ε) (by positivity)
  obtain ⟨CA, hCA, henergy⟩ := NormalizedProbe.principal_additiveCoefficient_square_energy
    A σ η hS P P.domain.domain P.domain.relativelyCompact
  have hmass : P.domain.measure P.domain.domain < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono subset_closure)
      P.domain.relativelyCompact.measure_lt_top
  refine ⟨Real.sqrt (2 * CA * KB) * P.domain.measure.real P.domain.domain, by positivity, ?_⟩
  intro Z hZ
  have hZpos : 0 < Z := by linarith
  have hZone : 1 ≤ Z := by linarith
  have hX : 1 ≤ Scales.xScale Z := Real.one_le_rpow hZone (by unfold Scales.xExponent; norm_num)
  have hY : 1 ≤ Scales.yScale Z := Real.one_le_rpow hZone (by unfold Scales.yExponent; norm_num)
  have hXpos : 0 < Scales.xScale Z := lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Scales.yScale Z := lt_of_lt_of_le zero_lt_one hY
  have hYX : Scales.yScale Z ≤ Scales.xScale Z :=
    Real.rpow_le_rpow_of_exponent_le hZone (by unfold Scales.xExponent Scales.yExponent; norm_num)
  have hXY : Scales.xScale Z * Scales.yScale Z = Z ^ Scales.supportExponent := by
    unfold Scales.xScale Scales.yScale; rw [← Real.rpow_add hZpos]; congr 1
    unfold Scales.xExponent Scales.yExponent Scales.supportExponent; norm_num
  have key : Z ^ (2 * Scales.supportExponent - 1 + 2 * ε) =
      Z ^ ((Scales.reflectedExponent + ε) * 2) * Scales.yScale Z := by
    unfold Scales.yScale
    rw [← Real.rpow_add hZpos]
    congr 1
    unfold Scales.supportExponent Scales.reflectedExponent Scales.yExponent
    norm_num
    ring
  generalize hXg : Scales.xScale Z = X at *
  generalize hYg : Scales.yScale Z = Y at *
  have hYt : Y = Z ^ Scales.yExponent := by rw [← hYg]; rfl
  obtain ⟨hf, hs⟩ := hsupport X Y hXpos hYpos
  let rs := hf.toFinset
  let rows : Finset (ThetaReflectionData.Row A) := rs.subtype (fun m => m ≠ 0)
  have hB : (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A P.coefficients m Z‖ ^ 2) ≤
      KB * Z ^ (2 * Scales.supportExponent - 1 + 2 * ε) := by
    apply hmomentB Z hZ rows
    intro m hm
    have hmem : m.val ∈ NormalizedProbe.scaledIntegralRows A (X * Y) Kbox := by
      exact hf.mem_toFinset.mp (Finset.mem_subtype.mp hm)
    obtain ⟨k, hk, hshape, hn⟩ := scaled_row_shape A (X * Y) (mul_pos hXpos hYpos)
      Kbox m hmem
    constructor
    · exact ⟨k, hk, hshape.symm⟩
    · rw [hn, hXY, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
      exact (le_abs_self (A.norm k)).trans ((hCstar k hk).trans (le_max_left _ _))
  have hBrs : (∑ m ∈ rs, ‖NormalizedProbe.rowB A P.coefficients m Z‖ ^ 2) ≤
      KB * Z ^ (2 * Scales.supportExponent - 1 + 2 * ε) := by
    have heq : (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A P.coefficients m Z‖ ^ 2) =
        ∑ m ∈ rs, ‖NormalizedProbe.rowB A P.coefficients m Z‖ ^ 2 := by
      simp_rw [← NormalizedProbe.rowB_nonzero]
      dsimp only [rows]
      rw [Finset.sum_subtype_eq_sum_filter
        (fun m : A.R => ‖NormalizedProbe.rowB A P.coefficients m Z‖ ^ 2)]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro m hm hn
      have hz : m = 0 := by simpa only [Finset.mem_filter, hm, true_and, not_not] using hn
      simp [hz, NormalizedProbe.rowB]
    rwa [heq] at hB
  have hpoint : ∀ t ∈ P.domain.domain,
      ‖NormalizedProbe.integrand A P.coefficients P.domain P.W0 P.W1 X Y Z t‖ ≤
        Real.sqrt (2 * CA * KB) * Z ^ (Scales.reflectedExponent + ε) := by
    intro t ht
    have hterm := (hs t ht).1
    rw [integrand_eq_rows A P.coefficients P.domain P.W0 P.W1 X Y Z hYpos t rs
      (fun s m hw1 hw0 => hf.mem_toFinset.mpr (hterm s m hw1 hw0))]
    obtain ⟨hsummable, _, hsmall⟩ := henergy X Y hX hY t ht
    have hArs : (∑ m ∈ rs,
        ‖NormalizedProbe.additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) ≤
        2 * CA / Y :=
      (Summable.sum_le_tsum rs (fun m _ => sq_nonneg _) hsummable).trans (hsmall hYX)
    calc
      _ ≤ ∑ m ∈ rs,
          ‖NormalizedProbe.additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ *
          ‖NormalizedProbe.rowB A P.coefficients m Z‖ := by
        simpa only [norm_mul] using norm_sum_le rs (fun m =>
          NormalizedProbe.additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m *
            NormalizedProbe.rowB A P.coefficients m Z)
      _ ≤ Real.sqrt (∑ m ∈ rs,
          ‖NormalizedProbe.additiveCoefficient A P.coefficients P.W0 P.W1 X Y t m‖ ^ 2) *
          Real.sqrt (∑ m ∈ rs, ‖NormalizedProbe.rowB A P.coefficients m Z‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ ≤ Real.sqrt (2 * CA / Y) *
          Real.sqrt (KB * Z ^ (2 * Scales.supportExponent - 1 + 2 * ε)) :=
        mul_le_mul (Real.sqrt_le_sqrt hArs) (Real.sqrt_le_sqrt hBrs)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt (2 * CA * KB) * Z ^ (Scales.reflectedExponent + ε) := by
        rw [← Real.sqrt_mul (by positivity), key]
        have hW : Z ^ ((Scales.reflectedExponent + ε) * 2) = (Z ^ (Scales.reflectedExponent + ε)) ^ 2 := by
          rw [Real.rpow_mul hZpos.le, Real.rpow_two]
        have hYne : Y ≠ 0 := hYpos.ne'
        rw [hW, show 2 * CA / Y * (KB * ((Z ^ (Scales.reflectedExponent + ε)) ^ 2 * Y)) =
          (2 * CA * KB) * (Z ^ (Scales.reflectedExponent + ε)) ^ 2 by field_simp]
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.rpow_nonneg hZpos.le _)]
  have hint := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmass hpoint
  change ‖∫ t in P.domain.domain,
    NormalizedProbe.integrand A P.coefficients P.domain P.W0 P.W1 X Y Z t
      ∂P.domain.measure‖ ≤ _
  exact hint.trans_eq (by ring)

end DedekindZetaZeroFree.Quantitative.ReflectedProbe

namespace DedekindZetaZeroFree.Quantitative

open DedekindZetaZeroFree

theorem FixedData.Iscale_bound {F : Type} [Field F] [NumberField F]
    {S : SArithmeticData F} {η : RayClassCharacter F S.modulus} (D : FixedData S η)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 < Cε ∧ ∀ Z : ℝ, 2 ≤ Z → ‖D.Iscale Z‖ ≤ Cε * Z ^ (Scales.reflectedExponent + ε) := by
  obtain ⟨C, hC0, hC⟩ := ReflectedProbe.general_bound D.recipe.A D.recipe.σ D.recipe.target
    D.recipe.traceBad D.recipe.probe
    (fun Kshape hK Cstar hCstar ε' hε' => D.moment_m₀ Kshape hK Cstar hCstar ε' hε') ε hε
  refine ⟨C + 1, by linarith, fun Z hZ => ?_⟩
  have h2 : 0 ≤ Z ^ (Scales.reflectedExponent + ε) := Real.rpow_nonneg (by linarith) _
  exact (hC Z hZ).trans (mul_le_mul_of_nonneg_right (by linarith) h2)

end DedekindZetaZeroFree.Quantitative
