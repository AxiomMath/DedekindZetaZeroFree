module

public import DedekindZetaZeroFree.LargeSieve.CharacterBounds.AdditiveCoefficientEnergy

@[expose] public section

namespace DedekindZetaZeroFree
namespace PoissonProbe
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
open scoped NumberField Classical
open MeasureTheory

variable {F : Type} [Field F] [NumberField F]

def BalancedReflectedMomentConclusion (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) : Prop :=
  ∀ Kshape : Set A.G, IsCompact Kshape →
    ∀ Cstar : ℝ, 0 < Cstar → ∀ δ : ℝ, 0 < δ →
      ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 2 ≤ Z →
        ∀ rows : Finset (ThetaReflectionData.Row A),
          (∀ m ∈ rows, ActualRowTransfer.rowShape A m ∈ Kshape ∧
            A.exteriorNorm (ActualRowTransfer.rowIdeal A m) ≤
              Cstar * Z ^ (1033 / 1000 : ℝ)) →
          (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A D m Z‖ ^ 2) ≤
            K * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + δ)

theorem reflected_probe_exponent_identity (ε : ℝ) :
    (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε - 133 / 1000) / 2 =
      933 / 2000 + ε := by
  ring

private theorem norm_continuous (A : SArithmeticData F) : Continuous A.norm := by
  unfold SArithmeticData.norm
  fun_prop

 theorem norm_pos (A : SArithmeticData F) (k : A.G) : 0 < A.norm k := by
  unfold SArithmeticData.norm
  apply mul_pos
  · exact Finset.prod_pos (fun w _ => pow_pos (norm_pos_iff.mpr (k.1 w).ne_zero) _)
  · exact Finset.prod_pos (fun v _ => norm_pos_iff.mpr (k.2 v).ne_zero)

 def normalizeShape (A : SArithmeticData F) (k : A.G) : A.G :=
  k / A.radialSection (A.norm k) (norm_pos A k)

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

theorem principal_reflected_exponent_bound_of_moment (A : SArithmeticData F)
    (σ : F →+* ℂ) (η : RayClassCharacter F A.modulus)
    (hS : A.ContainsTraceBadPlaces)
    (P : NormalizedProbe.PrincipalData A σ η hS)
    (hmoment : BalancedReflectedMomentConclusion A P.coefficients)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧ ∀ Z : ℝ, 2 ≤ Z →
      ‖NormalizedProbe.probe A P.coefficients P.domain P.W0 P.W1
        (Z ^ (9 / 10 : ℝ)) (Z ^ (133 / 1000 : ℝ)) Z‖ ≤
        Cε * Z ^ (933 / 2000 + ε) := by
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
  let Cpoint := Real.sqrt (2 * CA * KB)
  have hCpoint : 0 ≤ Cpoint := Real.sqrt_nonneg _
  have hmass : P.domain.measure P.domain.domain < ⊤ :=
    lt_of_le_of_lt (MeasureTheory.measure_mono subset_closure)
      P.domain.relativelyCompact.measure_lt_top
  refine ⟨Cpoint * P.domain.measure.real P.domain.domain, by positivity, ?_⟩
  intro Z hZ
  have hZpos : 0 < Z := by linarith
  have hZone : 1 ≤ Z := by linarith
  let X := Z ^ (9 / 10 : ℝ)
  let Y := Z ^ (133 / 1000 : ℝ)
  have hX : 1 ≤ X := Real.one_le_rpow hZone (by norm_num)
  have hY : 1 ≤ Y := Real.one_le_rpow hZone (by norm_num)
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hYX : Y ≤ X := Real.rpow_le_rpow_of_exponent_le hZone (by norm_num)
  have hXY : X * Y = Z ^ (1033 / 1000 : ℝ) := by
    dsimp [X, Y]
    rw [← Real.rpow_add hZpos]
    norm_num
  obtain ⟨hf, hs⟩ := hsupport X Y hXpos hYpos
  let rs := hf.toFinset
  let rows : Finset (ThetaReflectionData.Row A) := rs.subtype (fun m => m ≠ 0)
  have hB : (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A P.coefficients m Z‖ ^ 2) ≤
      KB * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε) := by
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
      KB * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε) := by
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
        Cpoint * Z ^ (933 / 2000 + ε) := by
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
          Real.sqrt (KB * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε)) :=
        mul_le_mul (Real.sqrt_le_sqrt hArs) (Real.sqrt_le_sqrt hBrs)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Cpoint * Z ^ (933 / 2000 + ε) := by
        rw [← Real.sqrt_mul (by positivity)]
        have halg : 2 * CA / Y * (KB * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε)) =
            (2 * CA * KB) * Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε - 133 / 1000) := by
          dsimp [Y]
          rw [Real.rpow_sub hZpos]
          ring
        rw [halg, Real.sqrt_mul (by positivity)]
        change Cpoint * Real.sqrt (Z ^ (2 * (1033 / 1000 : ℝ) - 1 + 2 * ε - 133 / 1000)) = _
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hZpos.le]
        congr 1
        congr 1
        rw [← reflected_probe_exponent_identity ε]
        ring
  have hint := MeasureTheory.norm_setIntegral_le_of_norm_le_const hmass hpoint
  change ‖∫ t in P.domain.domain,
    NormalizedProbe.integrand A P.coefficients P.domain P.W0 P.W1 X Y Z t
      ∂P.domain.measure‖ ≤ _
  exact hint.trans_eq (by ring)

end
end PoissonProbe
end DedekindZetaZeroFree
