module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.InitialIntegralIdentity

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.InitialDyadDomination

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory PoissonKernel PoissonInitialBridge
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

theorem J_singleton_eq (u : D.Row) (Z : ℝ) (hZ : 0 < Z) :
    J D {u} 4 4 2 Z =
      ((2 * (Real.pi : ℂ)) ^ 3)⁻¹ * ∫ t : ℝ × ℝ × ℝ, initialRowIntegrand D u Z t := by
  have hint := rowIntegrand_integrable D u Z hZ
  have hint' : Integrable (initialRowIntegrand D u Z) (volume.prod (volume.prod volume)) := hint
  unfold J
  rw [finsum_mem_singleton]
  unfold comparisonVerticalIntegral wzIntegral comparisonVerticalIntegral
  simp only [integral_const_mul]
  have h1 := integral_prod _ hint'
  have h2 : ∀ᵐ s : ℝ ∂volume, Integrable (fun p : ℝ × ℝ => initialRowIntegrand D u Z (s, p))
      (volume.prod volume) := hint'.prod_right_ae
  have h3 : ∫ s : ℝ, (∫ p : ℝ × ℝ, initialRowIntegrand D u Z (s, p) ∂(volume.prod volume)) =
      ∫ s : ℝ, ∫ t : ℝ, ∫ r : ℝ, initialRowIntegrand D u Z (s, t, r) := by
    refine integral_congr_ae ?_
    filter_upwards [h2] with s hs
    rw [integral_prod _ hs]
  rw [show (volume : Measure (ℝ × ℝ × ℝ)) = volume.prod (volume.prod volume) from rfl, h1, h3]
  simp only [initialRowIntegrand, Complex.ofReal_ofNat]
  ring

theorem J_finset_eq (C : Finset D.Row) (Z : ℝ) :
    J D (C : Set D.Row) 4 4 2 Z = ∑ u ∈ C, J D {u} 4 4 2 Z := by
  unfold J
  rw [finsum_mem_coe_finset]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [finsum_mem_singleton]

theorem norm_J_finset_le (C : Finset D.Row) (Z : ℝ) (hZ : 0 < Z) :
    ‖J D (C : Set D.Row) 4 4 2 Z‖ ≤
      ((2 * Real.pi) ^ 3)⁻¹ * ∑ u ∈ C, ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ := by
  have hn : ‖((2 * (Real.pi : ℂ)) ^ 3)⁻¹‖ = ((2 * Real.pi) ^ 3)⁻¹ := by
    have : (2 * (Real.pi : ℂ)) ^ 3 = (((2 * Real.pi) ^ 3 : ℝ) : ℂ) := by push_cast; ring
    rw [this, ← Complex.ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (by have := Real.pi_pos; positivity)]
  rw [J_finset_eq, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  rw [J_singleton_eq D u Z hZ, norm_mul, hn]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (by have := Real.pi_pos; positivity)

theorem norm_J_set_le (C : Set D.Row) (hC : C.Finite) (Z : ℝ) (hZ : 0 < Z) :
    ‖J D C 4 4 2 Z‖ ≤
      ((2 * Real.pi) ^ 3)⁻¹ *
        ∑ u ∈ hC.toFinset, ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ := by
  have h := norm_J_finset_le D hC.toFinset Z hZ
  rwa [Set.Finite.coe_toFinset] at h

theorem finset_partition_sum {ι : Type*} (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f)
    (T : ℕ → Finset ι) (hT : Pairwise (Function.onFun Disjoint T)) :
    Summable (fun k => ∑ u ∈ T k, f u) ∧ ∑' k, ∑ u ∈ T k, f u ≤ ∑' u, f u := by
  have hnn : ∀ k, 0 ≤ ∑ u ∈ T k, f u := fun k => Finset.sum_nonneg fun u _ => hf0 u
  have hpart : ∀ n : ℕ, ∑ k ∈ Finset.range n, ∑ u ∈ T k, f u ≤ ∑' u, f u := by
    intro n
    rw [← Finset.sum_biUnion (fun i _ j _ hij => hT hij)]
    exact hf.sum_le_tsum _ (fun i _ => hf0 i)
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

theorem dyadRows_disjoint {k j : ℕ} (h : k ≠ j) :
    Disjoint (dyadRows D ((2 : ℝ) ^ k)) (dyadRows D ((2 : ℝ) ^ j)) := by
  rw [Set.disjoint_left]
  intro u hk hj
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have h1 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hlt
    have h2 := hk.2
    have h3 := hj.1
    rw [pow_succ] at h1
    linarith
  · have h1 : (2 : ℝ) ^ (j + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hlt
    have h2 := hj.2
    have h3 := hk.1
    rw [pow_succ] at h1
    linarith

def nonprincipalDyad (k : ℕ) : Set D.Row := dyadRows D ((2 : ℝ) ^ k) \ principalRows D

theorem nonprincipalDyad_finite (k : ℕ) : (nonprincipalDyad D k).Finite :=
  (ActualRowCount.dyadRows_finite D _).subset Set.diff_subset

def Jnp (k : ℕ) (Z : ℝ) : ℂ := J D (nonprincipalDyad D k) 4 4 2 Z

theorem norm_Jnp_le (k : ℕ) (Z : ℝ) (hZ : 0 < Z) :
    ‖Jnp D k Z‖ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
      ∑ u ∈ (nonprincipalDyad_finite D k).toFinset,
        ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ :=
  norm_J_set_le D _ (nonprincipalDyad_finite D k) Z hZ

def rowNormTotal (Z : ℝ) : ℝ := ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖

private theorem partition_facts (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun k : ℕ => ∑ u ∈ (nonprincipalDyad_finite D k).toFinset,
      ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖) ∧
    ∑' k : ℕ, ∑ u ∈ (nonprincipalDyad_finite D k).toFinset,
      ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ ≤ rowNormTotal D Z := by
  refine finset_partition_sum _ (fun u => integral_nonneg fun t => norm_nonneg _)
    (rowIntegrand_norm_summable D Z hZ) (fun k => (nonprincipalDyad_finite D k).toFinset) ?_
  intro k j hkj
  rw [Function.onFun, Finset.disjoint_left]
  intro u hk hj
  rw [Set.Finite.mem_toFinset] at hk hj
  exact Set.disjoint_left.mp (dyadRows_disjoint D hkj) hk.1 hj.1

theorem Jnp_norm_summable (Z : ℝ) (hZ : 0 < Z) : Summable (fun k : ℕ => ‖Jnp D k Z‖) := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_Jnp_le D k Z hZ)
    ((partition_facts D Z hZ).1.mul_left _)

theorem Jnp_norm_tsum_le (Z : ℝ) (hZ : 0 < Z) :
    ∑' k : ℕ, ‖Jnp D k Z‖ ≤ ((2 * Real.pi) ^ 3)⁻¹ * rowNormTotal D Z := by
  obtain ⟨hs, hle⟩ := partition_facts D Z hZ
  calc ∑' k : ℕ, ‖Jnp D k Z‖ ≤ ∑' k : ℕ, ((2 * Real.pi) ^ 3)⁻¹ *
        ∑ u ∈ (nonprincipalDyad_finite D k).toFinset,
          ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ :=
        (Jnp_norm_summable D Z hZ).tsum_le_tsum (fun k => norm_Jnp_le D k Z hZ) (hs.mul_left _)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑' k : ℕ, ∑ u ∈ (nonprincipalDyad_finite D k).toFinset,
          ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hle (by have := Real.pi_pos; positivity)

def weightExp : ℝ := Scales.xExponent / 2 + 3 + 2 * Scales.smoothingExponent + 3 * Scales.yExponent

theorem weightExp_nonneg : 0 ≤ weightExp := by
  unfold weightExp Scales.xExponent Scales.smoothingExponent Scales.yExponent; norm_num

theorem norm_weight_scale (Z : ℝ) (hZ : 0 < Z) (ξ w z : ℂ) (hξ : ξ.re = 4) (hw : w.re = 4)
    (hz : z.re = 2) :
    ‖NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale Z) (Scales.yScale Z) Z ξ w z‖ =
      (Z / 2) ^ weightExp *
        ‖NormalizedProbe.tripleMellinWeight D.recipe.probe (Scales.xScale 2) (Scales.yScale 2) 2 ξ w z‖ := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  rw [tripleMellinWeight_eq D Z hZ, tripleMellinWeight_eq D 2 h2]
  simp only [norm_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ, Complex.norm_cpow_eq_rpow_re_of_pos h2]
  have hre : ((((Scales.xExponent / 2 : ℝ)) : ℂ) + ξ - 1 + (Scales.smoothingExponent : ℂ) * z +
      (Scales.yExponent : ℂ) * (w - 1)).re = weightExp := by
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im, hξ, hw, hz, weightExp]
    ring
  rw [hre, Real.div_rpow hZ.le h2.le]
  have : (2 : ℝ) ^ weightExp ≠ 0 := (Real.rpow_pos_of_pos h2 _).ne'
  field_simp

theorem norm_row_scale (u : D.Row) (Z : ℝ) (hZ : 0 < Z) (t : ℝ × ℝ × ℝ) :
    ‖initialRowIntegrand D u Z t‖ = (Z / 2) ^ weightExp * ‖initialRowIntegrand D u 2 t‖ := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h1 : (NormalizedProbe.initialMellinPoint t).1.re = 4 := by
    simp [NormalizedProbe.initialMellinPoint]
  have h2' : (NormalizedProbe.initialMellinPoint t).2.1.re = 4 := by
    simp [NormalizedProbe.initialMellinPoint]
  have h3 : (NormalizedProbe.initialMellinPoint t).2.2.re = 2 := by
    simp [NormalizedProbe.initialMellinPoint]
  have hw := norm_weight_scale D Z hZ (NormalizedProbe.initialMellinPoint t).1
    (NormalizedProbe.initialMellinPoint t).2.1 (NormalizedProbe.initialMellinPoint t).2.2 h1 h2' h3
  rw [rowIntegrand_eq_tsum D u Z hZ, rowIntegrand_eq_tsum D u 2 h2]
  simp only [NormalizedProbe.initialTripleMellinSummand]
  rw [tsum_mul_left, tsum_mul_left]
  simp only [norm_mul, hw]
  ring

theorem rowNormTotal_scale (Z : ℝ) (hZ : 0 < Z) :
    rowNormTotal D Z = (Z / 2) ^ weightExp * rowNormTotal D 2 := by
  unfold rowNormTotal
  have : ∀ u : D.Row, ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u Z t‖ =
      (Z / 2) ^ weightExp * ∫ t : ℝ × ℝ × ℝ, ‖initialRowIntegrand D u 2 t‖ := by
    intro u
    rw [← integral_const_mul]
    congr 1
    funext t
    exact norm_row_scale D u Z hZ t
  simp_rw [this]
  exact tsum_mul_left

theorem rowNormTotal_bdd_on_compact (Z₀ : ℝ) :
    ∃ C : ℝ, ∀ Z ∈ Set.Icc (2 : ℝ) Z₀, rowNormTotal D Z ≤ C := by
  refine ⟨(Z₀ / 2) ^ weightExp * rowNormTotal D 2, fun Z hZ => ?_⟩
  rw [rowNormTotal_scale D Z (by linarith [hZ.1])]
  refine mul_le_mul_of_nonneg_right ?_ ?_
  · exact Real.rpow_le_rpow (by linarith [hZ.1]) (by linarith [hZ.2]) weightExp_nonneg
  · exact tsum_nonneg fun u => integral_nonneg fun t => norm_nonneg _

theorem Jnp_norm_tsum_bdd_on_compact (Z₀ : ℝ) :
    ∃ C : ℝ, ∀ Z ∈ Set.Icc (2 : ℝ) Z₀, ∑' k : ℕ, ‖Jnp D k Z‖ ≤ C := by
  obtain ⟨C, hC⟩ := rowNormTotal_bdd_on_compact D Z₀
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * C, fun Z hZ => ?_⟩
  refine (Jnp_norm_tsum_le D Z (by linarith [hZ.1])).trans ?_
  exact mul_le_mul_of_nonneg_left (hC Z hZ) (by have := Real.pi_pos; positivity)

end

end DedekindZetaZeroFree.Quantitative.InitialDyadDomination
