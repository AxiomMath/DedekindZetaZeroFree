module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.AllowedRows.GoodCentralSum

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RowsHeightErrors

noncomputable section

open DedekindZetaZeroFree NumberField DedekindZetaZeroFree.Quantitative.PoissonKernel DedekindZetaZeroFree.Quantitative.DetectorDef
  DedekindZetaZeroFree.Quantitative.DetectorHeight DedekindZetaZeroFree.Quantitative.RowsExceptional DedekindZetaZeroFree.Quantitative.RowGoodDeform
  DedekindZetaZeroFree.Quantitative.RowsGoodCentral

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

section helpers

open MeasureTheory

lemma Jhoriz_norm_le (G : Set D.Row) (hG : G.Finite) (sgn x₀ x₁ y v T Z K : ℝ)
    (hK : ∀ u ∈ G, ∀ σ ∈ Set.uIcc x₀ x₁,
      ‖wzIntegral D u ((σ : ℂ) + ((sgn * T : ℝ) : ℂ) * Complex.I) y v Z‖ ≤ K) :
    ‖Jhoriz D G sgn x₀ x₁ y v T Z‖ ≤ (G.ncard : ℝ) * ((2 * Real.pi)⁻¹ * (K * |x₁ - x₀|)) := by
  unfold Jhoriz
  rw [finsum_mem_eq_finite_toFinset_sum _ hG]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ u ∈ hG.toFinset, ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ∫ σ in x₀..x₁, wzIntegral D u ((σ : ℂ) + (sgn * T : ℝ) * Complex.I) y v Z‖ ≤
      (2 * Real.pi)⁻¹ * (K * |x₁ - x₀|) := by
    intro u hu
    have hu' : u ∈ G := hG.mem_toFinset.1 hu
    rw [norm_mul, norm_inv, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real]
    simp only [Complex.norm_ofNat, mul_one, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun σ hσ => ?_)
    exact hK u hu' σ (Set.uIoc_subset_uIcc hσ)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card G hG]

lemma Jtail_norm_le (G : Set D.Row) (hG : G.Finite) (x y v T Z K B : ℝ) (hB : 2 ≤ B)
    (hT : 0 ≤ T) (hK0 : 0 ≤ K)
    (hK : ∀ u ∈ G, ∀ t : ℝ, T < |t| →
      ‖wzIntegral D u ((x : ℂ) + (t : ℂ) * Complex.I) y v Z‖ ≤ K * (1 + |t|) ^ (-B)) :
    ‖Jtail D G x y v T Z‖ ≤ (G.ncard : ℝ) *
      ((2 * Real.pi)⁻¹ * (K * (1 + T) ^ (-(B - 2)) * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)))) := by
  unfold Jtail
  rw [finsum_mem_eq_finite_toFinset_sum _ hG]
  refine (norm_sum_le _ _).trans ?_
  have hint : Integrable (fun t : ℝ => (1 + |t|) ^ (-(2 : ℝ))) := by
    have := integrable_one_add_norm (μ := volume) (E := ℝ) (r := (2 : ℝ)) (by norm_num)
    simpa [Real.norm_eq_abs] using this
  have hmeas : MeasurableSet {t : ℝ | T < |t|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hterm : ∀ u ∈ hG.toFinset, ‖(2 * (Real.pi : ℂ))⁻¹ *
      ∫ t in {t : ℝ | T < |t|}, wzIntegral D u ((x : ℂ) + (t : ℂ) * Complex.I) y v Z‖ ≤
      (2 * Real.pi)⁻¹ * (K * (1 + T) ^ (-(B - 2)) * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ))) := by
    intro u hu
    have hu' : u ∈ G := hG.mem_toFinset.1 hu
    rw [norm_mul, norm_inv, norm_mul]
    simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hT1 : 0 ≤ (1 + T) ^ (-(B - 2)) := Real.rpow_nonneg (by linarith) _
    have hg : Integrable (fun t : ℝ => K * (1 + T) ^ (-(B - 2)) * (1 + |t|) ^ (-(2 : ℝ))) :=
      hint.const_mul _
    calc ‖∫ t in {t : ℝ | T < |t|}, wzIntegral D u ((x : ℂ) + (t : ℂ) * Complex.I) y v Z‖
        ≤ ∫ t in {t : ℝ | T < |t|}, K * (1 + T) ^ (-(B - 2)) * (1 + |t|) ^ (-(2 : ℝ)) := by
          refine norm_integral_le_of_norm_le hg.restrict ?_
          refine (ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun t ht => ?_)
          have ht' : T < |t| := ht
          refine (hK u hu' t ht').trans ?_
          have h1 : (1 + |t|) ^ (-B) = (1 + |t|) ^ (-(B - 2)) * (1 + |t|) ^ (-(2 : ℝ)) := by
            rw [← Real.rpow_add (by positivity)]; congr 1; ring
          have h2 : (1 + |t|) ^ (-(B - 2)) ≤ (1 + T) ^ (-(B - 2)) :=
            Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
          rw [h1, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hK0) (by positivity)
      _ ≤ ∫ t : ℝ, K * (1 + T) ^ (-(B - 2)) * (1 + |t|) ^ (-(2 : ℝ)) :=
          setIntegral_le_integral hg (Filter.Eventually.of_forall fun t => by
            have : 0 ≤ (1 + |t|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
            exact mul_nonneg (mul_nonneg hK0 hT1) this)
      _ = K * (1 + T) ^ (-(B - 2)) * ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := by
          rw [integral_const_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card G hG]

theorem dyad_row_count :
    ∃ C : ℝ, 0 < C ∧ ∀ U : ℝ, 1 ≤ U →
      (dyadRows D U).Finite ∧ ((dyadRows D U).ncard : ℝ) ≤ C * U :=
  DedekindZetaZeroFree.Quantitative.ActualRowCount.dyadRows_count D

lemma entireNumerator (u : D.Row) (hu : u.u ≠ 1) : RowKernelGrowth.EntireNumerator D u := by
  obtain ⟨hp, -⟩ := RowNonprincipal.inducers_nonprincipal D u hu
  obtain ⟨g, hg, hgeq⟩ := RowHeckeBridge.hecke_exists_entire D.recipe.A (D.inducers u).plus hp
  refine ⟨fun s => DedekindZetaZeroFree.Detector.finiteEulerDeletionMask F (RowHeckeBridge.deletionSet D u)
      (fun v => (D.inducers u).plus.character v.asIdeal) s * g s,
    (RowHeckeBridge.mask_differentiable D.recipe.A (D.inducers u).plus hp _
      (RowHeckeBridge.deletionSet_finite D u)).mul hg, fun s hs => ?_⟩
  have hs0 : 0 < s.re := by linarith
  simp only
  rw [RowHeckeBridge.Lpsi_eq_mask_mul D u hp s hs, hgeq s hs0]

theorem wz_height_bound (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ Z : ℝ, 1 ≤ Z → ∀ U : ℝ, U₀ ≤ U →
      ∀ u ∈ goodRows D ρ U, ∀ ξ : ℂ, Scales.goodLine ≤ ξ.re → ξ.re ≤ Scales.rightLine →
        (|ξ.im| = U ^ ρ ∨ (ξ.re = Scales.rightLine ∧ U ^ ρ ≤ |ξ.im|)) →
        ‖wzIntegral D u ξ Scales.wLine Scales.zLine Z‖ ≤
          C * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine * U ^ (1 / 25 + ε) *
            (1 + |ξ.im|) ^ (-B) := by
  obtain ⟨C₁, hC₁, U₁, hU₁, h₁⟩ :=
    RowKernelGrowth.wzIntegral_decay_rect D A_F ρ hA hconv hρ ε hε B hB
  obtain ⟨C₂, hC₂, h₂⟩ := RowKernelGrowth.wzIntegral_decay_right D A_F hconv ε hε B hB
  have hρpos : 0 < ρ := hρ.1
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, max U₁ 2, le_max_right _ _,
    fun Z hZ U hU u hu ξ hξ1 hξ2 hξ => ?_⟩
  have hU1 : U₁ ≤ U := le_trans (le_max_left _ _) hU
  have hU2 : 2 ≤ U := le_trans (le_max_right _ _) hU
  have hZpos : 0 < Z := by linarith
  have hUpos : 0 < U := by linarith
  obtain ⟨⟨hq1, hq2⟩, hnp, hexc⟩ := hu
  have hu1 : u.u ≠ 1 := hnp
  have hent : RowKernelGrowth.EntireNumerator D u := entireNumerator D u hu1
  have hUe : U ^ ((11 / 25 : ℝ) + ε - Scales.zLine) = U ^ (1 / 25 + ε) := by
    congr 1; unfold Scales.zLine; ring
  have hT : 0 ≤ U ^ ρ := Real.rpow_nonneg hUpos.le _
  have hT1 : 1 ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρpos.le
  rcases hξ with him | ⟨hre, him⟩
  · have hle : |ξ.im| ≤ 2 * U ^ ρ := by rw [him]; linarith
    have h := h₁ U hU1 u hu1 hent hq1 hq2 hexc ξ Z hZpos hξ1 hξ2 hle
    have hZe : Z ^ (Scales.xExponent / 2 + ξ.re - 1 + Scales.smoothingExponent * Scales.zLine + Scales.yExponent * (Scales.wLine - 1))
        ≤ Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := by
      refine Real.rpow_le_rpow_of_exponent_le hZ ?_
      unfold Scales.kernelExponent; linarith
    rw [hUe] at h
    refine h.trans ?_
    gcongr
    exact le_max_left _ _
  · have hξeq : ξ = (Scales.rightLine : ℂ) + (ξ.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hre]
    have h := h₂ U hU2 u hu1 hent hq1 hq2 ξ.im Z hZpos
    rw [← hξeq, hUe] at h
    have hZe : Z ^ (Scales.xExponent / 2 + Scales.rightLine - 1 + Scales.smoothingExponent * Scales.zLine +
        Scales.yExponent * (Scales.wLine - 1)) ≤ Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine := by
      refine Real.rpow_le_rpow_of_exponent_le hZ ?_
      unfold Scales.kernelExponent; linarith
    refine h.trans ?_
    gcongr
    exact le_max_right _ _

end helpers

def heightErrors (ρ U Z : ℝ) : ℂ :=
  Jhoriz D (goodRows D ρ U) 1 Scales.goodLine Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z +
  Jhoriz D (goodRows D ρ U) (-1) Scales.rightLine Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z +
  Jtail D (goodRows D ρ U) Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z

theorem rows_height_errors_dyad (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (A₁ : ℝ) (hA₁ : 0 < A₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ U₀ : ℝ, 2 ≤ U₀ ∧ ∀ Z : ℝ, 2 ≤ Z → ∀ U : ℝ, U₀ ≤ U →
      Z ^ Scales.smallCutoffExponent < U → U ≤ Z ^ Scales.largeCutoffExponent →
        ‖heightErrors D ρ U Z‖ ≤
          C * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine * U ^ (26 / 25 + ε - ρ * A₁) := by
  have hρpos : 0 < ρ := hρ.1
  obtain ⟨Cw, hCw, U₁, hU₁, hw⟩ :=
    wz_height_bound D A_F ρ hA hconv hρ (A₁ + 2) ε (by linarith) hε
  obtain ⟨Cr, hCr, hrow⟩ := dyad_row_count D
  obtain ⟨I2, hI2⟩ : ∃ I2 : ℝ, I2 = ∫ t : ℝ, (1 + |t|) ^ (-(2 : ℝ)) := ⟨_, rfl⟩
  have hI2nn : 0 ≤ I2 := by
    rw [hI2]; exact MeasureTheory.integral_nonneg (fun t => Real.rpow_nonneg (by positivity) _)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
      c₀ = (2 * Real.pi)⁻¹ * (2 * |Scales.rightLine - Scales.goodLine| + I2) := ⟨_, rfl⟩
  have hc₀nn : 0 ≤ c₀ := by rw [hc₀]; positivity
  refine ⟨Cr * Cw * (c₀ + 1), mul_pos (mul_pos hCr hCw) (by linarith), U₁, hU₁,
    fun Z hZ U hU _ _ => ?_⟩
  have hU2 : 2 ≤ U := le_trans hU₁ hU
  have hUU : U₁ ≤ U := hU
  have hxle : Scales.goodLine ≤ Scales.rightLine := by
    unfold Scales.goodLine Scales.rightLine Scales.contourOffset; norm_num
  have hGsub : goodRows D ρ U ⊆ dyadRows D U := fun u hu => hu.1
  obtain ⟨hfinD, hcard⟩ := hrow U (by linarith)
  have hGfin : (goodRows D ρ U).Finite := hfinD.subset hGsub
  have hGcard : ((goodRows D ρ U).ncard : ℝ) ≤ Cr * U :=
    (Nat.cast_le.2 (Set.ncard_le_ncard hGsub hfinD)).trans hcard
  obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = Cw * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
      U ^ (1 / 25 + ε) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKd]; positivity
  have hT1 : 1 ≤ U ^ ρ := Real.one_le_rpow (by linarith) hρpos.le
  have hside : ∀ s : ℝ, |s| = 1 → ∀ u ∈ goodRows D ρ U, ∀ σ ∈ Set.uIcc Scales.goodLine Scales.rightLine,
      ‖wzIntegral D u ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        K * (1 + U ^ ρ) ^ (-(A₁ + 2)) := by
    intro s hs u hu σ hσ
    rw [Set.uIcc_of_le hxle] at hσ
    have hre : ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I).im = s * U ^ ρ := by simp
    have habs : |s * U ^ ρ| = U ^ ρ := by
      rw [abs_mul, hs, one_mul, abs_of_nonneg (by linarith)]
    have := hw Z (by linarith) U hUU u hu ((σ : ℂ) + ((s * U ^ ρ : ℝ) : ℂ) * Complex.I)
      (by rw [hre]; exact hσ.1) (by rw [hre]; exact hσ.2)
      (Or.inl (by rw [him, habs]))
    rw [him, habs] at this
    rw [hKd]; exact this
  have htail : ∀ u ∈ goodRows D ρ U, ∀ t : ℝ, U ^ ρ < |t| →
      ‖wzIntegral D u ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I) Scales.wLine Scales.zLine Z‖ ≤
        K * (1 + |t|) ^ (-(A₁ + 2)) := by
    intro u hu t ht
    have hre : ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I).re = Scales.rightLine := by simp
    have him : ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    have := hw Z (by linarith) U hUU u hu ((Scales.rightLine : ℂ) + (t : ℂ) * Complex.I)
      (by rw [hre]; exact hxle) (by rw [hre])
      (Or.inr ⟨hre, by rw [him]; exact ht.le⟩)
    rw [him] at this
    rw [hKd]; exact this
  have hh1 := Jhoriz_norm_le D (goodRows D ρ U) hGfin 1 Scales.goodLine Scales.rightLine Scales.wLine
    Scales.zLine (U ^ ρ) Z _ (hside 1 (by simp))
  have hh2 := Jhoriz_norm_le D (goodRows D ρ U) hGfin (-1) Scales.rightLine Scales.goodLine Scales.wLine
    Scales.zLine (U ^ ρ) Z _
    (fun u hu σ hσ => hside (-1) (by simp) u hu σ (by rwa [Set.uIcc_comm] at hσ))
  have ht := Jtail_norm_le D (goodRows D ρ U) hGfin Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z K
    (A₁ + 2) (by linarith) (by linarith) hK0 htail
  rw [abs_sub_comm] at hh2
  rw [← hI2] at ht
  have hν : (1 + U ^ ρ) ^ (-(A₁ + 2 - 2)) ≤ U ^ (-(ρ * A₁)) := by
    have e1 : -(A₁ + 2 - 2) = -A₁ := by ring
    rw [e1]
    calc (1 + U ^ ρ) ^ (-A₁) ≤ (U ^ ρ) ^ (-A₁) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
      _ = U ^ (-(ρ * A₁)) := by
          rw [← Real.rpow_mul (by linarith)]; congr 1; ring
  have hν' : (1 + U ^ ρ) ^ (-(A₁ + 2)) ≤ U ^ (-(ρ * A₁)) :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hν
  have hν0 : 0 ≤ U ^ (-(ρ * A₁)) := Real.rpow_nonneg (by linarith) _
  have hQ : (0 : ℝ) ≤ Cr * U := by positivity
  have hh1' : ‖Jhoriz D (goodRows D ρ U) 1 Scales.goodLine Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ ≤
      Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * |Scales.rightLine - Scales.goodLine|)) := by
    refine hh1.trans ?_
    gcongr
  have hh2' : ‖Jhoriz D (goodRows D ρ U) (-1) Scales.rightLine Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ ≤
      Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * |Scales.rightLine - Scales.goodLine|)) := by
    refine hh2.trans ?_
    gcongr
  have ht' : ‖Jtail D (goodRows D ρ U) Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ ≤
      Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * I2)) := by
    refine ht.trans ?_
    gcongr
  have hX : U * U ^ (1 / 25 + ε) * U ^ (-(ρ * A₁)) = U ^ (26 / 25 + ε - ρ * A₁) := by
    rw [show 26 / 25 + ε - ρ * A₁ = 1 + (1 / 25 + ε) + (-(ρ * A₁)) by ring,
      Real.rpow_add (by linarith : (0 : ℝ) < U) (1 + (1 / 25 + ε)) (-(ρ * A₁)),
      Real.rpow_add (by linarith : (0 : ℝ) < U) 1 (1 / 25 + ε), Real.rpow_one]
  have hM : 0 ≤ Cr * Cw * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine * U ^ (26 / 25 + ε - ρ * A₁) := by
    positivity
  unfold heightErrors
  calc ‖Jhoriz D (goodRows D ρ U) 1 Scales.goodLine Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z +
        Jhoriz D (goodRows D ρ U) (-1) Scales.rightLine Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z +
        Jtail D (goodRows D ρ U) Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z‖
      ≤ ‖Jhoriz D (goodRows D ρ U) 1 Scales.goodLine Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ +
        ‖Jhoriz D (goodRows D ρ U) (-1) Scales.rightLine Scales.goodLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ +
        ‖Jtail D (goodRows D ρ U) Scales.rightLine Scales.wLine Scales.zLine (U ^ ρ) Z‖ := norm_add₃_le
    _ ≤ Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * |Scales.rightLine - Scales.goodLine|)) +
        Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * |Scales.rightLine - Scales.goodLine|)) +
        Cr * U * ((2 * Real.pi)⁻¹ * (K * U ^ (-(ρ * A₁)) * I2)) := by linarith
    _ = c₀ * (Cr * Cw * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
          (U * U ^ (1 / 25 + ε) * U ^ (-(ρ * A₁)))) := by
        rw [hc₀, hKd]; ring
    _ = c₀ * (Cr * Cw * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
          U ^ (26 / 25 + ε - ρ * A₁)) := by rw [hX]
    _ ≤ (c₀ + 1) * (Cr * Cw * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
          U ^ (26 / 25 + ε - ρ * A₁)) :=
        mul_le_mul_of_nonneg_right (by linarith) hM
    _ = Cr * Cw * (c₀ + 1) * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
          U ^ (26 / 25 + ε - ρ * A₁) := by ring

theorem rows_height_errors (A_F ρ : ℝ) (hA : 0 ≤ A_F) (hconv : ConvexityExponent D A_F)
    (hρ : HeightSpec D A_F ρ) (A₁ : ℝ) (hA₁ : 10 / ρ < A₁) :
    ∃ C : ℝ, 0 < C ∧ ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ Z : ℝ, Z₀ ≤ Z →
      ‖∑ k ∈ intermediateDyads Z, heightErrors D ρ ((2 : ℝ) ^ k) Z‖ ≤
        C * Z ^ (Scales.mainExponent - 1) := by
  have hρpos : 0 < ρ := hρ.1
  have hρlt : ρ < 1 / 10000 := hρ.2.1
  have hρA : 10 < ρ * A₁ := by
    rwa [div_lt_iff₀ hρpos, mul_comm] at hA₁
  have hA₁pos : 0 < A₁ := lt_trans (by positivity) hA₁
  obtain ⟨Cd, hCd, U₀, hU₀, hd⟩ :=
    rows_height_errors_dyad D A_F ρ hA hconv hρ A₁ hA₁pos (1 / 100) (by norm_num)
  refine ⟨3 * Cd, by positivity, max 2 (U₀ ^ (5 : ℝ)), le_max_left _ _, fun Z hZ => ?_⟩
  have hZ2 : 2 ≤ Z := le_trans (le_max_left _ _) hZ
  have hZ1 : 1 ≤ Z := by linarith
  have hZpos : 0 < Z := by linarith
  have hZU : U₀ ≤ Z ^ Scales.smallCutoffExponent := by
    have h5 : U₀ ^ (5 : ℝ) ≤ Z := le_trans (le_max_right _ _) hZ
    have : (U₀ ^ (5 : ℝ)) ^ Scales.smallCutoffExponent ≤ Z ^ Scales.smallCutoffExponent :=
      Real.rpow_le_rpow (by positivity) h5 (by unfold Scales.smallCutoffExponent; norm_num)
    rwa [← Real.rpow_mul (by linarith), show (5 : ℝ) * Scales.smallCutoffExponent = 1 by
      unfold Scales.smallCutoffExponent; norm_num, Real.rpow_one] at this

  obtain ⟨e, he⟩ : ∃ e : ℝ, e = 26 / 25 + 1 / 100 - ρ * A₁ := ⟨_, rfl⟩
  have he0 : e < 0 := by rw [he]; linarith
  obtain ⟨B₁, hB₁⟩ : ∃ B₁ : ℝ, B₁ = Cd * Z ^ Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine *
      Z ^ (Scales.smallCutoffExponent * e) := ⟨_, rfl⟩
  have hB₁0 : 0 ≤ B₁ := by rw [hB₁]; positivity
  have hterm : ∀ k ∈ intermediateDyads Z, ‖heightErrors D ρ ((2 : ℝ) ^ k) Z‖ ≤ B₁ := by
    intro k hk
    unfold intermediateDyads at hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have hκpos : 0 < Z ^ Scales.smallCutoffExponent := Real.rpow_pos_of_pos hZpos _
    have hkU : Z ^ Scales.smallCutoffExponent < (2 : ℝ) ^ k := hk2
    have hkU₀ : U₀ ≤ (2 : ℝ) ^ k := le_trans hZU hkU.le
    have hkl : (2 : ℝ) ^ k ≤ Z ^ Scales.largeCutoffExponent := by
      have hy1 : 1 ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow hZ1 (by unfold Scales.largeCutoffExponent; norm_num)
      have hk3 : (k : ℝ) ≤ Real.logb 2 (Z ^ Scales.largeCutoffExponent) :=
        (Nat.cast_le.2 (Nat.lt_succ_iff.1 hk1)).trans
          (Nat.floor_le (Real.logb_nonneg (by norm_num) hy1))
      calc (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 : ℝ) ^ Real.logb 2 (Z ^ Scales.largeCutoffExponent) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hk3
        _ = Z ^ Scales.largeCutoffExponent := Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
    have h1 := hd Z hZ2 ((2 : ℝ) ^ k) hkU₀ hkU hkl
    rw [← he] at h1
    refine h1.trans ?_
    rw [hB₁]
    have : ((2 : ℝ) ^ k) ^ e ≤ (Z ^ Scales.smallCutoffExponent) ^ e :=
      Real.rpow_le_rpow_of_nonpos hκpos hkU.le he0.le
    rw [← Real.rpow_mul hZpos.le] at this
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hcard : ((intermediateDyads Z).card : ℝ) ≤ 3 * Z := by
    unfold intermediateDyads
    refine le_trans (Nat.cast_le.2 (Finset.card_filter_le _ _)) ?_
    rw [Finset.card_range]
    have hy1 : 1 ≤ Z ^ Scales.largeCutoffExponent := Real.one_le_rpow hZ1 (by unfold Scales.largeCutoffExponent; norm_num)
    have hyZ : Z ^ Scales.largeCutoffExponent ≤ Z := by
      calc Z ^ Scales.largeCutoffExponent ≤ Z ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hZ1 (by unfold Scales.largeCutoffExponent; norm_num)
        _ = Z := Real.rpow_one Z
    have hlog : Real.logb 2 (Z ^ Scales.largeCutoffExponent) ≤ 2 * Z := by
      unfold Real.logb
      have hl2 : 1 / 2 < Real.log 2 := by
        have := Real.log_two_gt_d9; linarith
      rw [div_le_iff₀ (by linarith)]
      have h1 : Real.log (Z ^ Scales.largeCutoffExponent) ≤ Real.log Z :=
        Real.log_le_log (by linarith) hyZ
      have h2 : Real.log Z ≤ Z - 1 := Real.log_le_sub_one_of_pos hZpos
      nlinarith
    have hfl : (⌊Real.logb 2 (Z ^ Scales.largeCutoffExponent)⌋₊ : ℝ) ≤ 2 * Z :=
      (Nat.floor_le (Real.logb_nonneg (by norm_num) hy1)).trans hlog
    push_cast
    linarith
  calc ‖∑ k ∈ intermediateDyads Z, heightErrors D ρ ((2 : ℝ) ^ k) Z‖
      ≤ ∑ k ∈ intermediateDyads Z, ‖heightErrors D ρ ((2 : ℝ) ^ k) Z‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ intermediateDyads Z, B₁ := Finset.sum_le_sum hterm
    _ = ((intermediateDyads Z).card : ℝ) * B₁ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 3 * Z * B₁ := mul_le_mul_of_nonneg_right hcard hB₁0
    _ = 3 * Cd * Z ^ (1 + Scales.kernelExponent Scales.rightLine Scales.wLine Scales.zLine + Scales.smallCutoffExponent * e) := by
        rw [Real.rpow_add hZpos, Real.rpow_add hZpos, Real.rpow_one, hB₁]; ring
    _ ≤ 3 * Cd * Z ^ (Scales.mainExponent - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Real.rpow_le_rpow_of_exponent_le hZ1 ?_
        rw [he]
        unfold Scales.kernelExponent Scales.xExponent Scales.smoothingExponent Scales.yExponent Scales.rightLine Scales.contourOffset Scales.wLine Scales.zLine
          Scales.smallCutoffExponent Scales.mainExponent
        linarith

end

end DedekindZetaZeroFree.Quantitative.RowsHeightErrors
