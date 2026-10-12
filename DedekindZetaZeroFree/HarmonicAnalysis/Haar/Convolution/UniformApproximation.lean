module

public import DedekindZetaZeroFree.Eisenstein.Residues.MetaplecticRealizations
public import DedekindZetaZeroFree.RepresentationTheory.Compact.RepresentativeDensity

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

local instance finite_stage_borel_measurable (K : Subgroup (G F ζ hζ)) : MeasurableSpace K := borel K
local instance finiteStageBorelSpace (K : Subgroup (G F ζ hζ)) : BorelSpace K := ⟨rfl⟩

def compactConvolution (K : Subgroup (G F ζ hζ)) (μ : Measure K)
    (h : C(K, ℂ)) (u : Functions F ζ hζ) : Functions F ζ hζ :=
  fun g => ∫ k : K, h k * u (g * k.val) ∂μ

theorem representative_convolution_uniform_approximation
    (K : Subgroup (G F ζ hζ)) (hK : IsCompact (K : Set (G F ζ hζ)))
    (u : Functions F ζ hζ) (hu : Continuous u)
    (C : Set (G F ζ hζ)) (hC : IsCompact C) (ε : ℝ) (hε : 0 < ε) :
    ∃ (μ : Measure K), μ.IsHaarMeasure ∧ IsProbabilityMeasure μ ∧
      ∃ h : C(K, ℂ), h ∈ TauCeti.representativeSubmodule ℂ K ∧
        ∀ y ∈ C, ‖compactConvolution F ζ hζ K μ h u y - u y‖ < ε := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let f : C(K, C(C, ℂ)) := ContinuousMap.curry
    ⟨fun p : K × C => u (p.2.val * p.1.val),
      hu.comp ((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp continuous_fst))⟩
  have hf (k : K) (y : C) : f k y = u (y.val * k.val) := rfl
  let V : Set K := {k | ‖f k - f 1‖ < ε / 2}
  have hV : V ∈ 𝓝 (1 : K) := by
    have ht : ContinuousAt (fun k : K => ‖f k - f 1‖) 1 :=
      (f.continuous.sub continuous_const).norm.continuousAt
    have ht' := ht.preimage_mem_nhds (Iio_mem_nhds (show ‖f 1 - f 1‖ < ε / 2 by
      simpa using half_pos hε))
    exact ht'
  obtain ⟨ψ, hψ⟩ := TauCeti.exists_isMollifier (𝕜 := ℂ) hV
  have hδ : 0 < ε / (2 * (‖f‖ + 1)) := by positivity
  obtain ⟨h, hh, hclose⟩ := Metric.mem_closure_iff.mp
    (TauCeti.dense_representativeSubmodule ℂ K ψ) _ hδ
  have hclose' : ‖h - ψ‖ < ε / (2 * (‖f‖ + 1)) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hclose
  let μ := TauCeti.haarProb K
  letI : IsProbabilityMeasure μ := inferInstance
  refine ⟨μ, TauCeti.isHaarMeasure_haarProb K, inferInstance, h, hh, ?_⟩
  intro y hy
  let y' : C := ⟨y, hy⟩
  have hi (a : C(K, ℂ)) : Integrable (fun k : K => a k * u (y * k.val)) μ := by
    exact (a.continuous.mul (hu.comp (continuous_const.mul continuous_subtype_val))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hd (k : K) : ‖u (y * k.val)‖ ≤ ‖f‖ := by
    calc
      ‖u (y * k.val)‖ = ‖f k y'‖ := rfl
      _ ≤ ‖f k‖ := (f k).norm_coe_le_norm y'
      _ ≤ ‖f‖ := f.norm_coe_le_norm k
  have hnear (k : K) (hk : k ∈ V) : ‖u (y * k.val) - u y‖ ≤ ε / 2 := by
    have he : (f k - f 1) y' = u (y * k.val) - u y := by simp [hf, y']
    rw [← he]
    exact ((f k - f 1).norm_coe_le_norm y').trans (le_of_lt hk)
  have herror : ‖(∫ k : K, h k * u (y * k.val) ∂μ) -
      ∫ k : K, ψ k * u (y * k.val) ∂μ‖ < ε / 2 := by
    rw [← integral_sub (hi h) (hi ψ)]
    have hb := norm_integral_le_of_norm_le_const (μ := μ) (C := ‖h - ψ‖ * ‖f‖)
      (Filter.Eventually.of_forall (fun k : K => show
        ‖h k * u (y * k.val) - ψ k * u (y * k.val)‖ ≤ ‖h - ψ‖ * ‖f‖ from by
        rw [← sub_mul, norm_mul]
        exact mul_le_mul ((h - ψ).norm_coe_le_norm k) (hd k) (norm_nonneg _) (norm_nonneg _)))
    have hb' : ‖∫ k : K, h k * u (y * k.val) - ψ k * u (y * k.val) ∂μ‖ ≤
        ‖h - ψ‖ * ‖f‖ := by simpa using hb
    refine hb'.trans_lt ?_
    calc
      ‖h - ψ‖ * ‖f‖ ≤ ‖h - ψ‖ * (‖f‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      _ < (ε / (2 * (‖f‖ + 1))) * (‖f‖ + 1) :=
        mul_lt_mul_of_pos_right hclose' (by positivity)
      _ = ε / 2 := by field_simp
  have hmain : ‖(∫ k : K, ψ k * u (y * k.val) ∂μ) - u y‖ ≤ ε / 2 := by
    have hiψ : Integrable (fun k : K => ψ k * u y) μ :=
      (ψ.continuous.mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have he : (∫ k : K, ψ k * u (y * k.val) ∂μ) - u y =
        ∫ k : K, ψ k * (u (y * k.val) - u y) ∂μ := by
      simp_rw [mul_sub]
      rw [integral_sub (hi ψ) hiψ, integral_mul_const, hψ.integral_eq_one, one_mul]
    rw [he]
    have hiN : Integrable (fun k : K => ‖ψ k‖ * (ε / 2)) μ :=
      (ψ.continuous.norm.mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      ‖∫ k : K, ψ k * (u (y * k.val) - u y) ∂μ‖ ≤
          ∫ k : K, ‖ψ k‖ * (ε / 2) ∂μ := by
        apply norm_integral_le_of_norm_le hiN
        apply Filter.Eventually.of_forall
        intro k
        by_cases hk : k ∈ V
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hnear k hk) (norm_nonneg _)
        · simp [hψ.eq_zero_of_notMem k hk]
      _ = ε / 2 := by rw [integral_mul_const, hψ.integral_norm_eq_one, one_mul]
  change ‖(∫ k : K, h k * u (y * k.val) ∂μ) - u y‖ < ε
  calc
    ‖(∫ k : K, h k * u (y * k.val) ∂μ) - u y‖ ≤
        ‖(∫ k : K, h k * u (y * k.val) ∂μ) -
          ∫ k : K, ψ k * u (y * k.val) ∂μ‖ +
        ‖(∫ k : K, ψ k * u (y * k.val) ∂μ) - u y‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

end DedekindZetaZeroFree.KPLiteralPeriod.HCCoreDensity.FiniteStageApproximation

end
