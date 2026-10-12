module

public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineL2.ClosedCentralCharacterSector

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory

namespace DedekindZetaZeroFree.KPContSectorExactBorelRepresentatives

open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContSectorClosedLpSubspace

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)

local instance : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _

def average (g : CoveredSpherical F ζ hζ U → ℂ) :
    CoveredSpherical F ζ hζ U → ℂ :=
  fun v => (3 : ℂ)⁻¹ * ∑ ε : rootsOfUnity 3 F,
    (chi F ζ hζ ε : ℂ)⁻¹ * g (z F ζ hζ U ε v)

private lemma z_mul (ε ε' : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U) :
    z F ζ hζ U (ε * ε') v = z F ζ hζ U ε (z F ζ hζ U ε' v) := by
  change (ε * ε') • v = ε • (ε' • v)
  exact mul_smul ε ε' v

theorem average_measurable (g : CoveredSpherical F ζ hζ U → ℂ)
    (hg : Measurable g) : Measurable (average F ζ hζ U g) := by
  letI : BorelSpace (CoveredSpherical F ζ hζ U) := ⟨rfl⟩
  unfold average
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro ε _
  exact measurable_const.mul (hg.comp (z F ζ hζ U ε).continuous.measurable)

theorem average_equivariant (g : CoveredSpherical F ζ hζ U → ℂ)
    (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U) :
    average F ζ hζ U g (z F ζ hζ U ε v) =
      (chi F ζ hζ ε : ℂ) * average F ζ hζ U g v := by
  show (3 : ℂ)⁻¹ * (∑ ε' : rootsOfUnity 3 F,
        (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U ε' (z F ζ hζ U ε v))) =
      (chi F ζ hζ ε : ℂ) * ((3 : ℂ)⁻¹ * ∑ ε' : rootsOfUnity 3 F,
        (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U ε' v))
  have hstep : (∑ ε' : rootsOfUnity 3 F,
        (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U ε' (z F ζ hζ U ε v)))
      = ∑ ε' : rootsOfUnity 3 F, (chi F ζ hζ (ε' * ε⁻¹))⁻¹ * g (z F ζ hζ U ε' v) := by
    rw [show (∑ ε' : rootsOfUnity 3 F,
          (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U ε' (z F ζ hζ U ε v)))
        = ∑ ε' : rootsOfUnity 3 F, (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U (ε' * ε) v) from by
      refine Finset.sum_congr rfl (fun ε' _ => ?_)
      rw [z_mul]]
    rw [← Equiv.sum_comp (Equiv.mulRight ε)
      (fun ε' => (chi F ζ hζ (ε' * ε⁻¹))⁻¹ * g (z F ζ hζ U ε' v))]
    refine Finset.sum_congr rfl (fun ε' _ => ?_)
    simp [mul_assoc]
  have h2 : (∑ ε' : rootsOfUnity 3 F, (chi F ζ hζ (ε' * ε⁻¹))⁻¹ * g (z F ζ hζ U ε' v))
      = (chi F ζ hζ ε : ℂ) * ∑ ε' : rootsOfUnity 3 F,
          (chi F ζ hζ ε')⁻¹ * g (z F ζ hζ U ε' v) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ε' _ => ?_)
    simp only [map_mul, map_inv, Circle.coe_inv, Circle.coe_mul]
    rw [mul_inv, inv_inv]
    ring
  rw [hstep, h2]
  ring

theorem average_represents (u : H F ζ hζ R U)
    (g : CoveredSpherical F ζ hζ U → ℂ) (hg : Measurable g)
    (hgLp : MemLp g 2 (coveredMeasure F ζ hζ R U))
    (hgu : hgLp.toLp g = (u : CoveredL2 F ζ hζ R U)) :
    average F ζ hζ U g =ᵐ[coveredMeasure F ζ hζ R U] g ∧
    ∃ hf : MemLp (average F ζ hζ U g) 2 (coveredMeasure F ζ hζ R U),
      hf.toLp (average F ζ hζ U g) = (u : CoveredL2 F ζ hζ R U) := by
  set μ : Measure (CoveredSpherical F ζ hζ U) := coveredMeasure F ζ hζ R U
  set v : CoveredL2 F ζ hζ R U := (u : CoveredL2 F ζ hζ R U)
  have hgen : ∀ ε : rootsOfUnity 3 F,
      (v : CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε =ᵐ[μ]
        (chi F ζ hζ ε : ℂ) • (v : CoveredSpherical F ζ hζ U → ℂ) :=
    (mem_H_iff F ζ hζ R U v).mp u.2
  have hvu : (v : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[μ] g := by
    rw [← hgu]; exact MemLp.coeFn_toLp hgLp
  have hgε : ∀ ε : rootsOfUnity 3 F,
      g ∘ z F ζ hζ U ε =ᵐ[μ] (chi F ζ hζ ε : ℂ) • g := by
    intro ε
    have h1 : (v : CoveredSpherical F ζ hζ U → ℂ) ∘ z F ζ hζ U ε =ᵐ[μ]
        g ∘ z F ζ hζ U ε :=
      (KPContSectorCentralHaarInvariance.z_measurePreserving F ζ hζ R U ε).quasiMeasurePreserving.ae_eq_comp
        hvu
    have h2 : (chi F ζ hζ ε : ℂ) • (v : CoveredSpherical F ζ hζ U → ℂ) =ᵐ[μ]
        (chi F ζ hζ ε : ℂ) • g := by
      filter_upwards [hvu] with x hx
      simp only [Pi.smul_apply, hx]
    exact h1.symm.trans ((hgen ε).trans h2)
  have hcard : Fintype.card (rootsOfUnity 3 F) = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact (IsPrimitiveRoot.pow (n := 12) (a := 4) (b := 3) (by norm_num) hζ
      (by norm_num)).card_rootsOfUnity
  have havg : average F ζ hζ U g =ᵐ[μ] g := by
    filter_upwards [(Filter.eventually_all).mpr (fun ε => hgε ε)] with w hw
    unfold average
    have hterm : ∀ ε : rootsOfUnity 3 F,
        (chi F ζ hζ ε : ℂ)⁻¹ * g (z F ζ hζ U ε w) = g w := by
      intro ε
      have hwε : g (z F ζ hζ U ε w) = (chi F ζ hζ ε : ℂ) * g w := by
        simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hw ε
      rw [hwε, ← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero (chi F ζ hζ ε)), one_mul]
    rw [Finset.sum_congr rfl (fun ε _ => hterm ε)]
    have hsum : (∑ _ : rootsOfUnity 3 F, g w) = (3 : ℂ) * g w := by
      rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, Nat.cast_ofNat]
    rw [hsum, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), one_mul]
  refine ⟨havg, ?_⟩
  have hfLp : MemLp (average F ζ hζ U g) 2 μ := (memLp_congr_ae havg).mpr hgLp
  refine ⟨hfLp, ?_⟩
  rw [MemLp.toLp_congr hfLp hgLp havg]
  exact hgu

theorem average_independent (u : H F ζ hζ R U)
    (g₁ g₂ : CoveredSpherical F ζ hζ U → ℂ)
    (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
    (hg₁Lp : MemLp g₁ 2 (coveredMeasure F ζ hζ R U))
    (hg₂Lp : MemLp g₂ 2 (coveredMeasure F ζ hζ R U))
    (h₁u : hg₁Lp.toLp g₁ = (u : CoveredL2 F ζ hζ R U))
    (h₂u : hg₂Lp.toLp g₂ = (u : CoveredL2 F ζ hζ R U)) :
    average F ζ hζ U g₁ =ᵐ[coveredMeasure F ζ hζ R U]
      average F ζ hζ U g₂ := by
  have h1 := (average_represents F ζ hζ R U u g₁ hg₁ hg₁Lp h₁u).1
  have h2 := (average_represents F ζ hζ R U u g₂ hg₂ hg₂Lp h₂u).1
  have h12 : g₁ =ᵐ[coveredMeasure F ζ hζ R U] g₂ :=
    (MemLp.coeFn_toLp hg₁Lp).symm.trans
      ((Filter.EventuallyEq.of_eq (by rw [h₁u, h₂u])).trans (MemLp.coeFn_toLp hg₂Lp))
  exact h1.trans (h12.trans h2.symm)

theorem equivariant_vanish_of_fixed (f : CoveredSpherical F ζ hζ U → ℂ)
    (hf : ∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
      f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v)
    (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U)
    (hfixed : z F ζ hζ U ε v = v) (hchi : (chi F ζ hζ ε : ℂ) ≠ 1) :
    f v = 0 := by
  have h := hf ε v
  rw [hfixed] at h
  have h0 : ((chi F ζ hζ ε : ℂ) - 1) * f v = 0 := by
    rw [sub_mul, one_mul, ← h, sub_self]
  exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hchi)

theorem exists_exact_borel_representative (u : H F ζ hζ R U) :
    ∃ (g : CoveredSpherical F ζ hζ U → ℂ) (hg : Measurable g)
      (hgLp : MemLp g 2 (coveredMeasure F ζ hζ R U)),
      hgLp.toLp g = (u : CoveredL2 F ζ hζ R U) ∧
      ∃ (f : CoveredSpherical F ζ hζ U → ℂ) (hf : Measurable f)
        (hfLp : MemLp f 2 (coveredMeasure F ζ hζ R U)),
        f = average F ζ hζ U g ∧
        hfLp.toLp f = (u : CoveredL2 F ζ hζ R U) ∧
        (∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
          f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v) ∧
        (∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
          z F ζ hζ U ε v = v → (chi F ζ hζ ε : ℂ) ≠ 1 → f v = 0) := by
  set μ : Measure (CoveredSpherical F ζ hζ U) := coveredMeasure F ζ hζ R U
  set v : CoveredL2 F ζ hζ R U := (u : CoveredL2 F ζ hζ R U)
  have hvLp : MemLp (v : CoveredSpherical F ζ hζ U → ℂ) 2 μ := Lp.memLp v
  have hv_asm : AEStronglyMeasurable (v : CoveredSpherical F ζ hζ U → ℂ) μ :=
    hvLp.aestronglyMeasurable
  let g : CoveredSpherical F ζ hζ U → ℂ := hv_asm.mk (v : CoveredSpherical F ζ hζ U → ℂ)
  have hg : Measurable g := hv_asm.measurable_mk
  have hg_ae : g =ᵐ[μ] (v : CoveredSpherical F ζ hζ U → ℂ) := hv_asm.ae_eq_mk.symm
  have hgLp : MemLp g 2 μ := (memLp_congr_ae hg_ae).mpr hvLp
  have hgu : hgLp.toLp g = v := by
    rw [MemLp.toLp_congr hgLp hvLp hg_ae]
    exact Lp.toLp_coeFn v hvLp
  have hfmeas : Measurable (average F ζ hζ U g) := average_measurable F ζ hζ U g hg
  obtain ⟨havg, hfLp, hfLp_toLp⟩ := average_represents F ζ hζ R U u g hg hgLp hgu
  refine ⟨g, hg, hgLp, hgu, average F ζ hζ U g, hfmeas, hfLp, rfl, hfLp_toLp, ?_, ?_⟩
  · intro ε w
    exact average_equivariant F ζ hζ U g ε w
  · intro ε w hfixed hchi
    exact equivariant_vanish_of_fixed F ζ hζ U (average F ζ hζ U g)
      (fun ε w => average_equivariant F ζ hζ U g ε w) ε w hfixed hchi

end DedekindZetaZeroFree.KPContSectorExactBorelRepresentatives

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContSectorClosedLpSubspace KPContSectorExactBorelRepresentatives

theorem kp_cont_sector_exact_borel_representatives
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ) :
    (∀ u : H F ζ hζ R U,
      ∃ (f : CoveredSpherical F ζ hζ U → ℂ) (hf : Measurable f)
        (hfLp : MemLp f 2 (coveredMeasure F ζ hζ R U)),
        hfLp.toLp f = (u : CoveredL2 F ζ hζ R U) ∧
        (∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
          f (z F ζ hζ U ε v) = (chi F ζ hζ ε : ℂ) * f v) ∧
        (∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
          z F ζ hζ U ε v = v → (chi F ζ hζ ε : ℂ) ≠ 1 → f v = 0)) ∧
    (∀ (u : H F ζ hζ R U) (g : CoveredSpherical F ζ hζ U → ℂ)
      (hg : Measurable g) (hgLp : MemLp g 2 (coveredMeasure F ζ hζ R U)),
      hgLp.toLp g = (u : CoveredL2 F ζ hζ R U) →
      Measurable (average F ζ hζ U g) ∧
      average F ζ hζ U g =ᵐ[coveredMeasure F ζ hζ R U] g ∧
      (∃ hfLp : MemLp (average F ζ hζ U g) 2 (coveredMeasure F ζ hζ R U),
        hfLp.toLp (average F ζ hζ U g) = (u : CoveredL2 F ζ hζ R U)) ∧
      (∀ (ε : rootsOfUnity 3 F) (v : CoveredSpherical F ζ hζ U),
        average F ζ hζ U g (z F ζ hζ U ε v) =
          (chi F ζ hζ ε : ℂ) * average F ζ hζ U g v)) ∧
    (∀ (u : H F ζ hζ R U) (g₁ g₂ : CoveredSpherical F ζ hζ U → ℂ)
      (hg₁ : Measurable g₁) (hg₂ : Measurable g₂)
      (hg₁Lp : MemLp g₁ 2 (coveredMeasure F ζ hζ R U))
      (hg₂Lp : MemLp g₂ 2 (coveredMeasure F ζ hζ R U)),
      hg₁Lp.toLp g₁ = (u : CoveredL2 F ζ hζ R U) →
      hg₂Lp.toLp g₂ = (u : CoveredL2 F ζ hζ R U) →
      average F ζ hζ U g₁ =ᵐ[coveredMeasure F ζ hζ R U]
        average F ζ hζ U g₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u
    obtain ⟨g, hg, hgLp, hgu, f, hf, hfLp, hfavg, hfLp_toLp, heq, hvanish⟩ :=
      exists_exact_borel_representative F ζ hζ R U u
    exact ⟨f, hf, hfLp, hfLp_toLp, heq, hvanish⟩
  · intro u g hg hgLp hgu
    exact ⟨average_measurable F ζ hζ U g hg,
      (average_represents F ζ hζ R U u g hg hgLp hgu).1,
      (average_represents F ζ hζ R U u g hg hgLp hgu).2,
      fun ε v => average_equivariant F ζ hζ U g ε v⟩
  · intro u g₁ g₂ hg₁ hg₂ hg₁Lp hg₂Lp h₁u h₂u
    exact average_independent F ζ hζ R U u g₁ g₂ hg₁ hg₂ hg₁Lp hg₂Lp h₁u h₂u

end DedekindZetaZeroFree

end
