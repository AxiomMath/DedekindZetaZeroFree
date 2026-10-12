module

public import DedekindZetaZeroFree.LFunctions.Hecke.UniformRegularizationBoundaryBounds
public import DedekindZetaZeroFree.LFunctions.Hecke.RegularizationStripGrowth
public import DedekindZetaZeroFree.Analysis.PhragmenLindelof.PolynomialBoundaryBounds
public import DedekindZetaZeroFree.Arithmetic.Ideals.FrequencyNormValuations
public import DedekindZetaZeroFree.LFunctions.Hecke.NonprincipalMaskedRowInducers

@[expose] public section

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped NumberField

theorem nonprincipal_hecke_positive_strip_bound
    (F : Type) [Field F] [NumberField F] (hF : NumberField.IsTotallyComplex F)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ, 0 < B ∧
        ∀ (𝔪 : Ideal (𝓞 F)) (hm : 𝔪 ≠ ⊥)
          (χ : RayClassCharacter F 𝔪) (hprim : χ.IsPrimitive)
          (hnp : ¬ χ.IsPrincipal) (w : ℂ),
          a ≤ w.re → w.re ≤ b →
          ‖(nonprincipalRayHeckeData F hF 𝔪 hm χ hprim hnp).L w‖ ≤
            B * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ (1 / 2 + ε) *
              (2 + |w.im|) ^ d := by
  classical
  set k : ℕ := 2 * NumberField.InfinitePlace.nrComplexPlaces F + 1 with hk
  refine ⟨(k : ℝ), by positivity, ?_⟩
  intro ε hε
  set δ : ℝ := min (ε / 2) (1 / 10) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; exact lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 / 10 := by rw [hδ]; exact min_le_right _ _
  have hδε : δ ≤ ε := by
    rw [hδ]
    calc min (ε / 2) (1 / 10) ≤ ε / 2 := min_le_left _ _
      _ ≤ ε := by linarith
  obtain ⟨C0, hC0pos, hnb, _hpb⟩ :=
    heckeEntireRegularizations_uniform_boundaries F hF δ hδpos hδle
  set C : ℝ := max (6 ^ k * C0) (idealAbsoluteSum F (1 + δ)) + 1 with hC
  have hCpos : 0 < C := by
    rw [hC]
    have h6 : 0 < 6 ^ k * C0 := by positivity
    have hle := le_max_left (6 ^ k * C0) (idealAbsoluteSum F (1 + δ))
    linarith
  refine ⟨C, hCpos, ?_⟩
  intro 𝔪 hm χ hprim hnp w hwlo hwhi
  let D := nonprincipalRayHeckeData F hF 𝔪 hm χ hprim hnp
  have hNm1 : (1 : ℝ) ≤ 1 + (Ideal.absNorm 𝔪 : ℝ) := by
    have h := Nat.cast_nonneg (α := ℝ) (Ideal.absNorm 𝔪)
    linarith
  have hNeq : ∀ t : ℂ, 0 < t.re →
      nonprincipalHeckeEntireContinuation F 𝔪 χ D t = D.L t :=
    fun t ht => nonprincipalHeckeEntireContinuation_eq F hF 𝔪 hm χ D t ht
  have hNdiff : Differentiable ℂ (nonprincipalHeckeEntireContinuation F 𝔪 χ D) :=
    nonprincipalHeckeEntireContinuation_differentiable F hF 𝔪 hm χ D
  obtain ⟨M, Bg, hM, hBg, hgr⟩ :=
    nonprincipalHeckeEntireContinuation_quadratic_strip_growth F hF 𝔪 hm χ D
      (-δ) (1 + δ) (by linarith)
  have hPL : ∀ t : ℂ, -δ ≤ t.re ∧ t.re ≤ 1 + δ →
      ‖nonprincipalHeckeEntireContinuation F 𝔪 χ D t‖ ≤
        6 ^ k * (C0 * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ)) *
          (2 + |t.im|) ^ k := by
    refine norm_le_on_closed_strip_of_polynomial_boundary δ hδpos hδle k
      (C0 * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ))
      (by positivity) (nonprincipalHeckeEntireContinuation F 𝔪 χ D)
      hNdiff.diffContOnCl ?_ ?_
    · exact ⟨M, Bg, hM, hBg, fun t ht => hgr t (le_of_lt ht.1) (le_of_lt ht.2)⟩
    · intro t ht
      have hb := (hnb 𝔪 hm χ hprim hnp D).1 t ht
      simpa only [hk] using hb
  have hwpos : 0 < w.re := lt_of_lt_of_le ha hwlo
  rw [← hNeq w hwpos]
  rw [Real.rpow_natCast]
  by_cases hcase : w.re ≤ 1 + δ
  · have hPLs := hPL w ⟨by linarith [hδpos], hcase⟩
    have hCge : 6 ^ k * C0 ≤ C := by
      rw [hC]
      exact le_trans (le_max_left (6 ^ k * C0) (idealAbsoluteSum F (1 + δ)))
        (le_add_of_nonneg_right (by norm_num))
    have hmono : (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) ≤
        (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hNm1 (by linarith)
    have hA : 6 ^ k * (C0 * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ)) ≤
        C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) := by
      calc 6 ^ k * (C0 * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ))
          = (6 ^ k * C0) * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ) := by
            ring
        _ ≤ (6 ^ k * C0) * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) :=
            mul_le_mul_of_nonneg_right hCge (Real.rpow_nonneg (by linarith) _)
    calc ‖nonprincipalHeckeEntireContinuation F 𝔪 χ D w‖
        ≤ 6 ^ k * (C0 * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + δ)) *
            (2 + |w.im|) ^ k := hPLs
      _ ≤ C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) *
            (2 + |w.im|) ^ k := mul_le_mul_of_nonneg_right hA (by positivity)
  · rw [not_le] at hcase

    have hright : ‖nonprincipalHeckeEntireContinuation F 𝔪 χ D w‖ ≤
        idealAbsoluteSum F (1 + δ) := by
      rw [nonprincipalHeckeEntireContinuation_eq F hF 𝔪 hm χ D w (by linarith)]
      exact heckeDirichlet_hasSum_norm_le F (1 + δ) (by linarith) 𝔪 hm χ w
        (by linarith) (D.L w) (D.series w (by linarith))
    have hCge : idealAbsoluteSum F (1 + δ) ≤ C := by
      rw [hC]
      exact le_trans (le_max_right (6 ^ k * C0) (idealAbsoluteSum F (1 + δ)))
        (le_add_of_nonneg_right (by norm_num))
    have h1 : (1 : ℝ) ≤ (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) :=
      Real.one_le_rpow hNm1 (by positivity)
    have h2 : (1 : ℝ) ≤ (2 + |w.im|) ^ k :=
      one_le_pow₀ (by have h : (0 : ℝ) ≤ |w.im| := abs_nonneg _; linarith)
    have hXY : (1 : ℝ) ≤
        (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) * (2 + |w.im|) ^ k := by
      simpa using mul_le_mul h1 h2 (by norm_num : (0 : ℝ) ≤ 1)
        (le_trans (by norm_num : (0 : ℝ) ≤ 1) h1)
    calc ‖nonprincipalHeckeEntireContinuation F 𝔪 χ D w‖
        ≤ idealAbsoluteSum F (1 + δ) := hright
      _ ≤ C := hCge
      _ ≤ C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) *
            (2 + |w.im|) ^ k := by
          have h := le_mul_of_one_le_right hCpos.le hXY
          calc C ≤ C * ((1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) *
                (2 + |w.im|) ^ k) := h
            _ = C * (1 + (Ideal.absNorm 𝔪 : ℝ)) ^ ((1 : ℝ) / 2 + ε) *
                (2 + |w.im|) ^ k := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem raw_deletion_mask_subpower
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (a ε : ℝ) (ha : 0 < a) (hε : 0 < ε) :
    ∃ B : ℝ, 0 < B ∧ ∀ (u : Frequency R)
      (c : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℂ) (w : ℂ),
      (∀ v ∈ RawHeckeRows.rawDeletionSet (U u), ‖c v‖ ≤ 1) →
      a ≤ w.re →
      ‖Detector.finiteEulerDeletionMask F
        (RawHeckeRows.rawDeletionSet (U u)) c w‖ ≤
        B * (frequencyNorm R u) ^ ε := by
  classical
  obtain ⟨C, hC, hb⟩ := Detector.frequency_finite_euler_masks_subpower F
    (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) R.A.Sf.finite_toSet
    a ε ha hε
  refine ⟨C, hC, ?_⟩
  intro u c w hc hw
  have hu : (U u).u ≠ 0 := (U u).generates.1

  have hsub : RawHeckeRows.rawDeletionSet (U u) ⊆
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ∪
        Detector.exteriorFrequencyPrimeSupport F
          (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (U u).u := by
    intro v hv
    by_cases hvS : v ∈ R.A.Sf
    · exact Or.inl (Finset.mem_coe.mpr hvS)
    · have hv' : (U u).ideal.val ≤ v.asIdeal := by
        rcases hv with h | h
        · exact absurd (Finset.mem_coe.mp h) hvS
        · exact h
      refine Or.inr ⟨by simpa only [Finset.mem_coe] using hvS, ?_⟩

      let M : Ideal R.A.R :=
        { carrier := {x | v.valuation F (x : F) < 1}
          zero_mem' := by simp
          add_mem' := by
            intro x y hx hy
            refine lt_of_le_of_lt (by
              simpa only [Subalgebra.coe_add] using
                Valuation.map_add (v.valuation F) (x : F) (y : F)) (max_lt hx hy)
          smul_mem' := by
            intro x y hy
            show v.valuation F ((x * y : R.A.R) : F) < 1
            have hx : v.valuation F (x : F) ≤ 1 := x.property v hvS
            have hxy : v.valuation F ((x * y : R.A.R) : F) =
                v.valuation F (x : F) * v.valuation F (y : F) := by
              rw [show ((x * y : R.A.R) : F) = (x : F) * (y : F) from by
                simp only [Subalgebra.coe_mul], map_mul]
            rw [hxy]
            exact (mul_le_of_le_one_left' hx).trans_lt hy }
      have hmapM : Ideal.map (algebraMap (𝓞 F) R.A.R) v.asIdeal ≤ M := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        change v.valuation F (((algebraMap (𝓞 F) R.A.R) x : R.A.R) : F) < 1
        rw [show (((algebraMap (𝓞 F) R.A.R) x : R.A.R) : F) = (x : F) from by
          simp only [Subalgebra.coe_algebraMap]]
        exact (v.valuation_lt_one_iff_mem (K := F) x).mpr hx
      have hspan : (U u).u ∈ R.A.extendIdeal (U u).ideal := by
        rw [← (U u).generates.2]
        exact Ideal.mem_span_singleton_self _
      have hmem : (U u).u ∈ Ideal.map (algebraMap (𝓞 F) R.A.R) v.asIdeal :=
        Ideal.map_mono hv' (by simpa [SArithmeticData.extendIdeal] using hspan)
      exact hmapM hmem
  have hfreq : (Detector.frequencyNorm F
      (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (U u).u : ℝ) =
      frequencyNorm R u := by
    rw [frequencyNorm, Detector.frequencyNorm, hU u]
    rfl
  obtain ⟨-, hnorm, -⟩ := (hb ((U u).u) hu).2.2
    (RawHeckeRows.rawDeletionSet (U u)) hsub c w hc hw
  rw [hfreq] at hnorm
  exact hnorm

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped NumberField
variable {F : Type} [Field F] [NumberField F]

theorem deleted_exterior_continuation_eq
    (A : SArithmeticData F) (ν : Detector.PrimitiveFrequencyCharacter F)
    (H : NonprincipalRayHeckeData F ν.conductor ν.character)
    (D : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) (hD : D.Finite)
    (hSD : (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) ⊆ D)
    (c : A.Exterior → ℂ)
    (hc : ∀ I : A.Exterior,
      c I = Detector.deletedPrimitiveIdealCoefficient F ν D I.val)
    (l : ℂ → ℂ) (hl : DifferentiableOn ℂ l {s : ℂ | 0 < s.re})
    (hseries : ∀ s : ℂ, 1 < s.re →
      l s = InitialSeparatedEuler.dirichletSeries c s) :
    ∀ w : ℂ, 0 < w.re →
      l w = H.L w * Detector.finiteEulerDeletionMask F D
        (fun v => ν.character v.asIdeal) w := by
  classical
  let T : Set ℂ := {s : ℂ | 0 < s.re}
  have hT : IsOpen T := isOpen_lt continuous_const Complex.continuous_re
  have hLmero : MeromorphicOn H.L T := (H.L_holo.analyticOnNhd hT).meromorphicOn
  obtain ⟨hmaskdiff, -, hBs⟩ :=
    Detector.deleted_primitive_L_continuation F ν D hD T H.L hLmero H.series
  let g : ℂ → ℂ := fun s => H.L s *
    Detector.finiteEulerDeletionMask F D (fun v => ν.character v.asIdeal) s
  have hg : AnalyticOnNhd ℂ g T :=
    (H.L_holo.mul (hmaskdiff.differentiableOn.mono (Set.subset_univ T))).analyticOnNhd hT
  have hl' : AnalyticOnNhd ℂ l T := hl.analyticOnNhd hT
  have heq : ∀ s : ℂ, 1 < s.re → l s = g s := by
    intro s hs
    have hdir : InitialSeparatedEuler.dirichletSeries c s =
        ∑' I : Ideal (𝓞 F), Detector.deletedPrimitiveIdealCoefficient F ν D I *
          (Ideal.absNorm I : ℂ) ^ (-s) := by
      have hzero : ∀ I : Ideal (𝓞 F), ¬ (I ≠ ⊥ ∧ I ⊔ A.cS = ⊤) →
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s) = 0 := by
        intro I hn
        have hc0 : Detector.deletedPrimitiveIdealCoefficient F ν D I = 0 := by
          by_cases hbot : I = ⊥
          · subst hbot
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            by_cases hex : ∃ v ∈ D, (⊥ : Ideal (𝓞 F)) ≤ v.asIdeal
            · simp [hex]
            · simp only [hex, if_false]
              exact (ν.character.eq_zero_iff' ⊥).mpr (Or.inl rfl)
          · have hsup : I ⊔ A.cS ≠ ⊤ := fun h => hn ⟨hbot, h⟩
            have hex : ∃ v ∈ D, I ≤ v.asIdeal := by
              have hA : ¬ ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
                  v ∈ A.Sf → I ⊔ v.asIdeal = ⊤ := by
                intro hall
                exact hsup ((SArithmeticData.exterior_iff A ⟨I, hbot⟩).mpr hall)
              push Not at hA
              obtain ⟨v, hvS, hvv⟩ := hA
              have heqv : v.asIdeal = I ⊔ v.asIdeal :=
                v.isMaximal.eq_of_le hvv le_sup_right
              exact ⟨v, hSD (by simpa using hvS), le_sup_left.trans heqv.symm.le⟩
            simp only [Detector.deletedPrimitiveIdealCoefficient]
            simp [hex]
        rw [hc0, zero_mul]
      have hsupp : Function.support (fun I : Ideal (𝓞 F) =>
          Detector.deletedPrimitiveIdealCoefficient F ν D I *
            (Ideal.absNorm I : ℂ) ^ (-s)) ⊆
          {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I ⊔ A.cS = ⊤} := by
        intro I hI
        by_contra hn
        exact hI (hzero I hn)
      rw [InitialSeparatedEuler.dirichletSeries]
      rw [← tsum_subtype_eq_of_support_subset hsupp]
      apply tsum_congr
      intro I
      simp only [ExteriorIdealEuler.summand]
      rw [hc I]
    rw [hseries s hs, hdir, (hBs s hs).tsum_eq]
  have hEqOn : Set.EqOn l g T :=
    hl'.eqOn_of_preconnected_of_eventuallyEq hg (convex_halfSpace_re_gt 0).isPreconnected
      (z₀ := (2 : ℂ)) (by norm_num [T])
      (by
        filter_upwards [IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
          (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by norm_num)] with s hs
        exact heq s hs)
  intro w hw
  have h := hEqOn (by simpa [T] using hw)
  simpa [g] using h

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain UniqueFactorizationMonoid

private theorem finite_principal_quotient
    (F : Type) [Field F] [NumberField F]
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (u : S.integer F) (hu : u ≠ 0) :
    Finite ((S.integer F) ⧸ Ideal.span ({u} : Set (S.integer F))) := by
  obtain ⟨Sf, hSf⟩ := hS.exists_finset_coe
  subst hSf
  exact (sProductModulus_eq_principalIdeal_index F Sf u hu).1

theorem integral_kummer_conductor_cost
    (F : Type) [Field F] [NumberField F]
    (ζ12 : F) (hζ12 : IsPrimitiveRoot ζ12 12) (σ : F →+* ℂ)
    (S : Set (HeightOneSpectrum (𝓞 F))) (hS : S.Finite)
    (hSix : ∀ v : HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 → v ∈ S)
    [IsPrincipalIdealRing (S.integer F)] :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : S.integer F) (hu : u ≠ 0)
      (χ : Detector.PrimitiveFrequencyCharacter F),
      Detector.IsKummerFrequencyCharacter F ζ12 σ S
        (Units.mk0 (u : F) (by exact_mod_cast hu)) χ →
      (Ideal.absNorm χ.conductor : ℝ) ≤
        C * (Detector.frequencyNorm F S u : ℝ) := by
  classical
  obtain ⟨b, hb6, hb⟩ :=
    Detector.Conductor.LocalExponent.sextic_conductor_exponent_bounds F
  obtain ⟨C, hC, hnorm⟩ :=
    Detector.Conductor.NormFactorization.norm_le_exterior_prime_product F S hS b
  refine ⟨C, hC, ?_⟩
  intro u hu χ hχ
  have horder := Detector.Conductor.global_kummer_sixth_power F ζ12 hζ12 σ S hS
    (Units.mk0 (u : F) (by exact_mod_cast hu)) χ hχ
  have hExp : ∀ v : HeightOneSpectrum (𝓞 F),
      (normalizedFactors χ.conductor).count v.asIdeal ≤ b v := hb χ horder
  have hFinite : {v : HeightOneSpectrum (𝓞 F) | χ.conductor ≤ v.asIdeal}.Finite := by
    simpa only [Ideal.dvd_iff_le] using (Ideal.finite_factors χ.conductor_ne_zero)
  let T := hFinite.toFinset.filter (fun v => v ∉ S)
  have hTmem : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ T ↔ χ.conductor ≤ v.asIdeal ∧ v ∉ S := by
    intro v
    simp only [T, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hTval : ∀ v ∈ T, v.valuation F (u : F) < 1 := by
    intro v hv
    obtain ⟨hIle, hvS⟩ := (hTmem v).mp hv
    refine lt_of_le_of_ne (u.property v hvS) ?_
    intro heq
    have hcop := (hχ v hvS (by simpa using heq)).1
    have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by
      rw [← hcop]; exact sup_le le_rfl hIle
    exact v.isPrime.ne_top (top_unique htop)
  have h1 : (Ideal.absNorm χ.conductor : ℝ) ≤
      C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := by
    refine hnorm χ.conductor χ.conductor_ne_zero T ?_ ?_ ?_
    · intro v _
      exact hExp v
    · intro v hvS
      have hcop : (Ideal.absNorm v.asIdeal).Coprime 6 := by
        by_contra h
        exact hvS (hSix v h)
      simpa [hb6 v hcop] using hExp v
    · intro v hvS hle
      exact (hTmem v).mpr ⟨hle, hvS⟩
  have h2 : (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) ≤
      (Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) : ℝ) :=
    Detector.Conductor.RadicalQuotient.exterior_prime_product_le_radical_index
      F S hS u hu T (fun v hv => ⟨((hTmem v).mp hv).2, hTval v hv⟩)
  haveI : Finite ((S.integer F) ⧸ Ideal.span {u}) := finite_principal_quotient F S hS u hu
  have h3nat : Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) ≤
      Nat.card ((S.integer F) ⧸ Ideal.span {u}) :=
    Nat.card_le_card_of_surjective _
      (Ideal.Quotient.factor_surjective (Ideal.le_radical (I := Ideal.span {u})))
  have h3 : (Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) : ℝ) ≤
      (Detector.frequencyNorm F S u : ℝ) := by
    have hfn : (Detector.frequencyNorm F S u : ℝ) =
        (Nat.card ((S.integer F) ⧸ Ideal.span ({u} : Set (S.integer F))) : ℝ) := rfl
    rw [hfn]
    exact_mod_cast h3nat
  calc (Ideal.absNorm χ.conductor : ℝ)
      ≤ C * (∏ v ∈ T, (Ideal.absNorm v.asIdeal : ℝ)) := h1
    _ ≤ C * (Nat.card ((S.integer F) ⧸ (Ideal.span {u}).radical) : ℝ) :=
        mul_le_mul_of_nonneg_left h2 hC.le
    _ ≤ C * (Detector.frequencyNorm F S u : ℝ) := mul_le_mul_of_nonneg_left h3 hC.le

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic
noncomputable section
open scoped Classical NumberField
open IsDedekindDomain LocalFiniteSums
variable {F : Type} [Field F] [NumberField F]

 def rawValuationIdeal (A : SArithmeticData F) (v : HeightOneSpectrum (𝓞 F))
    (hv : v ∉ A.Sf) : Ideal A.R where
  carrier := {r | v.valuation F (r : F) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change v.valuation F ((x : F) + (y : F)) < 1
    exact (ValuationClass.map_add_le_max _ _ _).trans_lt (max_lt hx hy)
  smul_mem' := by
    intro x y hy
    change v.valuation F ((x : F) * (y : F)) < 1
    rw [map_mul]
    exact (mul_le_mul_of_nonneg_right (x.property v hv) zero_le).trans_lt (by simpa using hy)

theorem raw_plus_inducer_isKummer
    (A : SArithmeticData F) (σ : F →+* ℂ)
    (U : AllRowEuler.InitialSeparation.RawFrequency A)
    (χ : Detector.PrimitiveFrequencyCharacter F)
    (hχ : ∀ I : A.Exterior,
      AllRowEuler.InitialSeparation.plusExteriorCoefficient σ U I =
        Detector.deletedPrimitiveIdealCoefficient F χ
          (RawHeckeRows.rawDeletionSet U) I.val) :
    Detector.IsKummerFrequencyCharacter F A.zeta12 σ
      (A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) χ := by
  classical
  intro v hv huval
  simp only [Units.val_mk0] at huval

  have hexterior : v.asIdeal ⊔ A.cS = ⊤ := by
    by_contra hn
    have he : v.asIdeal = v.asIdeal ⊔ A.cS := v.isMaximal.eq_of_le hn le_sup_left
    have hc : A.cS ≤ v.asIdeal := le_sup_right.trans_eq he.symm
    obtain ⟨w, hw, hwv⟩ := v.isPrime.prod_le.mp hc
    exact hv ((HeightOneSpectrum.ext (w.isMaximal.eq_of_le v.isPrime.ne_top hwv)) ▸ hw)
  let p : ExteriorPrime A := ⟨v, hexterior⟩
  have hIval : (primeIdeal p).val = v.asIdeal := rfl

  have hmap_extend_le : A.extendIdeal (primeIdeal p) ≤ rawValuationIdeal A v hv := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change v.valuation F (((algebraMap (𝓞 F) A.R) a : A.R) : F) < 1
    have hcoe : (((algebraMap (𝓞 F) A.R) a : A.R) : F) = algebraMap (𝓞 F) F a := rfl
    rw [hcoe]
    exact (v.valuation_lt_one_iff_mem (K := F) a).mpr (hIval ▸ ha)

  have hexp : idealPrimeExponent v.asIdeal U.ideal.val = 0 := by
    have h1 := ArithmeticContext.actual_generator_valuation A U.ideal U.u U.generates
      (Units.mk0 (U.u : F) (by exact_mod_cast U.generates.1)) rfl v hv
    simp only [Units.val_mk0] at h1
    have h2 : WithZero.exp (-(idealPrimeExponent v.asIdeal U.ideal.val : ℤ)) = 1 := by
      rw [← h1]; exact huval
    have hle : -(idealPrimeExponent v.asIdeal U.ideal.val : ℤ) ≤ 0 :=
      WithZero.exp_le_one_iff.mp h2.le
    have hge : 0 ≤ -(idealPrimeExponent v.asIdeal U.ideal.val : ℤ) :=
      WithZero.one_le_exp_iff.mp h2.ge
    have hez : (idealPrimeExponent v.asIdeal U.ideal.val : ℤ) = 0 := by omega
    exact_mod_cast hez
  have hnot : ¬ U.ideal.val ≤ v.asIdeal := by
    intro hle
    have hm := (Ideal.mem_normalizedFactors_iff U.ideal.property.1).mpr
      ⟨v.isPrime, hle⟩
    exact (Multiset.count_eq_zero.mp hexp) hm

  have hvD : v ∉ RawHeckeRows.rawDeletionSet U := by
    simp only [RawHeckeRows.rawDeletionSet, Set.mem_union, Set.mem_setOf_eq]
    exact fun h => h.elim hv hnot
  have hdel : Detector.deletedPrimitiveIdealCoefficient F χ
      (RawHeckeRows.rawDeletionSet U) v.asIdeal = χ.character v.asIdeal := by
    unfold Detector.deletedPrimitiveIdealCoefficient
    rw [if_neg]
    rintro ⟨w, hw, hle⟩
    have hwv : w = v := (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle)).symm
    rw [hwv] at hw
    exact hvD hw

  have hchi : χ.character v.asIdeal = σ (A.sexticResidue (primeIdeal p) U.u) := by
    rw [← hdel, ← hIval, ← hχ (primeIdeal p)]
    exact AllRowEuler.UnitCovariance.residueCoefficient_eq (primeIdeal p) U.u

  have hunit : IsUnit (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) := by
    have hmax : (A.extendIdeal (primeIdeal p)).IsMaximal := by
      apply Ideal.Quotient.maximal_of_isField
      exact (A.exteriorLocalResidueEquiv (primeIdeal p) v rfl).toMulEquiv.isField
        (Field.toIsField (SArithmeticData.exteriorLocalResidue v))
    haveI := hmax
    rw [isUnit_iff_ne_zero]
    intro hz
    have hmem : U.u ∈ A.extendIdeal (primeIdeal p) := Ideal.Quotient.eq_zero_iff_mem.mp hz
    have hlt : v.valuation F (U.u : F) < 1 := hmap_extend_le hmem
    rw [huval] at hlt
    exact lt_irrefl 1 hlt
  let q : (A.R ⧸ A.extendIdeal (primeIdeal p))ˣ := hunit.unit
  have hqval : (q : A.R ⧸ A.extendIdeal (primeIdeal p)) =
      Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u := hunit.unit_spec
  obtain ⟨j, hj, hjchar, hjred⟩ :=
    A.sexticResidueFamily_normalized.2.1 (primeIdeal p) v hIval q

  have hchar : χ.character v.asIdeal = σ ((A.zeta12 ^ 2) ^ j) := by
    rw [hchi]
    have h1 : A.sexticResidue (primeIdeal p) U.u =
        ((A.sexticResidueFamily (primeIdeal p)) q : F) := by
      unfold SArithmeticData.sexticResidue SArithmeticData.residueValue
      rw [← hqval, MulChar.ofUnitHom_coe]
    rw [h1, hjchar, pow_mul]
  refine ⟨?_, ⟨⟨j, hj⟩, ?_, hchar⟩⟩
  ·
    by_contra hcop
    have hz : χ.character v.asIdeal = 0 := (χ.character.eq_zero_iff' v.asIdeal).mpr (Or.inr hcop)
    rw [hchar] at hz
    have h0 : (A.zeta12 ^ 2) ^ j = 0 := σ.injective (by rw [hz, map_zero])
    exact pow_ne_zero j (pow_ne_zero 2 (A.primitive_zeta12.ne_zero (by decide))) h0
  ·
    have hcard : Nat.card (A.R ⧸ A.extendIdeal (primeIdeal p)) = Ideal.absNorm v.asIdeal := by
      rw [A.exteriorResidue_card (primeIdeal p), hIval]
    rw [hcard] at hjred
    have hmk : Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
        (U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) =
        Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
          (algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j))) := by
      calc Ideal.Quotient.mk (A.extendIdeal (primeIdeal p))
            (U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6))
          = (Ideal.Quotient.mk (A.extendIdeal (primeIdeal p)) U.u) ^
              ((Ideal.absNorm v.asIdeal - 1) / 6) := by rw [map_pow]
        _ = (q : A.R ⧸ A.extendIdeal (primeIdeal p)) ^
              ((Ideal.absNorm v.asIdeal - 1) / 6) := by rw [← hqval]
        _ = _ := hjred.symm
    have hmem : U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
        algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) ∈
        A.extendIdeal (primeIdeal p) := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_sub, hmk, sub_self]
    have hval2 : v.valuation F
        ((U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
          algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) : A.R) : F) < 1 :=
      hmap_extend_le hmem
    have hcoe2 : ((U.u ^ ((Ideal.absNorm v.asIdeal - 1) / 6) -
          algebraMap (𝓞 F) A.R (A.primitive_zeta12.toInteger ^ (2 * j)) : A.R) : F) =
        (U.u : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - (A.zeta12 ^ 2) ^ j := by
      simp only [Subalgebra.coe_sub, Subalgebra.coe_pow]
      congr 1
      push_cast
      rw [show (algebraMap (𝓞 F) F A.primitive_zeta12.toInteger) = A.zeta12 from
        A.primitive_zeta12.coe_toInteger, pow_mul]
    rw [hcoe2] at hval2
    exact hval2

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate.RawInducerArithmetic

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate
noncomputable section
open scoped Classical NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem raw_plus_inducer_conductor_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (P : Frequency R → Detector.PrimitiveFrequencyCharacter F)
    (hP : ∀ (u : Frequency R) (I : R.A.Exterior),
      AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u) I =
        Detector.deletedPrimitiveIdealCoefficient F (P u)
          (RawHeckeRows.rawDeletionSet (U u)) I.val) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Frequency R,
      1 + (Ideal.absNorm (P u).conductor : ℝ) ≤ C * frequencyNorm R u := by
  letI : IsPrincipalIdealRing R.A.R :=
    R.A.principalIdealRing_of_classGroup_subsingleton R.classKilled
  have hSix : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      ¬ (Ideal.absNorm v.asIdeal).Coprime 6 →
        v ∈ (R.A.Sf : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra hn
    exact hv (ArithmeticContext.actual_outside_norm_coprime_six R.A v hn)
  obtain ⟨C, hC, hcost⟩ := RawInducerArithmetic.integral_kummer_conductor_cost F
    R.A.zeta12 R.A.primitive_zeta12 R.σ _ R.A.Sf.finite_toSet hSix
  refine ⟨1 + C, by positivity, ?_⟩
  intro u
  have hK := RawInducerArithmetic.raw_plus_inducer_isKummer R.A R.σ (U u) (P u) (hP u)
  have hbound := hcost (U u).u (U u).generates.1 (P u) hK
  have hnorm := RawInducerArithmetic.actual_frequency_norm_dictionary R u
  rw [hU u, ← hnorm.1] at hbound
  calc
    1 + (Ideal.absNorm (P u).conductor : ℝ) ≤
        frequencyNorm R u + C * frequencyNorm R u := add_le_add hnorm.2 hbound
    _ = (1 + C) * frequencyNorm R u := by ring

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound.ConductorEstimate

end

section

namespace DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound
noncomputable section
open scoped Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem continued_plus_strip_bound
    (R : PrincipalMellin.ActualRecipe S η)
    (U : Frequency R → AllRowEuler.InitialSeparation.RawFrequency R.A)
    (plus : Frequency R → ℂ → ℂ)
    (hU : ∀ u : Frequency R, (U u).u = u.val.val)
    (hplus : ∀ u : Frequency R, u ≠ principalFrequency R →
      DifferentiableOn ℂ (plus u) {s : ℂ | 0 < s.re})
    (hplusSeries : ∀ (u : Frequency R) (s : ℂ), 1 < s.re →
      plus u s = AllRowEuler.InitialSeparation.plusL R.σ (U u) s)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ, 0 < B ∧ ∀ u : Frequency R, u ≠ principalFrequency R →
        1 ≤ frequencyNorm R u → ∀ w : ℂ,
        w ∈ comparisonClosedStrip a b →
        ‖plus u w‖ ≤ B * (frequencyNorm R u) ^ (1 / 2 + ε) *
          (2 + |w.im|) ^ d := by
  classical
  obtain ⟨C, U₀, hC, hU₀⟩ := RawHeckeRows.actual_context_and_raw_frequencies R
  obtain ⟨P, M, hfinite, hP, hM⟩ :=
    RawHeckeRows.actual_raw_masked_inducers R C hC U hU
  obtain ⟨Ccond, hCcond, hcond⟩ :=
    ConductorEstimate.raw_plus_inducer_conductor_bound R U hU P hP
  have hF : NumberField.IsTotallyComplex F :=
    primitive12_totallyComplex F R.A.zeta12 R.A.primitive_zeta12
  obtain ⟨d, hd, hHeckeBound⟩ :=
    ConductorEstimate.nonprincipal_hecke_positive_strip_bound F hF a b ha hab
  refine ⟨d, hd, ?_⟩
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  obtain ⟨BH, hBH, hH⟩ := hHeckeBound (ε / 2) hεhalf
  obtain ⟨BM, hBM, hMask⟩ :=
    ConductorEstimate.raw_deletion_mask_subpower R U hU a (ε / 2) ha hεhalf
  let p : ℝ := 1 / 2 + ε / 2
  have hp : 0 ≤ p := by dsimp [p]; linarith
  refine ⟨BH * Ccond ^ p * BM, by positivity, ?_⟩
  intro u hu hNu w hw
  have hwlo : a ≤ w.re := hw.1
  have hwhi : w.re ≤ b := hw.2
  have hwpos : 0 < w.re := ha.trans_le hwlo
  have hnp : ¬ (P u).character.IsPrincipal :=
    (RawHeckeRows.actual_raw_inducers_nonprincipal
      R u (U u) (hU u) hu (P u) (M u) (hP u) (hM u)).1
  let H := nonprincipalRayHeckeData F hF (P u).conductor
    (P u).conductor_ne_zero (P u).character (P u).primitive hnp
  have heq : plus u w = H.L w * Detector.finiteEulerDeletionMask F
      (RawHeckeRows.rawDeletionSet (U u))
      (fun v => (P u).character v.asIdeal) w :=
    ConductorEstimate.deleted_exterior_continuation_eq R.A (P u) H
      (RawHeckeRows.rawDeletionSet (U u)) (hfinite u) Set.subset_union_left
      (AllRowEuler.InitialSeparation.plusExteriorCoefficient R.σ (U u)) (hP u)
      (plus u) (hplus u hu) (hplusSeries u) w hwpos
  have hL : ‖H.L w‖ ≤ BH * (1 + (Ideal.absNorm (P u).conductor : ℝ)) ^ p *
      (2 + |w.im|) ^ d := hH (P u).conductor (P u).conductor_ne_zero
        (P u).character (P u).primitive hnp w hwlo hwhi
  have hmask : ‖Detector.finiteEulerDeletionMask F
      (RawHeckeRows.rawDeletionSet (U u))
      (fun v => (P u).character v.asIdeal) w‖ ≤ BM * (frequencyNorm R u) ^ (ε / 2) :=
    hMask u (fun v => (P u).character v.asIdeal) w
      (fun v _ => RayUnitary.ray_character_norm_le_one F (P u).conductor
        (P u).conductor_ne_zero (P u).character v.asIdeal) hwlo
  have hNpos : 0 < frequencyNorm R u := zero_lt_one.trans_le hNu
  have hcpow : (1 + (Ideal.absNorm (P u).conductor : ℝ)) ^ p ≤
      Ccond ^ p * (frequencyNorm R u) ^ p := by
    calc
      _ ≤ (Ccond * frequencyNorm R u) ^ p :=
        Real.rpow_le_rpow (by positivity) (hcond u) hp
      _ = _ := Real.mul_rpow hCcond.le hNpos.le
  calc
    ‖plus u w‖ = ‖H.L w‖ * ‖Detector.finiteEulerDeletionMask F
        (RawHeckeRows.rawDeletionSet (U u))
        (fun v => (P u).character v.asIdeal) w‖ := by rw [heq, norm_mul]
    _ ≤ (BH * (1 + (Ideal.absNorm (P u).conductor : ℝ)) ^ p *
        (2 + |w.im|) ^ d) * (BM * (frequencyNorm R u) ^ (ε / 2)) :=
      mul_le_mul hL hmask (norm_nonneg _) (by positivity)
    _ ≤ (BH * (Ccond ^ p * (frequencyNorm R u) ^ p) *
        (2 + |w.im|) ^ d) * (BM * (frequencyNorm R u) ^ (ε / 2)) := by
      gcongr
    _ = (BH * Ccond ^ p * BM) * (frequencyNorm R u) ^ (1 / 2 + ε) *
        (2 + |w.im|) ^ d := by
      have hpow : (frequencyNorm R u) ^ p * (frequencyNorm R u) ^ (ε / 2) =
          (frequencyNorm R u) ^ (1 / 2 + ε) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        dsimp [p]
        ring
      calc
        _ = (BH * Ccond ^ p * BM) *
            ((frequencyNorm R u) ^ p * (frequencyNorm R u) ^ (ε / 2)) *
            (2 + |w.im|) ^ d := by ring
        _ = _ := by rw [hpow]

end
end DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.RightBound

end
