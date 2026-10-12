module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactCoefficients.Unitarization
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactInductionProjectivity
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.AdmissibleSchurLemma

@[expose] public section

section
namespace DedekindZetaZeroFree.CuspidalProjectiveRetractProof
open scoped Topology
variable {G S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup S] [Module ℂ S]

 theorem smoothFunctional (ρ : Representation ℂ G S) (ℓ : Module.Dual ℂ S)
    (U : CompactOpenLevel G) (hU : CuspidalFiniteCosetForm.FixesFunctional ρ U ℓ) :
    SmoothVector ρ.dual ℓ := by
  refine ⟨U.toOpenSubgroup, ?_⟩
  intro u hu
  ext s
  change ℓ (ρ u⁻¹ s) = ℓ s
  exact hU u⁻¹ (U.toOpenSubgroup.inv_mem hu) s

variable (ρ : Representation ℂ G S) [ρ.IsIrreducible]
  (hρ : SmoothRepresentation ρ) (ℓ : Module.Dual ℂ S) (hℓ : ℓ ≠ 0)
  (U : CompactOpenLevel G) (hU : CuspidalFiniteCosetForm.FixesFunctional ρ U ℓ)
  (hc : ∀ L : Module.Dual ℂ S, SmoothVector ρ.dual L →
    ∀ s : S, HasCompactSupport (CuspidalFiniteCosetForm.coefficient ρ L s))

include hρ hℓ hU hc

 theorem form_add (s t w : S) :
    CuspidalFiniteCosetForm.form ρ ℓ U (s + t) w =
      CuspidalFiniteCosetForm.form ρ ℓ U s w + CuspidalFiniteCosetForm.form ρ ℓ U t w :=
  (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.1 s t w

 theorem form_smul (a : ℂ) (s w : S) :
    CuspidalFiniteCosetForm.form ρ ℓ U (a • s) w = a * CuspidalFiniteCosetForm.form ρ ℓ U s w :=
  (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.1 a s w

 theorem form_hermitian (s w : S) :
    CuspidalFiniteCosetForm.form ρ ℓ U s w = star (CuspidalFiniteCosetForm.form ρ ℓ U w s) :=
  (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.2.2.2.1 s w

 theorem form_real (s : S) : (CuspidalFiniteCosetForm.form ρ ℓ U s s).im = 0 :=
  ((CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.2.2.2.2.1 s).1

 theorem form_pos (s : S) (hs : s ≠ 0) : 0 < (CuspidalFiniteCosetForm.form ρ ℓ U s s).re :=
  (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.2.2.2.2.2.1 s hs

 theorem form_invariant (g : G) (s w : S) :
    CuspidalFiniteCosetForm.form ρ ℓ U (ρ g s) (ρ g w) = CuspidalFiniteCosetForm.form ρ ℓ U s w :=
  (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
    (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.2.2.2.2.2.2.1 g s w

 theorem form_coefficient_compact (s w : S) :
    HasCompactSupport (fun g => CuspidalFiniteCosetForm.form ρ ℓ U (ρ g s) w) := by
  obtain ⟨L, hL, hs⟩ :=
    (CuspidalFiniteCosetForm.unitarization_noT2 ρ hρ ℓ hℓ U hU
      (hc ℓ (smoothFunctional ρ ℓ U hU))).2.2.2.2.2.2.2.2.2 w
  have he : CuspidalFiniteCosetForm.coefficient ρ L s =
      (fun g => CuspidalFiniteCosetForm.form ρ ℓ U (ρ g s) w) := by
    funext g
    exact hL (ρ g s)
  rw [← he]
  exact hc L hs s

 theorem section_smooth (W : CompactOpenLevel G) (s w : S)
    (F : EqSections (CompactInductionProjectivity.inducingSubgroup W)
      (Representation.trivial ℂ (CompactInductionProjectivity.inducingSubgroup W) ℂ) 1)
    (hF : ∀ g, F.val g = CuspidalFiniteCosetForm.form ρ ℓ U (ρ g s) w) :
    F ∈ SmoothInd (CompactInductionProjectivity.inducingSubgroup W)
      (Representation.trivial ℂ (CompactInductionProjectivity.inducingSubgroup W) ℂ) 1 := by
  apply (mem_smoothSubmodule _ _).mpr
  obtain ⟨J, hJ⟩ := hρ s
  refine ⟨J, ?_⟩
  intro j hj
  apply Subtype.ext
  funext g
  change F.val (g * j) = F.val g
  simp only [hF, map_mul, Module.End.mul_apply, hJ j hj]

 theorem section_compact (s w : S) (W : CompactOpenLevel G) :
    HasCompactSupportModH (CompactInductionProjectivity.inducingSubgroup W)
      (fun g => CuspidalFiniteCosetForm.form ρ ℓ U (ρ g s) w) := by
  let H := CompactInductionProjectivity.inducingSubgroup W
  letI : DiscreteTopology (SectionCosetSpace H) := by
    apply discreteTopology_iff_isOpen_singleton.mpr
    intro c
    rw [isOpen_coinduced]
    have heq : (Quotient.mk (QuotientGroup.rightRel H)) ⁻¹' {c} =
        (fun g : G => c.out * g⁻¹) ⁻¹' (H : Set G) := by
      ext g
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      conv_lhs => rw [← Quotient.out_eq c]
      rw [Quotient.eq, QuotientGroup.rightRel_apply]
      rfl
    change IsOpen ((Quotient.mk (QuotientGroup.rightRel H)) ⁻¹' {c})
    rw [heq]
    exact W.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_inv)
  have hcpt := form_coefficient_compact ρ hρ ℓ hℓ U hU hc s w
  have him := hcpt.isCompact.image
    (continuous_quotient_mk' : Continuous (Quotient.mk (QuotientGroup.rightRel H)))
  apply him.of_isClosed_subset isClosed_closure
  apply closure_minimal _ him.isClosed
  exact Set.image_mono subset_closure

end DedekindZetaZeroFree.CuspidalProjectiveRetractProof

end

section

namespace DedekindZetaZeroFree.CuspidalProjectiveRetract

open scoped Topology

variable {G S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [AddCommGroup S] [Module ℂ S]

def CompactSmoothCoefficients (ρ : Representation ℂ G S) : Prop :=
  ∀ L : Module.Dual ℂ S, SmoothVector ρ.dual L →
    ∀ s : S, HasCompactSupport (CuspidalFiniteCosetForm.coefficient ρ L s)

noncomputable def beta (ρ : Representation ℂ G S) (ℓ : Module.Dual ℂ S)
    (U : CompactOpenLevel G) (s t : S) : ℂ :=
  CuspidalFiniteCosetForm.form ρ ℓ U s t

section ExplicitMaps

variable (ρ : Representation ℂ G S) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (ℓ : Module.Dual ℂ S) (hℓ : ℓ ≠ 0)
    (U : CompactOpenLevel G) (hU : CuspidalFiniteCosetForm.FixesFunctional ρ U ℓ)
    (hc : CompactSmoothCoefficients ρ) (W : CompactOpenLevel G)
    (v₀ : fixedSubmodule ρ (CompactInductionProjectivity.inducingSubgroup W))

noncomputable def coefficientEmbedding
    (ρ : Representation ℂ G S) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (ℓ : Module.Dual ℂ S) (hℓ : ℓ ≠ 0)
    (U : CompactOpenLevel G) (hU : CuspidalFiniteCosetForm.FixesFunctional ρ U ℓ)
    (hc : CompactSmoothCoefficients ρ) (W : CompactOpenLevel G)
    (v₀ : fixedSubmodule ρ (CompactInductionProjectivity.inducingSubgroup W)) :
    Representation.IntertwiningMap ρ (CompactInductionProjectivity.representation W) where
  toLinearMap :=
    { toFun := fun s => ⟨⟨⟨fun g => beta ρ ℓ U (ρ g s) v₀.val,
          by
            intro u g
            change beta ρ ℓ U (ρ ((u : G) * g) s) v₀.val =
              (1 : ℂ) • beta ρ ℓ U (ρ g s) v₀.val
            rw [one_smul, map_mul, Module.End.mul_apply]
            have hv := v₀.property u
            change ρ (u : G) v₀.val = v₀.val at hv
            simpa only [hv, beta] using
              CuspidalProjectiveRetractProof.form_invariant ρ hρ ℓ hℓ U hU hc (u : G) (ρ g s) v₀.val⟩,
          by
            exact CuspidalProjectiveRetractProof.section_smooth ρ hρ ℓ hℓ U hU hc W s v₀.val _
              (fun g => rfl)⟩,
        by exact CuspidalProjectiveRetractProof.section_compact ρ hρ ℓ hℓ U hU hc s v₀.val W⟩
      map_add' := by
        intro s t
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change beta ρ ℓ U (ρ g (s + t)) v₀.val = _
        rw [map_add]
        exact CuspidalProjectiveRetractProof.form_add ρ hρ ℓ hℓ U hU hc _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
        funext g
        change beta ρ ℓ U (ρ g (a • s)) v₀.val = _
        rw [map_smul]
        exact CuspidalProjectiveRetractProof.form_smul ρ hρ ℓ hℓ U hU hc _ _ _ }
  isIntertwining' := by
    intro h
    apply LinearMap.ext
    intro s
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
    funext g
    change beta ρ ℓ U (ρ g (ρ h s)) v₀.val = beta ρ ℓ U (ρ (g * h) s) v₀.val
    rw [map_mul, Module.End.mul_apply]

@[simp] theorem coefficientEmbedding_apply (s : S) (g : G) :
    CompactInductionProjectivity.sectionValue W
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ s) g =
    beta ρ ℓ U (ρ g s) v₀.val := rfl

noncomputable def unnormalizedRetraction :
    Representation.IntertwiningMap (CompactInductionProjectivity.representation W) ρ :=
  CompactInductionProjectivity.finiteSumMap W ρ v₀

theorem unnormalizedRetraction_apply (F : CompactInductionProjectivity.P W) :
    unnormalizedRetraction ρ W v₀ F =
      ∑ c ∈ (CompactInductionProjectivity.finiteSupportEquiv W F).support,
        (CompactInductionProjectivity.finiteSupportEquiv W F) c • ρ c.out⁻¹ v₀.val := by
  rfl

noncomputable def coefficientSquareSum : ℝ :=
  ∑ c ∈ (CompactInductionProjectivity.finiteSupportEquiv W
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ v₀.val)).support,
    ‖beta ρ ℓ U (ρ c.out v₀.val) v₀.val‖ ^ 2

theorem pairing_unnormalized_composite :
    beta ρ ℓ U
      (unnormalizedRetraction ρ W v₀
        (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ v₀.val)) v₀.val =
    (coefficientSquareSum ρ hρ ℓ hℓ U hU hc W v₀ : ℂ) := by
  classical
  obtain ⟨L, hL, hsL⟩ := (CuspidalFiniteCosetForm.unitarization ρ hρ ℓ hℓ U hU
    (hc ℓ (CuspidalProjectiveRetractProof.smoothFunctional ρ ℓ U hU))).2.2.2.2.2.2.2.2.2 v₀.val
  change CuspidalFiniteCosetForm.form ρ ℓ U _ v₀.val = _
  rw [← hL]
  rw [unnormalizedRetraction_apply, map_sum]
  unfold coefficientSquareSum
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro c hc'
  rw [map_smul, hL]
  change _ * beta ρ ℓ U (ρ c.out⁻¹ v₀.val) v₀.val = _
  have hinv : beta ρ ℓ U (ρ c.out⁻¹ v₀.val) v₀.val =
      star (beta ρ ℓ U (ρ c.out v₀.val) v₀.val) := by
    have hi := CuspidalProjectiveRetractProof.form_invariant ρ hρ ℓ hℓ U hU hc
      c.out (ρ c.out⁻¹ v₀.val) v₀.val
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at hi
    unfold beta
    rw [← hi]
    exact CuspidalProjectiveRetractProof.form_hermitian ρ hρ ℓ hℓ U hU hc _ _
  rw [hinv]
  change beta ρ ℓ U (ρ c.out v₀.val) v₀.val * star (beta ρ ℓ U (ρ c.out v₀.val) v₀.val) = _
  simpa only [Complex.normSq_eq_norm_sq, starRingEnd_apply] using
    Complex.mul_conj (beta ρ ℓ U (ρ c.out v₀.val) v₀.val)

theorem coefficientSquareSum_pos (hv₀ : v₀.val ≠ 0) :
    0 < coefficientSquareSum ρ hρ ℓ hℓ U hU hc W v₀ := by
  classical
  have hp := CuspidalProjectiveRetractProof.form_pos ρ hρ ℓ hℓ U hU hc v₀.val hv₀
  have hb : beta ρ ℓ U v₀.val v₀.val ≠ 0 := by
    intro hz
    change 0 < (beta ρ ℓ U v₀.val v₀.val).re at hp
    rw [hz, Complex.zero_re] at hp
    exact (lt_irrefl 0 hp)
  let c₁ : CompactInductionProjectivity.Cosets W := Quotient.mk _ (1 : G)
  have he : beta ρ ℓ U (ρ c₁.out v₀.val) v₀.val = beta ρ ℓ U v₀.val v₀.val := by
    have hh := CompactInductionProjectivity.finiteSupportEquiv_apply W
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ v₀.val) 1
    change beta ρ ℓ U (ρ c₁.out v₀.val) v₀.val =
      CompactInductionProjectivity.sectionValue W
        (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ v₀.val) 1 at hh
    simpa only [coefficientEmbedding_apply, map_one, Module.End.one_apply] using hh
  unfold coefficientSquareSum
  apply Finset.sum_pos'
  · intro c hc'; exact sq_nonneg _
  · refine ⟨c₁, ?_, ?_⟩
    · apply Finsupp.mem_support_iff.mpr
      change beta ρ ℓ U (ρ c₁.out v₀.val) v₀.val ≠ 0
      rwa [he]
    · rw [he]
      exact sq_pos_of_pos (norm_pos_iff.mpr hb)

theorem positive_scalar_composite
    [Nontrivial S]
    (hcompactOpen : ∀ N ∈ 𝓝 (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ N)
    (hadmissible : Admissible ρ) (hv₀ : v₀.val ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      (unnormalizedRetraction ρ W v₀).comp
        (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀) =
          (c : ℂ) • Representation.IntertwiningMap.id ρ ∧
      c = coefficientSquareSum ρ hρ ℓ hℓ U hU hc W v₀ /
        (beta ρ ℓ U v₀.val v₀.val).re := by
  obtain ⟨a, ha⟩ := admissible_irreducible_endomorphism_scalar hcompactOpen ρ hρ hadmissible
    ((unnormalizedRetraction ρ W v₀).comp (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀))
  have hav : unnormalizedRetraction ρ W v₀
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀ v₀.val) = a • v₀.val := by
    have hh := congrArg (fun T : S →ₗ[ℂ] S => T v₀.val) ha
    exact hh
  have hp := CuspidalProjectiveRetractProof.form_pos ρ hρ ℓ hℓ U hU hc v₀.val hv₀
  have hr := CuspidalProjectiveRetractProof.form_real ρ hρ ℓ hℓ U hU hc v₀.val
  change 0 < (beta ρ ℓ U v₀.val v₀.val).re at hp
  change (beta ρ ℓ U v₀.val v₀.val).im = 0 at hr
  have hb : beta ρ ℓ U v₀.val v₀.val = ((beta ρ ℓ U v₀.val v₀.val).re : ℂ) := by
    apply Complex.ext <;> simp [hr]
  have hpair := pairing_unnormalized_composite ρ hρ ℓ hℓ U hU hc W v₀
  rw [hav] at hpair
  change CuspidalFiniteCosetForm.form ρ ℓ U (a • v₀.val) v₀.val = _ at hpair
  rw [CuspidalProjectiveRetractProof.form_smul ρ hρ ℓ hℓ U hU hc] at hpair
  change a * beta ρ ℓ U v₀.val v₀.val = _ at hpair
  rw [hb] at hpair
  let c := coefficientSquareSum ρ hρ ℓ hℓ U hU hc W v₀ / (beta ρ ℓ U v₀.val v₀.val).re
  have hac : a = (c : ℂ) := by
    apply (mul_left_inj' (show ((beta ρ ℓ U v₀.val v₀.val).re : ℂ) ≠ 0 by
      exact_mod_cast ne_of_gt hp)).mp
    rw [hpair]
    dsimp [c]
    rw [Complex.ofReal_div]
    exact (div_mul_cancel₀ _ (show ((beta ρ ℓ U v₀.val v₀.val).re : ℂ) ≠ 0 by
      exact_mod_cast ne_of_gt hp)).symm
  refine ⟨c, div_pos (coefficientSquareSum_pos ρ hρ ℓ hℓ U hU hc W v₀ hv₀) hp, ?_, rfl⟩
  apply Representation.IntertwiningMap.ext
  rw [ha, hac]
  rfl

noncomputable def normalizedRetraction (c : ℝ) :
    Representation.IntertwiningMap (CompactInductionProjectivity.representation W) ρ :=
  ((c : ℂ)⁻¹) • unnormalizedRetraction ρ W v₀

theorem normalizedRetraction_comp (c : ℝ) (hcpos : 0 < c)
    (hscalar : (unnormalizedRetraction ρ W v₀).comp
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀) =
        (c : ℂ) • Representation.IntertwiningMap.id ρ) :
    (normalizedRetraction ρ W v₀ c).comp
      (coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀) =
        Representation.IntertwiningMap.id ρ := by
  rw [normalizedRetraction, Representation.IntertwiningMap.smul_comp, hscalar, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast ne_of_gt hcpos), one_smul]

end ExplicitMaps

theorem exists_explicit_retract [Nontrivial S]
    (hcompactOpen : ∀ N ∈ 𝓝 (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ N)
    (ρ : Representation ℂ G S) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (hadmissible : Admissible ρ)
    (hc : CompactSmoothCoefficients ρ) :
    ∃ (ℓ : Module.Dual ℂ S) (U W : CompactOpenLevel G),
      ℓ ≠ 0 ∧ CuspidalFiniteCosetForm.FixesFunctional ρ U ℓ ∧
      ∃ v₀ : fixedSubmodule ρ (CompactInductionProjectivity.inducingSubgroup W),
        v₀.val ≠ 0 ∧ ∃ c : ℝ, 0 < c ∧
        ∃ j : Representation.IntertwiningMap ρ (CompactInductionProjectivity.representation W),
        ∃ r₀ r : Representation.IntertwiningMap (CompactInductionProjectivity.representation W) ρ,
          (∀ (s : S) (g : G), CompactInductionProjectivity.sectionValue W (j s) g =
            beta ρ ℓ U (ρ g s) v₀.val) ∧
          r₀ = unnormalizedRetraction ρ W v₀ ∧
          r₀.comp j = (c : ℂ) • Representation.IntertwiningMap.id ρ ∧
          r = ((c : ℂ)⁻¹) • r₀ ∧ r.comp j = Representation.IntertwiningMap.id ρ := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : S)
  obtain ⟨ℓ, hℓsmooth, hℓv⟩ :=
    exists_smooth_dual_separating hcompactOpen ρ hρ hadmissible v hv
  have hℓ : ℓ ≠ 0 := by
    intro h
    exact hℓv (by rw [h]; rfl)
  have hBasis : ∀ J : OpenSubgroup G, ∃ U : CompactOpenLevel G,
      U.toOpenSubgroup ≤ J := by
    intro J
    obtain ⟨U, hU⟩ := hcompactOpen (J : Set G) (J.isOpen.mem_nhds J.one_mem)
    exact ⟨U, hU⟩
  obtain ⟨U, hU⟩ := CuspidalFiniteCosetForm.exists_fixing_level hBasis ρ ℓ hℓsmooth
  obtain ⟨W, hW⟩ := (smoothVector_iff_compactOpen_fixed hcompactOpen ρ v).mp (hρ v)
  let v₀ : fixedSubmodule ρ (CompactInductionProjectivity.inducingSubgroup W) := ⟨v, hW⟩
  obtain ⟨c, hcpos, hscalar, hnorm⟩ :=
    positive_scalar_composite ρ hρ ℓ hℓ U hU hc W v₀ hcompactOpen hadmissible hv
  refine ⟨ℓ, U, W, hℓ, hU, v₀, hv, c, hcpos,
    coefficientEmbedding ρ hρ ℓ hℓ U hU hc W v₀,
    unnormalizedRetraction ρ W v₀, normalizedRetraction ρ W v₀ c,
    ?_, rfl, hscalar, rfl, ?_⟩
  · intro s g
    rfl
  · exact normalizedRetraction_comp ρ hρ ℓ hℓ U hU hc W v₀ c hcpos hscalar

theorem lift_equivariant_surjection [Nontrivial S]
    (hcompactOpen : ∀ N ∈ 𝓝 (1 : G),
      ∃ J : CompactOpenLevel G, (J.toOpenSubgroup : Set G) ⊆ N)
    (ρ : Representation ℂ G S) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ) (hadmissible : Admissible ρ)
    (hc : CompactSmoothCoefficients ρ)
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (σ : Representation ℂ G X) (τ : Representation ℂ G Y)
    (hσ : SmoothRepresentation σ) (hτ : SmoothRepresentation τ)
    (q : Representation.IntertwiningMap σ τ) (hq : Function.Surjective q)
    (f : Representation.IntertwiningMap ρ τ) :
    ∃ f' : Representation.IntertwiningMap ρ σ, q.comp f' = f := by
  obtain ⟨ℓ, U, W, hℓ, hU, v₀, hv₀, c, hcpos, j, r₀, r, hform, hr₀, hscalar, hr, hrj⟩ :=
    exists_explicit_retract hcompactOpen ρ hρ hadmissible hc
  obtain ⟨T', hT'⟩ := CompactInductionProjectivity.lift_equivariant_surjection W hcompactOpen
    σ τ hσ hτ q hq (f.comp r)
  refine ⟨T'.comp j, ?_⟩
  calc q.comp (T'.comp j) = (q.comp T').comp j := by ext v; rfl
    _ = (f.comp r).comp j := by rw [hT']
    _ = f.comp (r.comp j) := by ext v; rfl
    _ = f.comp (Representation.IntertwiningMap.id ρ) := by rw [hrj]
    _ = f := by ext v; rfl

end DedekindZetaZeroFree.CuspidalProjectiveRetract

end
