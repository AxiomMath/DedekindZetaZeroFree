module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.OrbitMapInjectivity

@[expose] public section

noncomputable section

set_option maxHeartbeats 1200000

namespace DedekindZetaZeroFree.KPKirillovOrbitMapSurjective

open scoped NumberField Classical TensorProduct
open NumberField IsDedekindDomain
open KPKirillovGenuineSectionCharts KPKirillovProjectorGerms
open KPKirillovFiniteBallProjectors KPKirillovOrbitMapFaithful

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (𝓞 F))
  {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (KPLocalSmoothRepresentation.FiniteCover F ζ hζ w) V)
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (hρ : IsSmooth F ζ hζ w m ρ)
  (hgen : KPLocalSmoothRepresentation.genuine F ζ hζ w ρ)

def spectralPatch (u : ℤ) (t₀ : (K F w)ˣ) : Set (K F w)ˣ :=
  {t | (t : K F w) ∈ frequencyCoset F w u t₀}

private theorem values_eq_of_chart_eq
    (f g : Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ))
    (c : LocalChart F ζ hζ w m) (t : c.ball.domain)
    (p : P F ζ hζ w) (hp : slope F ζ hζ w p = t.val)
    (heq : chartValue F ζ hζ w m (ψ F w) c f t =
      chartValue F ζ hζ w m (ψ F w) c g t) :
    sectionValue F ζ hζ w m (ψ F w) f p =
      sectionValue F ζ hζ w m (ψ F w) g p := by
  have hH : p * (c.lift t)⁻¹ ∈ H F ζ hζ w := by
    change slope F ζ hζ w (p * (c.lift t)⁻¹) = 1
    rw [map_mul, map_inv, c.slope_lift, hp, mul_inv_cancel]
  obtain ⟨⟨b, e⟩, hbe, _⟩ := H_decomposition F ζ hζ w
    ⟨p * (c.lift t)⁻¹, hH⟩
  have hpe : p = (n F ζ hζ w b * z F ζ hζ w e) * c.lift t := by
    rw [← hbe]
    exact (inv_mul_cancel_right p (c.lift t)).symm
  rw [hpe, sections_covariance, sections_covariance]
  exact congrArg (fun v =>
    (((ψ F w (Multiplicative.ofAdd b) * iota F ζ hζ e : ℂˣ) : ℂ)) • v) heq

private theorem spectralPatch_open (u : ℤ) (t₀ : (K F w)ˣ) :
    IsOpen (spectralPatch F w u t₀) := by
  unfold spectralPatch frequencyCoset
  rw [localFiniteAnnihilator_finiteCompletionBall]
  exact (isOpen_finiteCompletionBall_coset F w t₀ _).preimage Units.continuous_val

private theorem spectralPatch_self (u : ℤ) (t₀ : (K F w)ˣ) :
    t₀ ∈ spectralPatch F w u t₀ := by
  change (t₀ : K F w) - t₀ ∈ localFiniteAnnihilator F w (finiteCompletionBall F w u)
  simp

private theorem exists_small_spectralPatch (t₀ : (K F w)ˣ)
    (W : Set (K F w)ˣ) (hW : IsOpen W) (htW : t₀ ∈ W) :
    ∃ u : ℤ, spectralPatch F w u t₀ ⊆ W ∧
      (0 : K F w) ∉ frequencyCoset F w u t₀ := by
  have hopen : IsOpen ((Units.val : (K F w)ˣ → K F w) '' W) :=
    IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap _ hW
  obtain ⟨n, _, hn⟩ := (finiteCompletionBall_hasBasis_nhds F w (t₀ : K F w)).mem_iff.mp
    (hopen.mem_nhds ⟨t₀, htW, rfl⟩)
  refine ⟨-n - (localDifferentExponent F w : ℤ), ?_, ?_⟩
  · intro t ht
    have hx := hn (show (t : K F w) - t₀ ∈ finiteCompletionBall F w n by
      simpa [spectralPatch, frequencyCoset, localFiniteAnnihilator_finiteCompletionBall] using ht)
    obtain ⟨s, hs, heq⟩ := hx
    exact (Units.val_injective heq) ▸ hs
  · intro hz
    have hx := hn (show (0 : K F w) - t₀ ∈ finiteCompletionBall F w n by
      simpa [frequencyCoset, localFiniteAnnihilator_finiteCompletionBall] using hz)
    obtain ⟨s, _, hs⟩ := hx
    exact s.ne_zero hs

include hm hρ in
private theorem raw_chart_locallyConstant (v : V) (c : LocalChart F ζ hζ w m) :
    IsLocallyConstant (fun t : c.ball.domain => rawOrbitMap F ζ hζ w ρ v (c.lift t)) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  exact ((smoothRepresentation_orbit_isLocallyConstant ρ hρ v).comp
    (quotientMap F ζ hζ w ρ 1)).comp_continuous
      (continuous_subtype_val.comp c.continuous_lift)

theorem exists_spectral_patch_lift (t₀ : (K F w)ˣ)
    (c : LocalChart F ζ hζ w m) (ht₀ : t₀ ∈ c.ball.domain)
    (W : Set (K F w)ˣ) (hW : IsOpen W) (htW : t₀ ∈ W)
    (e : J F ζ hζ w ρ) :
    ∃ (u : ℤ) (v : V),
      quotientMap F ζ hζ w ρ 1 (ρ (c.lift ⟨t₀, ht₀⟩).val v) = e ∧
      spectralPatch F w u t₀ ⊆ c.ball.domain ∩ W ∧
      ∃ hzero : (0 : K F w) ∉ frequencyCoset F w u t₀,
      ∃ f : Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ),
        (∀ t : c.ball.domain, t.val ∈ spectralPatch F w u t₀ →
          rawOrbitMap F ζ hζ w ρ v (c.lift t) = e) ∧
        (∀ p : P F ζ hζ w, slope F ζ hζ w p ∉ spectralPatch F w u t₀ →
          sectionValue F ζ hζ w m (ψ F w) f p = 0) ∧
        (∀ t : c.ball.domain, chartValue F ζ hζ w m (ψ F w) c f t =
          if t.val ∈ spectralPatch F w u t₀ then e else 0) ∧
        orbitSectionMap F ζ hζ w ρ m hm hρ hgen
          ⟨projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v,
            projector_mem_ordinaryKernel F ζ hζ w ρ m hm hρ u t₀ hzero v⟩ = f := by
  obtain ⟨v₀, hv₀⟩ := rootCoinvariantsMk_surjective ρ
    (KPLocalSmoothRepresentation.upperRoot F ζ hζ w) (ψ F w) e
  let p₀ := c.lift ⟨t₀, ht₀⟩
  let v := ρ p₀.val⁻¹ v₀
  have hv : rawOrbitMap F ζ hζ w ρ v p₀ = e := by
    change quotientMap F ζ hζ w ρ 1 (ρ p₀.val (ρ p₀.val⁻¹ v₀)) = e
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, quotientMap] using hv₀
  let L := {t : c.ball.domain | rawOrbitMap F ζ hζ w ρ v (c.lift t) = e}
  have hL : IsOpen L := (raw_chart_locallyConstant F ζ hζ w ρ m hm hρ v c).isOpen_fiber e
  let W' := Subtype.val '' L ∩ W
  have hW' : IsOpen W' :=
    ((c.ball.open_domain.isOpenEmbedding_subtypeVal).isOpenMap _ hL).inter hW
  obtain ⟨u, hu, hzero⟩ := exists_small_spectralPatch F w t₀ W' hW'
    ⟨⟨⟨t₀, ht₀⟩, hv, rfl⟩, htW⟩
  have hD : spectralPatch F w u t₀ ⊆ c.ball.domain ∩ W := by
    intro t ht
    obtain ⟨⟨s, _, rfl⟩, hW⟩ := hu ht
    exact ⟨s.property, hW⟩
  have hconst : ∀ t : c.ball.domain, t.val ∈ spectralPatch F w u t₀ →
      rawOrbitMap F ζ hζ w ρ v (c.lift t) = e := by
    intro t ht
    obtain ⟨s, hs, heq⟩ := (hu ht).1
    have heq' : s = t := Subtype.ext heq
    exact heq' ▸ hs
  let f := orbitSectionMap F ζ hζ w ρ m hm hρ hgen
    ⟨projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v,
      projector_mem_ordinaryKernel F ζ hζ w ρ m hm hρ u t₀ hzero v⟩
  refine ⟨u, v, hv, hD, hzero, f, hconst, ?_, ?_, rfl⟩
  · intro p hp
    obtain ⟨d, ht, _⟩ := exists_localChart F ζ hζ w m hm
      (slope F ζ hζ w p) Set.univ isOpen_univ (Set.mem_univ _)
    let t : d.ball.domain := ⟨slope F ζ hζ w p, ht⟩
    have heq := values_eq_of_chart_eq F ζ hζ w ρ m f 0 d t p rfl
    apply heq
    change rawOrbitMap F ζ hζ w ρ
      (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v) (d.lift t) = 0
    rw [rawOrbitMap_projector_chart F ζ hζ w ρ m hm hρ]
    exact if_neg hp
  · intro t
    change rawOrbitMap F ζ hζ w ρ
      (projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v) (c.lift t) = _
    rw [rawOrbitMap_projector_chart F ζ hζ w ρ m hm hρ]
    by_cases ht : t.val ∈ spectralPatch F w u t₀
    · simp only [show (t.val : K F w) ∈ frequencyCoset F w u t₀ from ht,
        ht, if_true, hconst t ht]
    · exact (if_neg ht).trans (if_neg ht).symm

private theorem finite_cutoff_mem {X E I : Type*} [AddCommGroup E] [Module ℂ E]
    (M : Submodule ℂ (X → E)) (D : I → Set X) (T : Finset I) (f : X → E)
    (hstab : ∀ i ∈ T, ∀ g ∈ M, (D i).indicator g ∈ M)
    (hloc : ∀ i ∈ T, (D i).indicator f ∈ M)
    (hs : ∀ x, (∀ i ∈ T, x ∉ D i) → f x = 0) : f ∈ M := by
  classical
  induction T using Finset.induction_on generalizing f with
  | empty =>
    have hf : f = 0 := funext fun x => hs x (by simp)
    rw [hf]
    exact M.zero_mem
  | @insert i T hi ih =>
    have hfi : (D i).indicator f ∈ M := hloc i (by simp)
    let f' := f - (D i).indicator f
    have hf' : f' ∈ M := by
      apply ih f'
      · intro j hj
        exact hstab j (Finset.mem_insert_of_mem hj)
      · intro j hj
        have heq : (D j).indicator f' =
            (D j).indicator f - (D i).indicator ((D j).indicator f) := by
          funext x
          by_cases hxi : x ∈ D i <;> by_cases hxj : x ∈ D j <;>
            simp [f', hxi, hxj]
        rw [heq]
        exact M.sub_mem (hloc j (Finset.mem_insert_of_mem hj))
          (hstab i (by simp) _ (hloc j (Finset.mem_insert_of_mem hj)))
      · intro x hx
        by_cases hxi : x ∈ D i
        · simp [f', hxi]
        · have hf := hs x (by
            intro j hj
            rcases Finset.mem_insert.mp hj with rfl | hj
            · exact hxi
            · exact hx j hj)
          simp [f', hxi, hf]
    have heq : f = f' + (D i).indicator f := by dsimp [f']; abel
    rw [heq]
    exact M.add_mem hf' hfi

private theorem projector_value (u : ℤ) (t₀ : (K F w)ˣ)
    (v : ordinaryKernel F ζ hζ w ρ) (p : P F ζ hζ w) :
    sectionValue F ζ hζ w m (ψ F w)
      (orbitSectionMap F ζ hζ w ρ m hm hρ hgen
        ⟨projector F ζ hζ w ρ m hm hρ u (t₀ : K F w) v.val,
          projector_preserves_ordinaryKernel F ζ hζ w ρ m hm hρ u t₀ v⟩) p =
      if slope F ζ hζ w p ∈ spectralPatch F w u t₀ then
        sectionValue F ζ hζ w m (ψ F w)
          (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v) p else 0 := by
  obtain ⟨c, ht, _⟩ := exists_localChart F ζ hζ w m hm
    (slope F ζ hζ w p) Set.univ isOpen_univ (Set.mem_univ _)
  let t : c.ball.domain := ⟨slope F ζ hζ w p, ht⟩
  have hp := orbitSectionMap_projector_chart F ζ hζ w ρ m hm hρ hgen u t₀ v c t
  by_cases h : slope F ζ hζ w p ∈ spectralPatch F w u t₀
  · rw [if_pos h]
    apply values_eq_of_chart_eq F ζ hζ w ρ m _ _ c t p rfl
    simpa only [show (t.val : K F w) ∈ frequencyCoset F w u t₀ from h, if_true] using hp
  · rw [if_neg h]
    apply values_eq_of_chart_eq F ζ hζ w ρ m _ 0 c t p rfl
    change chartValue F ζ hζ w m (ψ F w) c
      (orbitSectionMap F ζ hζ w ρ m hm hρ hgen _) t = 0
    simpa only [show (t.val : K F w) ∉ frequencyCoset F w u t₀ from h, if_false] using hp

private theorem standardCharacter_locallyConstant : IsLocallyConstant (ψ F w) := by
  change IsLocallyConstant (fun x : Multiplicative (K F w) =>
    Circle.toUnits (localFiniteCharacter F w (1 * Multiplicative.toAdd x)))
  simpa only [one_mul, Function.comp_def] using
    ((isLocallyConstant_localFiniteCharacter F w).comp_continuous
      (show Continuous (Multiplicative.toAdd : Multiplicative (K F w) → K F w)
        from continuous_id)).comp Circle.toUnits

private theorem patch_surjective (c : LocalChart F ζ hζ w m)
    (f : PatchSections F ζ hζ w m (ψ F w) c (J F ζ hζ w ρ)) :
    ∃ v, orbitSectionMap F ζ hζ w ρ m hm hρ hgen v = f.val := by
  let M := (rawOrbitMap F ζ hζ w ρ |>.comp (ordinaryKernel F ζ hζ w ρ).subtype).range
  let g := chartValue F ζ hζ w m (ψ F w) c f.val
  have hg : IsLocallyConstant g := by
    have h := (patchEquiv F ζ hζ w m hm (ψ F w)
      (standardCharacter_locallyConstant F w) c (J F ζ hζ w ρ) f).property.1
    convert h using 1
    funext t
    exact (patchEquiv_value F ζ hζ w m hm (ψ F w)
      (standardCharacter_locallyConstant F w) c f t).symm
  have hl (x : c.ball.domain) :
      ∃ u : ℤ, x.val ∈ spectralPatch F w u x.val ∧
        ∃ v : ordinaryKernel F ζ hζ w ρ,
          ∀ p : P F ζ hζ w, rawOrbitMap F ζ hζ w ρ v.val p =
            if slope F ζ hζ w p ∈ spectralPatch F w u x.val then
              sectionValue F ζ hζ w m (ψ F w) f.val p else 0 := by
    let W := Subtype.val '' {t : c.ball.domain | g t = g x}
    have hW : IsOpen W := c.ball.open_domain.isOpenEmbedding_subtypeVal.isOpenMap _
      (hg.isOpen_fiber (g x))
    obtain ⟨u, v, hv, hD, hzero, f₀, hc, hs, hf, hT⟩ :=
      exists_spectral_patch_lift F ζ hζ w ρ m hm hρ hgen x.val c x.property W hW
        ⟨x, rfl, rfl⟩ (g x)
    let v' : ordinaryKernel F ζ hζ w ρ :=
      ⟨projector F ζ hζ w ρ m hm hρ u (x.val : K F w) v,
        projector_mem_ordinaryKernel F ζ hζ w ρ m hm hρ u x.val hzero v⟩
    refine ⟨u, spectralPatch_self F w u x.val, v', ?_⟩
    intro p
    change sectionValue F ζ hζ w m (ψ F w)
      (orbitSectionMap F ζ hζ w ρ m hm hρ hgen v') p = _
    rw [show orbitSectionMap F ζ hζ w ρ m hm hρ hgen v' = f₀ from hT]
    by_cases hp : slope F ζ hζ w p ∈ spectralPatch F w u x.val
    · rw [if_pos hp]
      let t : c.ball.domain := ⟨slope F ζ hζ w p, (hD hp).1⟩
      apply values_eq_of_chart_eq F ζ hζ w ρ m f₀ f.val c t p rfl
      rw [hf, if_pos hp]
      obtain ⟨s, hs, heq⟩ := (hD hp).2
      have heq' : s = t := Subtype.ext heq
      exact (heq' ▸ hs).symm
    · rw [if_neg hp]
      exact hs p hp
  choose u hu v hv using hl
  obtain ⟨T, hT⟩ := c.ball.compact_domain.elim_finite_subcover
    (fun x : c.ball.domain => spectralPatch F w (u x) x.val)
    (fun x => spectralPatch_open F w (u x) x.val)
    (by intro x hx; exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hu ⟨x, hx⟩⟩)
  have hmem : sectionValue F ζ hζ w m (ψ F w) f.val ∈ M := by
    apply finite_cutoff_mem M
      (fun x : c.ball.domain => (slope F ζ hζ w) ⁻¹' spectralPatch F w (u x) x.val) T
    · intro x hx g hg
      obtain ⟨v₀, rfl⟩ := hg
      refine ⟨⟨projector F ζ hζ w ρ m hm hρ (u x) (x.val : K F w) v₀.val,
        projector_preserves_ordinaryKernel F ζ hζ w ρ m hm hρ (u x) x.val v₀⟩, ?_⟩
      funext p
      change sectionValue F ζ hζ w m (ψ F w)
        (orbitSectionMap F ζ hζ w ρ m hm hρ hgen
          ⟨projector F ζ hζ w ρ m hm hρ (u x) (x.val : K F w) v₀.val,
            projector_preserves_ordinaryKernel F ζ hζ w ρ m hm hρ (u x) x.val v₀⟩) p = _
      rw [projector_value F ζ hζ w ρ m hm hρ hgen]
      by_cases hp : slope F ζ hζ w p ∈ spectralPatch F w (u x) x.val <;>
        simp [hp, Set.indicator, Set.mem_preimage, orbitSectionMap_value]
    · intro x hx
      refine ⟨v x, ?_⟩
      funext p
      exact (hv x p).trans (by
        by_cases hp : slope F ζ hζ w p ∈ spectralPatch F w (u x) x.val <;>
          simp [hp, Set.indicator, Set.mem_preimage])
    · intro p hp
      apply f.property p
      intro hpc
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hT hpc)
      obtain ⟨hx, hpx⟩ := Set.mem_iUnion.mp hx
      exact hp x hx hpx
  obtain ⟨v₀, hv₀⟩ := hmem
  refine ⟨v₀, ?_⟩
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  exact hv₀

theorem orbitSectionMap_surjective :
    Function.Surjective (orbitSectionMap F ζ hζ w ρ m hm hρ hgen) := by
  intro f
  obtain ⟨r, c, v, hf⟩ := finite_patch_decomposition F ζ hζ w m hm (ψ F w)
    (standardCharacter_locallyConstant F w) f
  choose x hx using fun i => patch_surjective F ζ hζ w ρ m hm hρ hgen (c i) (v i)
  refine ⟨∑ i, x i, ?_⟩
  rw [map_sum]
  exact (Finset.sum_congr rfl (fun i _ => hx i)).trans hf.symm

def orbitEquiv : (ordinaryKernel F ζ hζ w ρ) ≃ₗ[ℂ]
    Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ) :=
  LinearEquiv.ofBijective (orbitSectionMap F ζ hζ w ρ m hm hρ hgen)
    ⟨orbitSectionMap_injective F ζ hζ w ρ m hm hρ hgen,
      orbitSectionMap_surjective F ζ hζ w ρ m hm hρ hgen⟩

@[simp] theorem orbitEquiv_apply (v : ordinaryKernel F ζ hζ w ρ) :
    orbitEquiv F ζ hζ w ρ m hm hρ hgen v =
      orbitSectionMap F ζ hζ w ρ m hm hρ hgen v := by
  rfl

theorem orbitEquiv_symm_intertwines (p : P F ζ hζ w)
    (f : Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ)) :
    (orbitEquiv F ζ hζ w ρ m hm hρ hgen).symm
      (rightAction F ζ hζ w m hm (ψ F w) (J F ζ hζ w ρ) p f) =
    ordinaryKernelRepresentation F ζ hζ w ρ p
      ((orbitEquiv F ζ hζ w ρ m hm hρ hgen).symm f) := by
  apply (orbitEquiv F ζ hζ w ρ m hm hρ hgen).injective
  let E := orbitEquiv F ζ hζ w ρ m hm hρ hgen
  exact (E.apply_symm_apply _).trans (((orbitSectionMap_intertwines
    F ζ hζ w ρ m hm hρ hgen p (E.symm f)).trans
    (congrArg (rightAction F ζ hζ w m hm (ψ F w) (J F ζ hζ w ρ) p)
      (E.apply_symm_apply f))).symm)

@[simp] theorem orbitEquiv_symm_quotient
    (f : Sections F ζ hζ w m (ψ F w) (J F ζ hζ w ρ)) :
    quotientMap F ζ hζ w ρ 1
      ((orbitEquiv F ζ hζ w ρ m hm hρ hgen).symm f).val =
        sectionValue F ζ hζ w m (ψ F w) f 1 := by
  rw [← orbitSectionMap_at_one F ζ hζ w ρ m hm hρ hgen]
  change sectionValue F ζ hζ w m (ψ F w)
    ((orbitEquiv F ζ hζ w ρ m hm hρ hgen)
      ((orbitEquiv F ζ hζ w ρ m hm hρ hgen).symm f)) 1 = _
  rw [LinearEquiv.apply_symm_apply]

end DedekindZetaZeroFree.KPKirillovOrbitMapSurjective

end
