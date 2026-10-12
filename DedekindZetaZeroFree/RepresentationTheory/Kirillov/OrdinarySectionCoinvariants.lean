module

public import DedekindZetaZeroFree.RepresentationTheory.Kirillov.GenuineSectionTensorCharts

@[expose] public section

noncomputable section

set_option maxHeartbeats 2000000

set_option maxRecDepth 4096

set_option synthInstance.maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPKirillovSectionOrdinaryVanishing

open scoped NumberField TensorProduct

open NumberField IsDedekindDomain

open KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F))
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (ψ : Multiplicative (K F w) →* ℂˣ)

noncomputable instance sectionAddCommGroup
    (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (Sections F ζ hζ w m ψ E) := by
  letI := KPLocalSmoothRepresentation.finiteCoverTopology F ζ hζ w m
  letI := (KPPGLLocalCover.finite_topological_cover F ζ hζ w m hm).2.2.1
  letI : AddCommGroup (EqSections (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ E) 1) := Submodule.addCommGroup _
  letI : AddCommGroup (SmoothInd (H F ζ hζ w)
      (coefficientRepresentation F ζ hζ w ψ E) 1) := Submodule.addCommGroup _
  exact Submodule.addCommGroup (CompactSmoothInd (H F ζ hζ w)
    (coefficientRepresentation F ζ hζ w ψ E) 1)

end DedekindZetaZeroFree.KPKirillovSectionOrdinaryVanishing

end

section

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPKirillovSectionOrdinaryVanishing

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain
open KPKirillovGenuineSectionCharts

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (w : HeightOneSpectrum (RingOfIntegers F))
  (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F w m)
  (ψ : Multiplicative (K F w) →* ℂˣ)

def ordinaryRootAction (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Representation ℂ (Multiplicative (K F w)) (Sections F ζ hζ w m ψ E) where
  toFun b := rightAction F ζ hζ w m hm ψ E (n F ζ hζ w b.toAdd)
  map_one' := by
    have hn : n F ζ hζ w 0 = 1 := by
      apply Subtype.ext
      exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_one
    simpa only [toAdd_one, hn] using
      (rightAction F ζ hζ w m hm ψ E).map_one
  map_mul' := by
    intro a b
    have hn : n F ζ hζ w (a.toAdd + b.toAdd) =
        n F ζ hζ w a.toAdd * n F ζ hζ w b.toAdd := by
      apply Subtype.ext
      exact (KPLocalSmoothRepresentation.upperRoot F ζ hζ w).map_mul a b
    simpa only [toAdd_mul, hn] using
      (rightAction F ζ hζ w m hm ψ E).map_mul
        (n F ζ hζ w a.toAdd) (n F ζ hζ w b.toAdd)

@[simp] theorem ordinaryRootAction_apply
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : K F w) (f : Sections F ζ hζ w m ψ E) :
    ordinaryRootAction F ζ hζ w m hm ψ E (Multiplicative.ofAdd b) f =
      rightAction F ζ hζ w m hm ψ E (n F ζ hζ w b) f := rfl

def ordinaryTensorRootAction (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Representation ℂ (Multiplicative (K F w))
      (Sections F ζ hζ w m ψ ℂ ⊗[ℂ] E) where
  toFun b := TensorProduct.map
    (ordinaryRootAction F ζ hζ w m hm ψ ℂ b) LinearMap.id
  map_one' := by
    apply TensorProduct.ext
    ext f v
    change TensorProduct.map _ _ (f ⊗ₜ[ℂ] v) = f ⊗ₜ[ℂ] v
    simp
  map_mul' := by
    intro a b
    apply TensorProduct.ext
    ext f v
    change TensorProduct.map _ _ (f ⊗ₜ[ℂ] v) =
      TensorProduct.map _ _ (TensorProduct.map _ _ (f ⊗ₜ[ℂ] v))
    simp [Module.End.mul_apply]

def ordinaryRelationSpan (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Submodule ℂ (Sections F ζ hζ w m ψ E) :=
  Submodule.span ℂ (Set.range fun bf : K F w × Sections F ζ hζ w m ψ E =>
    rightAction F ζ hζ w m hm ψ E (n F ζ hζ w bf.1) bf.2 - bf.2)

private theorem root_preserves_patch {E : Type*} [AddCommGroup E] [Module ℂ E]
 (c : LocalChart F ζ hζ w m) (b : K F w)
 (f : PatchSections F ζ hζ w m ψ c E) :
 rightAction F ζ hζ w m hm ψ E (n F ζ hζ w b) f.val ∈
 PatchSections F ζ hζ w m ψ c E := by
 intro p hp
 rw [rightAction_apply]
 apply f.property
 simpa only [map_mul, show slope F ζ hζ w (n F ζ hζ w b) = 1 from
   MonoidHom.mem_ker.mp (n_mem_H F ζ hζ w b), mul_one] using hp
private theorem chart_sub {E : Type*} [AddCommGroup E] [Module ℂ E]
 (c : LocalChart F ζ hζ w m) (f g : Sections F ζ hζ w m ψ E)
 (t : c.ball.domain) :
 chartValue F ζ hζ w m ψ c (f-g) t =
 chartValue F ζ hζ w m ψ c f t - chartValue F ζ hζ w m ψ c g t := rfl
include hm in
private theorem patch_sub_eq (hψ : IsLocallyConstant ψ)
 {E : Type*} [AddCommGroup E] [Module ℂ E]
 (c : LocalChart F ζ hζ w m) (f g : PatchSections F ζ hζ w m ψ c E)
 (h : ∀ t, chartValue F ζ hζ w m ψ c f.val t = chartValue F ζ hζ w m ψ c g.val t) : f=g := by
 apply (patchEquiv F ζ hζ w m hm ψ hψ c E).injective
 apply Subtype.ext
 funext t
 simpa only [patchEquiv_value] using h t
private theorem lc_factor (hψ : IsLocallyConstant ψ)
 (c : LocalChart F ζ hζ w m) (b : K F w) :
 IsLocallyConstant (fun t : c.ball.domain =>
 ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ) - 1)⁻¹) := by
 have hc : Continuous (fun t : c.ball.domain =>
   Multiplicative.ofAdd ((t.val : K F w) * b)) := by fun_prop
 exact (hψ.comp_continuous hc).comp (fun x : ℂˣ => ((x : ℂ)-1)⁻¹)
private theorem residual_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
 (a : ℂ) (v : E) (h : a = 1 → v = 0) : v - (a-1) • ((a-1)⁻¹ • v) = 0 := by
 by_cases ha : a = 1
 · simp [ha, h ha]
 · rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr ha), one_smul, sub_self]
include hm in
private theorem patch_mem_aux (hψ : IsLocallyConstant ψ)
 {E : Type*} [AddCommGroup E] [Module ℂ E]
 (c : LocalChart F ζ hζ w m) (s : Finset (K F w))
 (f : PatchSections F ζ hζ w m ψ c E)
 (hf : ∀ t : c.ball.domain, (∀ b ∈ s,
   (ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ) = 1) →
   chartValue F ζ hζ w m ψ c f.val t = 0) :
 f.val ∈ ordinaryRelationSpan F ζ hζ w m hm ψ E := by
 classical
 letI : CompactSpace c.ball.domain := isCompact_iff_compactSpace.mp c.ball.compact_domain
 induction s using Finset.induction_on generalizing f with
 | empty =>
   have he : f = 0 := patch_sub_eq F ζ hζ w m hm ψ hψ c f 0 (by
     intro t
     exact hf t (by simp))
   simpa only [he, Submodule.coe_zero] using
     (ordinaryRelationSpan F ζ hζ w m hm ψ E).zero_mem
 | @insert b s hb ih =>
   let fv := patchEquiv F ζ hζ w m hm ψ hψ c E f
   let gv : CompactFunctions c.ball.domain E :=
     ⟨fun t => ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1)⁻¹ • fv.val t,
       ⟨(lc_factor F ζ hζ w m ψ hψ c b).comp₂ fv.property.1 (fun a v => a • v),
        HasCompactSupport.of_compactSpace _⟩⟩
   let g := (patchEquiv F ζ hζ w m hm ψ hψ c E).symm gv
   let d : PatchSections F ζ hζ w m ψ c E :=
     ⟨rightAction F ζ hζ w m hm ψ E (n F ζ hζ w b) g.val - g.val,
       (PatchSections F ζ hζ w m ψ c E).sub_mem
         (root_preserves_patch F ζ hζ w m hm ψ c b g) g.property⟩
   have hd : d.val ∈ ordinaryRelationSpan F ζ hζ w m hm ψ E :=
     Submodule.subset_span ⟨(b, g.val), rfl⟩
   have hg (t : c.ball.domain) : chartValue F ζ hζ w m ψ c g.val t =
       ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1)⁻¹ •
         chartValue F ζ hζ w m ψ c f.val t := by
     rw [← patchEquiv_value F ζ hζ w m hm ψ hψ c g t]
     change (patchEquiv F ζ hζ w m hm ψ hψ c E
       ((patchEquiv F ζ hζ w m hm ψ hψ c E).symm gv)).val t = _
     rw [LinearEquiv.apply_symm_apply]
     exact congrArg (fun x => ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1)⁻¹ • x)
       (patchEquiv_value F ζ hζ w m hm ψ hψ c f t)
   have hdt (t : c.ball.domain) : chartValue F ζ hζ w m ψ c d.val t =
     ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1) •
       (((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1)⁻¹ •
       chartValue F ζ hζ w m ψ c f.val t) := by
     change chartValue F ζ hζ w m ψ c
       (rightAction F ζ hζ w m hm ψ E (n F ζ hζ w b) g.val - g.val) t = _
     rw [chart_sub, chartValue_right_root]
     rw [show (ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ) •
       chartValue F ζ hζ w m ψ c g.val t - chartValue F ζ hζ w m ψ c g.val t =
       ((ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ)-1) •
       chartValue F ζ hζ w m ψ c g.val t by rw [sub_smul, one_smul], hg]
   have hr : (f-d).val ∈ ordinaryRelationSpan F ζ hζ w m hm ψ E := by
     apply ih
     intro t ht
     change chartValue F ζ hζ w m ψ c (f.val-d.val) t = 0
     rw [chart_sub, hdt]
     apply residual_zero
     intro ha
     apply hf t
     intro a ha'
     rcases Finset.mem_insert.mp ha' with rfl | ha'
     · exact ha
     · exact ht a ha'
   simpa only [Submodule.coe_sub, sub_add_cancel] using
     (ordinaryRelationSpan F ζ hζ w m hm ψ E).add_mem hr hd
include hm in
private theorem patch_mem (hψ : IsLocallyConstant ψ) (hψne : ψ ≠ 1)
 {E : Type*} [AddCommGroup E] [Module ℂ E]
 (c : LocalChart F ζ hζ w m) (f : PatchSections F ζ hζ w m ψ c E) :
 f.val ∈ ordinaryRelationSpan F ζ hζ w m hm ψ E := by
 classical
 have hx : ∃ x : K F w, (ψ (Multiplicative.ofAdd x) : ℂ) ≠ 1 := by
   by_contra! h
   apply hψne
   apply MonoidHom.ext
   intro x
   apply Units.ext
   exact h x.toAdd
 let U : K F w → Set c.ball.domain := fun b =>
   {t | (ψ (Multiplicative.ofAdd ((t.val : K F w) * b)) : ℂ) ≠ 1}
 have hU (b : K F w) : IsOpen (U b) := by
   have hc : Continuous (fun t : c.ball.domain =>
     Multiplicative.ofAdd ((t.val : K F w) * b)) := by fun_prop
   exact (hψ.comp_continuous hc).comp (fun x : ℂˣ => (x : ℂ)) {1}ᶜ
 have hcover : Set.univ ⊆ ⋃ b, U b := by
   intro t _
   rcases hx with ⟨x, hx⟩
   refine Set.mem_iUnion.mpr ⟨x / (t.val : K F w), ?_⟩
   change (ψ (Multiplicative.ofAdd ((t.val : K F w) * (x / (t.val : K F w)))) : ℂ) ≠ 1
   simpa only [mul_div_cancel₀ _ t.val.ne_zero] using hx
 letI : CompactSpace c.ball.domain := isCompact_iff_compactSpace.mp c.ball.compact_domain
 obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU hcover
 apply patch_mem_aux F ζ hζ w m hm ψ hψ c s f
 intro t ht
 obtain ⟨b, hb, hbt⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
 exact False.elim (hbt (ht b hb))

include hm in

theorem section_mem_ordinaryRelationSpan
    (hψ : IsLocallyConstant ψ) (hψne : ψ ≠ 1)
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : Sections F ζ hζ w m ψ E) :
    f ∈ ordinaryRelationSpan F ζ hζ w m hm ψ E := by
  obtain ⟨r, c, v, hv⟩ := finite_patch_decomposition F ζ hζ w m hm ψ hψ f
  rw [hv]
  exact Submodule.sum_mem _ (fun i hi => patch_mem F ζ hζ w m hm ψ hψ hψne (c i) (v i))

include hm in

theorem ordinaryRelationSpan_eq_top
    (hψ : IsLocallyConstant ψ) (hψne : ψ ≠ 1)
    (E : Type*) [AddCommGroup E] [Module ℂ E] :
    ordinaryRelationSpan F ζ hζ w m hm ψ E = ⊤ := by
  ext f
  simpa only [Submodule.mem_top, iff_true] using
    section_mem_ordinaryRelationSpan F ζ hζ w m hm ψ hψ hψne f

theorem ordinary_section_coinvariants_vanish
    (hψ : IsLocallyConstant ψ) (hψne : ψ ≠ 1)
    (E : Type*) [AddCommGroup E] [Module ℂ E] :
    Subsingleton (Representation.Coinvariants
      (ordinaryRootAction F ζ hζ w m hm ψ E)) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  change Representation.Coinvariants.ker (ordinaryRootAction F ζ hζ w m hm ψ E) = ⊤
  rw [← ordinaryRelationSpan_eq_top F ζ hζ w m hm ψ hψ hψne E]
  unfold Representation.Coinvariants.ker ordinaryRelationSpan
  congr 1

end DedekindZetaZeroFree.KPKirillovSectionOrdinaryVanishing

end
end
