module

public import DedekindZetaZeroFree.Eisenstein.Sections.FiniteTranslateExponentialExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField
open NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000

 theorem smooth_add (f g : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) (hg : Smooth F ζ hζ g) : Smooth F ζ hζ (f + g) := by
  obtain ⟨U,hU⟩ := hf.2.2
  obtain ⟨V,hV⟩ := hg.2.2
  let W : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ V.toOpenSubgroup, U.isCompact.inter_right V.toOpenSubgroup.isClosed⟩
  refine ⟨hf.1.add hg.1, fun a => (hf.2.1 a).add (hg.2.1 a), W, ?_⟩
  intro a u hu
  have hwu : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
    Subgroup.map_mono inf_le_left hu
  have hwv : u ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ V :=
    Subgroup.map_mono inf_le_right hu
  simp only [Pi.add_apply, hU a u hwu, hV a u hwv]

 theorem smooth_smul (c : ℂ) (f : Functions F ζ hζ)
    (hf : Smooth F ζ hζ f) : Smooth F ζ hζ (c • f) := by
  refine ⟨continuous_const.smul hf.1, fun g => contDiffOn_const.smul (hf.2.1 g), ?_⟩
  obtain ⟨U,hU⟩ := hf.2.2
  exact ⟨U, fun g u hu => congrArg (fun z => c • z) (hU g u hu)⟩

 theorem kfinite_add (K : Subgroup (G F ζ hζ)) (f g : Functions F ζ hζ)
    (hf : KFinite F ζ hζ K f) (hg : KFinite F ζ hζ K g) : KFinite F ζ hζ K (f + g) := by
  obtain ⟨U,hU,hf,hUs⟩ := hf
  obtain ⟨V,hV,hg,hVs⟩ := hg
  letI := hU
  letI := hV
  refine ⟨U ⊔ V, inferInstance, Submodule.add_mem_sup hf hg, ?_⟩
  intro k w hw
  obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp hw
  exact Submodule.add_mem_sup (hUs k u hu) (hVs k v hv)

def add {K : Subgroup (G F ζ hζ)} (f g : Flat F ζ hζ K) : Flat F ζ hζ K :=
  ⟨fun s => f.val s + g.val s, (by
    intro s
    refine ⟨smooth_add F ζ hζ _ _ (f.property.1 s).1 (g.property.1 s).1, ?_⟩
    intro r x a
    simp only [Pi.add_apply, (f.property.1 s).2, (g.property.1 s).2, mul_add]),
    (by
    intro s t k
    change f.val s _ + g.val s _ = _ * (f.val 0 _ + g.val 0 _)
    rw [f.property.2.1 s t k, g.property.2.1 s t k, mul_add]),
    kfinite_add F ζ hζ K _ _ f.property.2.2 g.property.2.2⟩

def smul {K : Subgroup (G F ζ hζ)} (c : ℂ) (f : Flat F ζ hζ K) : Flat F ζ hζ K :=
  ⟨fun s => c • f.val s, (by
    intro s
    refine ⟨smooth_smul F ζ hζ c _ (f.property.1 s).1, ?_⟩
    intro r x a
    simp only [Pi.smul_apply, smul_eq_mul, (f.property.1 s).2]
    ring), (by
    intro s t k
    change c * f.val s _ = _ * (c * f.val 0 _)
    rw [f.property.2.1 s t k]
    ring), (by
    obtain ⟨U,hU,hf,hs⟩ := f.property.2.2
    exact ⟨U,hU,U.smul_mem c hf,hs⟩)⟩

 theorem level_exists : Nonempty (KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) := by
  rw [KPGlobalTorusFunctionData.FiniteLevel,
    KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
  obtain ⟨J, _⟩ := ActualFiniteFactor.productLevels_cofinal F ζ hζ Set.univ Filter.univ_mem
  exact ⟨⟨(ActualFiniteFactor.productLevel F ζ hζ J).subgroup,
    (ActualFiniteFactor.productLevel F ζ hζ J).compact⟩⟩

def zero (K : Subgroup (G F ζ hζ)) : Flat F ζ hζ K :=
  ⟨fun _ => 0, (by
    intro s
    refine ⟨⟨continuous_const, fun _ => contDiffOn_const, ?_⟩, ?_⟩
    · exact ⟨Classical.choice (level_exists F ζ hζ), by intros; rfl⟩
    · intros; simp), (by intros; simp), (by
    refine ⟨⊥, inferInstance, Submodule.zero_mem _, ?_⟩
    intro k v hv
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero])⟩

def sum {K : Subgroup (G F ζ hζ)} {I : Type} (s : Finset I)
    (c : I → ℂ) (f : I → Flat F ζ hζ K) : Flat F ζ hζ K :=
  s.toList.foldr (fun i a => add F ζ hζ (smul F ζ hζ (c i) (f i)) a) (zero F ζ hζ K)

@[simp] theorem sum_val {K : Subgroup (G F ζ hζ)} {I : Type} (s : Finset I)
    (c : I → ℂ) (f : I → Flat F ζ hζ K) (z : ℂ) (g : G F ζ hζ) :
    (sum F ζ hζ s c f).val z g = ∑ i ∈ s, c i * (f i).val z g := by
  unfold sum
  have hl (l : List I) :
      (l.foldr (fun i a => add F ζ hζ (smul F ζ hζ (c i) (f i)) a)
        (zero F ζ hζ K)).val z g = (l.map (fun i => c i * (f i).val z g)).sum := by
    induction l with
    | nil => rfl
    | cons i l ih => simpa only [List.foldr_cons, List.map_cons, List.sum_cons, add, smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul] using congrArg (fun a => c i * (f i).val z g + a) ih
  rw [hl]
  exact Finset.sum_map_toList _ _

theorem translate_lift (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q)) :
    ∃ (v : Flat F ζ hζ K) (n : ℕ) (b : Fin n → ℝ) (w : Fin n → Flat F ζ hζ K),
      (∀ z g, f.val z (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) =
          ∑ i, Complex.exp (z * (b i : ℂ)) * (w i).val z g) ∧
      (∀ z g, v.val z g = ∑ i, (w i).val z g) ∧
      ∀ g, v.val 0 g = f.val 0 (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) := by
  obtain ⟨n,b,w,he⟩ := KPLiteralTensorEquivariance.FiniteClearedCovariance.finite_translate_exponential_expansion
    F ζ hζ K hK f q a
  refine ⟨sum F ζ hζ Finset.univ (fun _ => 1) w,n,b,w,he,?_,?_⟩
  · intro z g
    simp only [sum_val, one_mul]
  · intro g
    simpa only [sum_val, one_mul, zero_mul, Complex.exp_zero] using (he 0 g).symm

end DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum

end
