module

public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData

@[expose] public section

noncomputable section
open scoped Classical
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPWildComplexWhittakerDictionary
open KPGlobalResidualConstruction KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
open KPCplxActualImage KPCplxWhittakerUnique
attribute [local instance] ContinuousLinearMap.addCommGroup

 def coreInImage (β : ℂˣ) : complexCore →ₗ[ℂ] Theta β :=
  complexCore.subtype.codRestrict (imageSubmodule β) (by
    intro h
    rw [imageSubmodule_eq_top]
    trivial)

 def coreRestriction (β : ℂˣ) : (Theta β →L[ℂ] ℂ) →ₗ[ℂ]
    (complexCore →ₗ[ℂ] ℂ) where
  toFun L := L.toLinearMap.comp (coreInImage β)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem coreRestriction_injective (β : ℂˣ) :
    Function.Injective (coreRestriction β) := by
  intro L M he
  ext h
  obtain ⟨a, ha, ht⟩ := KPCplxInverseTopology.harmonic_finiteSum_approximation
    negativeParameter h.val
  have hmem (N : ℕ) : (∑ ℓ ∈ Finset.range N, a ℓ) ∈ complexCore := by
    apply Submodule.sum_mem
    intro ℓ hℓ
    constructor
    · rw [imageSubmodule_eq_top]
      trivial
    · exact (le_iSup (fun ℓ => KPCplxIntertwinerEigenvalues.harmonicKType
        negativeParameter ℓ) ℓ) (ha ℓ)
  let b : ℕ → complexCore := fun N => ⟨∑ ℓ ∈ Finset.range N, a ℓ, hmem N⟩
  have hb : Filter.Tendsto (fun N => coreInImage β (b N)) Filter.atTop (nhds h) :=
    tendsto_subtype_rng.mpr ht
  have heval : (fun N => L (coreInImage β (b N))) =
      (fun N => M (coreInImage β (b N))) := by
    funext N
    exact LinearMap.congr_fun he (b N)
  have hL := (L.continuous.tendsto h).comp hb
  have hM := (M.continuous.tendsto h).comp hb
  change Filter.Tendsto (fun N => L (coreInImage β (b N))) Filter.atTop (nhds (L h)) at hL
  change Filter.Tendsto (fun N => M (coreInImage β (b N))) Filter.atTop (nhds (M h)) at hM
  rw [heval] at hL
  exact tendsto_nhds_unique hL hM

 def restrictedWhittakerSpace (β : ℂˣ) (ψ : AddChar ℂ Circle) :
    Submodule ℂ (complexCore →ₗ[ℂ] ℂ) :=
  (whittakerSpace β ψ).map (coreRestriction β)

 theorem restrictedWhittakerSpace_eq_span (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (hψ : Continuous ψ) (hne : ψ ≠ 1) :
    ∃ L : Theta β →L[ℂ] ℂ, L ≠ 0 ∧ L ∈ whittakerSpace β ψ ∧
      restrictedWhittakerSpace β ψ = Submodule.span ℂ {coreRestriction β L} := by
  obtain ⟨L, hL, hmem, -, hspan⟩ := transported_jacquet_generator β ψ hψ hne
  refine ⟨L, hL, hmem, ?_⟩
  rw [restrictedWhittakerSpace, hspan, Submodule.map_span]
  simp only [Set.image_singleton]

 theorem continuousWhittaker_comparison (β : ℂˣ) (ψ : AddChar ℂ Circle)
    (hψ : Continuous ψ) (hne : ψ ≠ 1)
    (L M : Theta β →L[ℂ] ℂ) (hL : L ∈ whittakerSpace β ψ)
    (hM : M ∈ whittakerSpace β ψ) (h : complexCore)
    (hh : coreRestriction β M h ≠ 0) :
    L = (coreRestriction β L h / coreRestriction β M h) • M := by
  have hMne : M ≠ 0 := by
    intro hz
    apply hh
    simp [hz, coreRestriction]
  let : AddCommGroup (Theta β →L[ℂ] ℂ) :=
    @ContinuousLinearMap.addCommGroup ℂ _ ℂ _ (Theta β) _ _ ℂ _ _ _ _ (RingHom.id ℂ) _
  have hd := (whittaker_dimension_one β ψ hψ hne).2
  have hMn : (⟨M, hM⟩ : whittakerSpace β ψ) ≠ 0 := by
    intro hz
    exact hMne (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd hMn
    (⟨L, hL⟩ : whittakerSpace β ψ)
  have he : L = c • M := (congrArg Subtype.val hc).symm
  have hcoef : coreRestriction β L h / coreRestriction β M h = c := by
    rw [he, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_div_cancel_right₀ c hh
  rw [hcoef]
  exact he

 def smoothImageAction (β : ℂˣ) (g : ComplexPGL2) : Theta β →L[ℂ] Theta β where
  toFun := imageAction β g
  map_add' h k := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    induction g using Quotient.inductionOn with | h g => rfl
  map_smul' c h := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    induction g using Quotient.inductionOn with | h g => rfl
  cont := (imageAction_continuous β).comp (continuous_const.prodMk continuous_id)

end DedekindZetaZeroFree.KPWildComplexWhittakerDictionary

end
