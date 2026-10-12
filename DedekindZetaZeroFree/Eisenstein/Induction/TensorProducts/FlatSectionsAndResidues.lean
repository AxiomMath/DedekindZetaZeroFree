module

public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.FiniteTranslationCovariance
public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RightWordFiniteSums
public import DedekindZetaZeroFree.Eisenstein.Induction.Convolution.ProjectedFlatExpansion

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open KPLiteralRaw
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_zero → smooth_zero
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_add → smooth_add
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming smooth_smul → smooth_smul
open _root_.DedekindZetaZeroFree.KPLiteralPeriod.SpanAutomorphy renaming finite_level_exists → finite_level_exists
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_add → kfinite_add
open _root_.DedekindZetaZeroFree.KPLiteralTensor.KernelAndHCRange.CoreGeneration.ActualProjectedFlatExpansion renaming kfinite_smul → kfinite_smul
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def literalFlatModule (K : Subgroup (G F ζ hζ)) :
    Submodule ℂ (ℂ → Functions F ζ hζ) where
  carrier := {f | (∀ s, Induced F ζ hζ s (f s)) ∧
    (∀ s (t : KPGlobalTorusFunctionData.E F ζ hζ) (k : K),
      f s (t.val * k.val) = KPGlobalExceptionalParameter.realLogPower
        (((KPGlobalTorusFunctionData.delta F ζ hζ t : NNReal) : ℝ)) s *
        f 0 (t.val * k.val)) ∧ KFinite F ζ hζ K (f 0)}
  zero_mem' := by
    obtain ⟨U⟩ := finite_level_exists F ζ hζ
    refine ⟨fun s => ⟨smooth_zero F ζ hζ U, ?_⟩, ?_, ?_⟩
    · intros; simp
    · intros; simp
    · exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun k v hv => by
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv, map_zero]⟩
  add_mem' := by
    rintro f g ⟨hf, hff, hfk⟩ ⟨hg, hgf, hgk⟩
    refine ⟨fun s => ⟨smooth_add F ζ hζ _ _ (hf s).1 (hg s).1, ?_⟩,
      ?_, kfinite_add F ζ hζ K _ _ hfk hgk⟩
    · intro r x a
      simp only [Pi.add_apply, (hf s).2 r x a, (hg s).2 r x a]
      ring
    · intro s t k
      simp only [Pi.add_apply, hff s t k, hgf s t k]
      ring
  smul_mem' := by
    rintro c f ⟨hf, hff, hfk⟩
    refine ⟨fun s => ⟨smooth_smul F ζ hζ c _ (hf s).1, ?_⟩,
      ?_, kfinite_smul F ζ hζ K _ hfk c⟩
    · intro r x a
      simp only [Pi.smul_apply, smul_eq_mul, (hf s).2 r x a]
      ring
    · intro s t k
      simp only [Pi.smul_apply, smul_eq_mul, hff s t k]
      ring

abbrev asLiteralFlat {K : Subgroup (G F ζ hζ)} (f : literalFlatModule K) : Flat F ζ hζ K := f

def literalFlatZero (K : Subgroup (G F ζ hζ)) :
    literalFlatModule K →ₗ[ℂ] Functions F ζ hζ :=
  (LinearMap.proj (0 : ℂ)).comp (literalFlatModule K).subtype

theorem literalFlatZero_injective {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) : Function.Injective (literalFlatZero K) := by
  intro f g h
  apply Subtype.ext
  funext z x
  have he := KPLiteralTensorEquivariance.FiniteClearedCovariance.flat_finite_combination_of_zero
    F ζ hζ K hK (asLiteralFlat f) 1 (fun _ => 1) (fun _ => asLiteralFlat g)
    (by
      intro x
      simp only [Fin.sum_univ_one, one_mul]
      exact congrFun h x) z x
  simpa using he

def literalFlatResidue {K : Subgroup (G F ζ hζ)} (hK : IwasawaCompact F ζ hζ K)
    (E N : Flat F ζ hζ K → ℂ → Functions F ζ hζ)
    (hg : ExceptionalGerm F ζ hζ K E N)
    (hm : ∀ f g, MeromorphicOn (fun z => E f z g) KPContinuation.spectralDomain) :
    literalFlatModule K →ₗ[ℂ] Functions F ζ hζ where
  toFun f := N (asLiteralFlat f) 0
  map_add' f g := by
    funext x
    let v : Fin 2 → Flat F ζ hζ K := ![asLiteralFlat f, asLiteralFlat g]
    have ht := literal_cleared_finite_transfer E N hg hm (asLiteralFlat (f + g)) v
      (fun _ _ => 1) (fun _ => analyticOnNhd_const) 1 (by
        intro z hz a
        simp_rw [hg.1 _ z hz]
        unfold eisenstein
        simp only [mul_one]
        have hs := Summable.tsum_add
          (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (asLiteralFlat f) z hz a)
          (KPLiteralExceptionalResidue.chamberConvergence F ζ hζ K hK (asLiteralFlat g) z hz a)
        simpa [v, Fin.sum_univ_two, asLiteralFlat] using hs) x
    simpa [v, Fin.sum_univ_two] using ht
  map_smul' c f := by
    funext x
    have ht := literal_cleared_finite_transfer E N hg hm (asLiteralFlat (c • f))
      (fun _ : Fin 1 => asLiteralFlat f) (fun _ _ => c)
      (fun _ => analyticOnNhd_const) 1 (by
        intro z hz a
        simp_rw [hg.1 _ z hz]
        unfold eisenstein
        simp only [mul_one, Fin.sum_univ_one]
        exact tsum_mul_left) x
    simpa using ht

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
