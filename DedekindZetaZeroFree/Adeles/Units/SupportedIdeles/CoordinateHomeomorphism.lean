module

public import DedekindZetaZeroFree.Adeles.Units.SupportedIdeles.Norm

@[expose] public section

open scoped NumberField NNReal RestrictedProduct Classical
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.SupportedChartConstruction
open SupportedChartDefinitions
noncomputable section
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

 def finiteAssembly (x : A.G × (SupportedChartDefinitions.C A)) :
    Πʳ v : HeightOneSpectrum (𝓞 F),
      [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units]_[Filter.principal (A.Sf : Set _)ᶜ] :=
  ⟨fun v => if hv : v ∈ A.Sf then x.1.2 ⟨v, hv⟩ else x.2 ⟨v, hv⟩,
    by intro v hv; change v ∉ A.Sf at hv; dsimp; rw [dif_neg hv]; exact (x.2 ⟨v, hv⟩).property⟩

 theorem outside_cofinite : Filter.cofinite ≤ Filter.principal ((A.Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  exact Filter.le_principal_iff.mpr (A.Sf.eventually_cofinite_notMem)

def assembly (x : A.G × (SupportedChartDefinitions.C A)) : IdeleGroup F :=
  (ContinuousMulEquiv.piUnits.symm x.1.1,
    RestrictedProduct.inclusion _ _ (outside_cofinite A) (finiteAssembly A x))

theorem assembly_apply (x : A.G × (SupportedChartDefinitions.C A)) (v : HeightOneSpectrum (𝓞 F)) :
    (assembly A x).2 v =
      (if hv : v ∈ A.Sf then x.1.2 ⟨v, hv⟩ else x.2 ⟨v, hv⟩ : (v.adicCompletion F)ˣ) := rfl

theorem assembly_supported (x : A.G × (SupportedChartDefinitions.C A)) :
    assembly A x ∈ IdeleGroup.supportedAt (K := F) (A.Sf : Set _) := by
  intro v hv
  change (assembly A x).2 v ∈ _
  rw [assembly_apply, dif_neg (show v ∉ A.Sf from hv)]
  exact (x.2 ⟨v, hv⟩).property

theorem coordinates_assembly (x : A.G × (SupportedChartDefinitions.C A)) : SupportedChartDefinitions.sCoordinatesRaw A (assembly A x) = x.1 := by
  classical
  apply Prod.ext
  · exact ContinuousMulEquiv.piUnits.apply_symm_apply _
  · funext v
    change (assembly A x).2 v.val = x.1.2 v
    rw [assembly_apply, dif_pos v.property]

theorem continuous_assembly : Continuous (assembly A) := by
  apply Continuous.prodMk
  · exact ContinuousMulEquiv.piUnits.symm.continuous.comp (continuous_fst.fst)
  · apply (RestrictedProduct.continuous_inclusion (outside_cofinite A)).comp
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    by_cases hv : v ∈ A.Sf
    · simp only [Function.comp_def, finiteAssembly, RestrictedProduct.mk_apply, dif_pos hv]
      fun_prop
    · simp only [Function.comp_def, finiteAssembly, RestrictedProduct.mk_apply, dif_neg hv]
      fun_prop

def forward (a : (SupportedChartDefinitions.H A)) : A.G1 × (SupportedChartDefinitions.C A) :=
  (⟨SupportedChartDefinitions.sCoordinatesRaw A a.1.1, by
    change A.norm (SupportedChartDefinitions.sCoordinatesRaw A a.1.1) = 1
    rw [SupportedChartNorm.supported_norm A a.1.1 a.2]
    have hn : IdeleGroup.absoluteNorm a.1.1 = 1 := a.1.property
    simp [hn]⟩, SupportedChartDefinitions.exteriorCoordinates A a)

def backward (x : A.G1 × (SupportedChartDefinitions.C A)) : (SupportedChartDefinitions.H A) :=
  ⟨⟨assembly A (x.1.val, x.2), by
    change IdeleGroup.absoluteNorm (assembly A (x.1.val, x.2)) = 1
    apply Units.ext
    apply NNReal.eq
    have hn := SupportedChartNorm.supported_norm A (assembly A (x.1.val, x.2))
      (assembly_supported A _)
    rw [coordinates_assembly] at hn
    have hx : A.norm x.1.val = 1 := x.1.property
    rw [hx] at hn
    exact inv_eq_one.mp hn.symm⟩, assembly_supported A _⟩

theorem forward_backward (x : A.G1 × (SupportedChartDefinitions.C A)) : forward A (backward A x) = x := by
  classical
  apply Prod.ext
  · apply Subtype.ext
    exact coordinates_assembly A _
  · funext v
    apply Subtype.ext
    change (assembly A (x.1.val, x.2)).2 v.val = (x.2 v).val
    rw [assembly_apply, dif_neg v.property]

theorem backward_forward (a : (SupportedChartDefinitions.H A)) : backward A (forward A a) = a := by
  classical
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · exact ContinuousMulEquiv.piUnits.symm_apply_apply _
  · apply RestrictedProduct.ext
    intro v
    change (if h : v ∈ A.Sf then a.1.1.2 v else a.1.1.2 v) = _
    split <;> rfl

theorem continuous_forward : Continuous (forward A) := by
  have hc : Continuous (fun a : (SupportedChartDefinitions.H A) => a.1.1) := continuous_subtype_val.comp continuous_subtype_val
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact ContinuousMulEquiv.piUnits.continuous.comp hc.fst
    · apply continuous_pi
      intro v
      exact (RestrictedProduct.continuous_eval v.val).comp
        hc.snd
  · apply continuous_pi
    intro v
    apply Continuous.subtype_mk
    exact (RestrictedProduct.continuous_eval v.val).comp
      hc.snd

theorem continuous_backward : Continuous (backward A) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_assembly A).comp (continuous_fst.subtype_val.prodMk continuous_snd)

def chart : (SupportedChartDefinitions.H A) ≃ₜ* (A.G1 × (SupportedChartDefinitions.C A)) where
  toFun := forward A
  invFun := backward A
  left_inv := backward_forward A
  right_inv := forward_backward A
  map_mul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · funext w; exact (InfiniteIdeleGroup.component w).map_mul _ _
      · funext v; rfl
    · funext v; apply Subtype.ext; rfl
  continuous_toFun := continuous_forward A
  continuous_invFun := continuous_backward A
end
end DedekindZetaZeroFree.SupportedChartConstruction
