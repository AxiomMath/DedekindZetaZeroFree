module

public import DedekindZetaZeroFree.Eisenstein.Sections.CompactTensorProfiles
public import DedekindZetaZeroFree.Eisenstein.Induction.Spherical.CompactJetHolomorphy

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalParameterStage
open KPLiteralRaw
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming canonicalCutCore → canonicalCutCore
open _root_.DedekindZetaZeroFree.KPLiteralExceptionalResidue.CompactTupleTransfer renaming reweight_expansion_in_canonical_core → reweight_expansion_in_canonical_core

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 abbrev Core := KPMsRationalCompactCrossPairing.Vplus F ζ hζ
  (KPContFlatFullProductIwasawa.iwasawaData F ζ hζ)

 local instance sourceAddCommGroup :
    AddCommGroup (KPMsRationalCompactCrossPairing.Source F ζ hζ 0) :=
  Submodule.addCommGroup _
 local instance coreAddCommGroup : AddCommGroup (Core F ζ hζ) :=
  Submodule.addCommGroup _

 abbrev stage (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    Submodule ℂ (Core F ζ hζ) :=
  Submodule.span ℂ (Set.range (fun a : C => canonicalCutCore F ζ hζ K hK a.val f))

 instance stageAddCommGroup (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    AddCommGroup (stage F ζ hζ K hK f C) :=
  Submodule.addCommGroup (stage F ζ hζ K hK f C)

 instance stageFiniteDimensional (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    FiniteDimensional ℂ (stage F ζ hζ K hK f C) :=
  Module.Finite.of_fg (Submodule.fg_span (Set.finite_range _))

 instance stageFree (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    Module.Free ℂ (stage F ζ hζ K hK f C) :=
  Module.Free.of_divisionRing ℂ (stage F ζ hζ K hK f C)

 abbrev Coordinates (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :=
  Fin (Module.finrank ℂ (stage F ζ hζ K hK f C)) → ℂ

 def coordinates (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    stage F ζ hζ K hK f C ≃ₗ[ℂ] Coordinates F ζ hζ K hK f C :=
  (Module.finBasis ℂ (stage F ζ hζ K hK f C)).equivFun

 def inclusion (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    Coordinates F ζ hζ K hK f C →ₗ[ℂ] Core F ζ hζ :=
  (stage F ζ hζ K hK f C).subtype.comp (coordinates F ζ hζ K hK f C).symm.toLinearMap

private theorem inclusion_injective (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    Function.Injective (inclusion F ζ hζ K hK f C) :=
  (stage F ζ hζ K hK f C).subtype_injective.comp (coordinates F ζ hζ K hK f C).symm.injective

 def coefficient (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) (a : C) :
    stage F ζ hζ K hK f C :=
  ⟨canonicalCutCore F ζ hζ K hK a.val f, Submodule.subset_span ⟨a, rfl⟩⟩

 def family (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ)
    (s : ℂ) : Coordinates F ζ hζ K hK f C :=
  ∑ a : C, Complex.exp (s * (a.val : ℂ)) •
    coordinates F ζ hζ K hK f C (coefficient F ζ hζ K hK f C a)

private theorem family_entire (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) :
    Differentiable ℂ (family F ζ hζ K hK f C) := by
  classical
  have hd := Differentiable.sum (u := (Finset.univ : Finset C))
    (A := fun a s => Complex.exp (s * (a.val : ℂ)) •
      coordinates F ζ hζ K hK f C (coefficient F ζ hζ K hK f C a))
    (fun a _ => (Complex.differentiable_exp.comp
      (differentiable_id.mul_const (a.val : ℂ))).smul (differentiable_const (𝕜 := ℂ) _))
  convert hd using 1
  funext s
  change (∑ a : C, Complex.exp (s * (a.val : ℂ)) •
    coordinates F ζ hζ K hK f C (coefficient F ζ hζ K hK f C a)) = _
  simp only [Finset.sum_apply]

private theorem inclusion_family_formula (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ) (s : ℂ) :
    inclusion F ζ hζ K hK f C (family F ζ hζ K hK f C s) =
      ∑ a : C, Complex.exp (s * (a.val : ℂ)) • canonicalCutCore F ζ hζ K hK a.val f := by
  simp [family, inclusion, coefficient]

private theorem literal_parameter_stage (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ C : Finset ℝ, ∀ (s : ℂ) (g : G F ζ hζ),
      KPContFlatStageJetHolomorphy.parameterSection F ζ hζ
        (inclusion F ζ hζ K hK f C) 0 s (family F ζ hζ K hK f C s) g = f.val s g := by
  obtain ⟨C, hC⟩ := reweight_expansion_in_canonical_core F ζ hζ K hK f
  refine ⟨C, ?_⟩
  intro s g
  have he : (inclusion F ζ hζ K hK f C (family F ζ hζ K hK f C s)).val.val g =
      ∑ a ∈ C, Complex.exp (s * (a : ℂ)) * (canonicalCutCore F ζ hζ K hK a f).val.val g := by
    rw [inclusion_family_formula]
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_coe_sort C (fun a : ℝ => Complex.exp (s * (a : ℂ)) *
      (canonicalCutCore F ζ hζ K hK a f).val.val g)
  simp only [KPContFlatStageJetHolomorphy.parameterSection, pow_zero, one_mul,
    KPContFlatStageJetHolomorphy.L, KPContFlatSourceRecipe.flatR_formula]
  rw [he, ← hC s g]
  rw [← mul_assoc, ← Complex.exp_add]
  simp

private theorem inclusion_smooth (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) (C : Finset ℝ)
    (v : Coordinates F ζ hζ K hK f C) :
    (inclusion F ζ hζ K hK f C v).val ∈
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
  have h := (inclusion F ζ hζ K hK f C v).property
  change (inclusion F ζ hζ K hK f C v).val ∈
    KPGlobalEisensteinData.hcHeckeCore _ _ _ at h
  apply (show KPGlobalEisensteinData.hcHeckeCore _ _ _ ≤
      KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) from ?_) h
  unfold KPGlobalEisensteinData.hcHeckeCore
  exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left

 theorem literal_entire_coordinate_stage (K : Subgroup (G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (ι : (Fin n → ℂ) →ₗ[ℂ] Core F ζ hζ) (p : ℂ → (Fin n → ℂ)),
      Function.Injective ι ∧ Differentiable ℂ p ∧
      (∀ v, (ι v).val ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
        (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0)) ∧
      ∀ s g, KPContFlatStageJetHolomorphy.parameterSection F ζ hζ ι 0 s (p s) g =
        f.val s g := by
  obtain ⟨C, hC⟩ := literal_parameter_stage F ζ hζ K hK f
  exact ⟨Module.finrank ℂ (stage F ζ hζ K hK f C), inclusion F ζ hζ K hK f C,
    family F ζ hζ K hK f C, inclusion_injective F ζ hζ K hK f C,
    family_entire F ζ hζ K hK f C, inclusion_smooth F ζ hζ K hK f C, hC⟩

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.CanonicalParameterStage

end
