module

public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.ExteriorInvariance

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

 theorem canonical_compact_translate
    (f : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
    (C : FlatScalarResidue F ζ hζ f)
    (hf : ∀ s g, f.val s g = scalarWeight F ζ hζ s (f.val 0) g)
    (a : (KPContFlatSourceRecipe.D F ζ hζ).K) :
    ∃ (v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
      (Cv : FlatScalarResidue F ζ hζ v),
      (∀ s g, v.val s g = scalarWeight F ζ hζ s (v.val 0) g) ∧
      v.val 0 = rightAction F ζ hζ a.val (f.val 0) ∧
      Cv.numerator 0 = rightAction F ζ hζ a.val (C.numerator 0) := by
  let u := rightAction F ζ hζ a.val (f.val 0)
  have hu : Induced F ζ hζ 0 u := by
    refine ⟨KPLiteralPeriod.NonzeroResidue.smooth_right_translate F ζ hζ _ (f.property.1 0).1 a.val,?_⟩
    intro r x g
    change f.val 0 (_ * a.val) = _ * f.val 0 (g*a.val)
    rw [mul_assoc,(f.property.1 0).2]
  have hk : KFinite F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K u := by
    obtain ⟨W,hW,hfW,hs⟩ := f.property.2.2
    exact ⟨W,hW,hs a _ hfW,hs⟩
  obtain ⟨v,hv⟩ := scalar_reflatten F ζ hζ u hu hk
  have hv0 : v.val 0 = u := by ext g; simp [hv,scalarWeight]
  let Cv := Classical.choice (flatScalarResidue_nonempty F ζ hζ _
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) v)
  refine ⟨v,Cv,?_,hv0,?_⟩
  · intro s g; rw [hv,hv0]
  · ext g
    have he (s : ℂ) (g : G F ζ hζ) : f.val s (g*a.val) = v.val s g := by
      rw [hf,hv]
      unfold scalarWeight u
      change Complex.exp _ * f.val 0 (g*a.val) = Complex.exp _ * f.val 0 (g*a.val)
      dsimp only [KPContFlatSourceRecipe.alpha]
      rw [KPContFlatFullProductIwasawa.alpha_mul_compact F ζ hζ g a]
    have hh := flat_finite_residue
      (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) C
      (Finset.univ : Finset Unit) (fun _ => v) (fun _ => Cv)
      (fun _ _ => 1) (fun _ _ => analyticOnNhd_const) a.val
      (by intro s g; simpa using he s g) g
    change Cv.numerator 0 g = C.numerator 0 (g*a.val)
    simpa using hh.symm

end DedekindZetaZeroFree.RootDerivatives

end
