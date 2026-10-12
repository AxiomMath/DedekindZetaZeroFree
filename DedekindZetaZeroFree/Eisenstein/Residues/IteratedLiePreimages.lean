module

public import DedekindZetaZeroFree.Eisenstein.Residues.LieDerivativePreimages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw hiding G
open KPGlobalResidualConstruction KPContActualSphericalRightFieldIdentification
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem native_word_flat_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (f : Flat F ζ hζ K)
    (Cf : FlatScalarResidue F ζ hζ f) (w : List (Fin (groupDimension F))) :
    ∃ (v : Flat F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ).K)
      (Cv : FlatScalarResidue F ζ hζ v),
      v.val 0 = actualRightWord F ζ hζ w (f.val 0) ∧
      (∀ s g, v.val s g = scalarWeight F ζ hζ s (v.val 0) g) ∧
      Cv.numerator 0 = actualRightWord F ζ hζ w (Cf.numerator 0) := by
  induction w with
  | nil =>
    obtain ⟨v,Cv,hv,hC⟩ := canonical_flat_residue F ζ hζ hK f Cf
    have hv0 : v.val 0 = f.val 0 := by ext g; simp [hv]
    refine ⟨v,Cv,hv0,?_,funext hC⟩
    intro s g
    rw [hv,hv0]
    rfl
  | cons b w ih =>
    obtain ⟨v,Cv,hv0,hv,hC⟩ := ih
    obtain ⟨u,Cu,hu0,hu,hCu⟩ := native_flat_residue F ζ hζ b v Cv hv
    exact ⟨u,Cu,by rw [hu0,hv0]; rfl,hu,by rw [hCu,hC]; rfl⟩

end DedekindZetaZeroFree.RootDerivatives

end
