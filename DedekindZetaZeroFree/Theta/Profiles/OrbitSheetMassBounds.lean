module

public import DedekindZetaZeroFree.Theta.Profiles.AbsoluteSheetBounds

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitFrequencies
open MomentSources NumberField MeasureTheory ThetaProfileHaarSheets ThetaSheetExactUnfolding
open scoped NumberField Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

def gammaEquiv : ThetaReflectionData.rationalGamma R.A ≃* R.A.Gamma1 :=
  MulEquiv.ofBijective
    ({ toFun := fun γ => ⟨⟨R.A.diagonal γ.val, R.A.Gamma_le_G1
          (Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩)⟩,
          Subgroup.mem_map.mpr ⟨γ.val, γ.property, rfl⟩⟩
       map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
       map_mul' := by intro x y; apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _ } :
      ThetaReflectionData.rationalGamma R.A →* R.A.Gamma1)
    (by
      constructor
      · intro x y h
        apply Subtype.ext
        apply Units.ext
        let w : InfinitePlace F := Classical.choice inferInstance
        have hw := congrArg (fun γ : R.A.Gamma1 => (γ.val.val.1 w : w.Completion)) h
        exact (algebraMap F w.Completion).injective hw
      · intro γ
        obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp γ.property
        refine ⟨⟨a, ha⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        exact he)

@[simp] lemma gammaEquiv_val (γ : ThetaReflectionData.rationalGamma R.A) :
    (gammaEquiv R γ).val.val = R.A.diagonal γ.val := rfl

end DedekindZetaZeroFree.OrbitFrequencies

end
