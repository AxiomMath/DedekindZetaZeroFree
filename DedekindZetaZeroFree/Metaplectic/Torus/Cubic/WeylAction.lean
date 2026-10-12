module

public import DedekindZetaZeroFree.Metaplectic.Torus.Cubic.SignedWeylConjugation

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel.Geometry
noncomputable section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))
local notation "H" => ActualFiniteTorus.H F ζ hζ q
local notation "W" => KPPGLLocalCover.signedW F ζ hζ (Sum.inr q)

 theorem W_inv : W⁻¹ = W := by
  apply inv_eq_of_mul_eq_one_left
  exact (pow_two _).symm.trans (KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q))

def weyl : H ≃ₜ* H where
  toFun t := ⟨W⁻¹ * t.val * W, signedW_preserves_torus F ζ hζ q t⟩
  invFun t := ⟨W⁻¹ * t.val * W, signedW_preserves_torus F ζ hζ q t⟩
  left_inv t := by
    apply Subtype.ext
    change W⁻¹ * (W⁻¹ * t.val * W) * W = t.val
    rw [W_inv]
    simp only [← mul_assoc, ← pow_two, KPPGLLocalCover.signedW_sq, one_mul]
    rw [mul_assoc, ← pow_two, KPPGLLocalCover.signedW_sq, mul_one]
  right_inv t := by
    apply Subtype.ext
    change W⁻¹ * (W⁻¹ * t.val * W) * W = t.val
    rw [W_inv]
    simp only [← mul_assoc, ← pow_two, KPPGLLocalCover.signedW_sq, one_mul]
    rw [mul_assoc, ← pow_two, KPPGLLocalCover.signedW_sq, mul_one]
  map_mul' x y := by
    apply Subtype.ext
    change W⁻¹ * (x.val * y.val) * W = (W⁻¹ * x.val * W) * (W⁻¹ * y.val * W)
    group
  continuous_toFun := (continuous_const.mul continuous_subtype_val |>.mul continuous_const).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val |>.mul continuous_const).subtype_mk _

def weylCenter : ActualFiniteTorus.C F ζ hζ q ≃* ActualFiniteTorus.C F ζ hζ q :=
  Subgroup.centerCongr (weyl F ζ hζ q).toMulEquiv

theorem weyl_central (e : rootsOfUnity 3 F) :
    weyl F ζ hζ q (ActualFiniteTorus.central F ζ hζ q e) =
      ActualFiniteTorus.central F ζ hζ q e := by
  apply Subtype.ext
  change W⁻¹ * (KPPGLLocalCover.centralInjection F ζ hζ (Sum.inr q) e) * W = _
  have hc := Subgroup.mem_center_iff.mp
    (KPPGLLocalCover.centralInjection_range_le_center F ζ hζ (Sum.inr q) ⟨e, rfl⟩) W
  rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
  rfl

theorem weyl_cube (y : (q.adicCompletion F)ˣ) :
    weylCenter F ζ hζ q (ActualFiniteTorus.cubeLift F ζ hζ q y) =
      ActualFiniteTorus.cubeLift F ζ hζ q y⁻¹ := by
  apply Subtype.ext
  apply Subtype.ext
  change W⁻¹ * ActualFiniteTorus.normalWord F ζ hζ q 1 (y ^ 3) * W =
    ActualFiniteTorus.normalWord F ζ hζ q 1 (y⁻¹ ^ 3)
  simpa using signedW_conjugates_normalWord F ζ hζ q 1 (y ^ 3)

end
end DedekindZetaZeroFree.ActualFiniteBorel.Geometry
