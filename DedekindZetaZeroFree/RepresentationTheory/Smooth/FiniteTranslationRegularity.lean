module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries
public import DedekindZetaZeroFree.Eisenstein.Residues.FiniteLevelActionsAndDensity

@[expose] public section

noncomputable section
open scoped NumberField Classical
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.RawFiniteCompact
open KPLiteralRaw
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 theorem smooth_translate (a : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (f : Functions F ζ hζ) (hf : Smooth F ζ hζ f) :
    Smooth F ζ hζ (rightAction F ζ hζ a.val f) := by
  letI : IsTopologicalGroup (G F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  obtain ⟨hfc, hfs, U, hU⟩ := hf
  let e : KPGlobalTorusFunctionData.finitePart F ζ hζ →*
      KPGlobalTorusFunctionData.finitePart F ζ hζ := (MulAut.conj a⁻¹).toMonoidHom
  have he : Continuous e := IsTopologicalGroup.continuous_conj a⁻¹
  let V : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨U.toOpenSubgroup ⊓ U.toOpenSubgroup.comap e he,
      U.isCompact.inter_right (U.toOpenSubgroup.comap e he).isClosed⟩
  refine ⟨hfc.comp (continuous_id.mul continuous_const), ?_, V, ?_⟩
  · intro g
    have hs := hfs (g * a.val)
    convert hs using 1
    funext x
    change f (g * archChart F ζ hζ x * a.val) = f (g * a.val * archChart F ζ hζ x)
    rw [mul_assoc, (ActualFiniteTranslationEstimates.archChart_commutes_finite F ζ hζ x a).eq,
      ← mul_assoc]
  · intro g u hu
    obtain ⟨b, hb, rfl⟩ := hu
    have hb' : e b ∈ U.toOpenSubgroup := hb.2
    have hb'' : a⁻¹ * b * a ∈ U.toOpenSubgroup := by
      change a⁻¹ * b * (a⁻¹)⁻¹ ∈ U.toOpenSubgroup at hb'
      simpa only [inv_inv] using hb'
    have hbU : (a⁻¹ * b * a).val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ U :=
      ⟨a⁻¹ * b * a, hb'', rfl⟩
    have h := hU (g * a.val) _ hbU
    change f (g * b.val * a.val) = f (g * a.val)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left] using h

end DedekindZetaZeroFree.KPGlobalResidualConstruction.RawFiniteCompact

end
