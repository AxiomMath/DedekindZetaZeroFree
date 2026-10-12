module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FrozenProjectorFamily

@[expose] public section

noncomputable section
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors

theorem irreducible_orbit_span {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : ρ.IsIrreducible) (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g : G => ρ g v)) = ⊤ := by
  letI := hρ
  let W : Subrepresentation ρ := {
    toSubmodule := Submodule.span ℂ (Set.range (fun g : G => ρ g v))
    apply_mem_toSubmodule := by
      intro g x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k,rfl⟩ := hx
        exact Submodule.subset_span ⟨g*k,by simp [map_mul]⟩
      | zero => simp
      | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
      | smul a x hx ih => simpa using Submodule.smul_mem _ a ih }
  have hvW : v ∈ W := Submodule.subset_span ⟨1,by simp⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (by
    intro h
    apply hv
    have hm : v ∈ (⊥ : Subrepresentation ρ) := h ▸ hvW
    exact hm)
  exact congrArg Subrepresentation.toSubmodule hW

open MomentSources NumberField
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

theorem actualFinite_irreducible (D : SourceFactorization R Q T) (q : KPFinitePlace F) :
    (actualFiniteAction R D q).IsIrreducible :=
  (KPRankOneShellRepair.ActualSourcePredicates.actual_images_irreducible_of_length
    F R.A.zeta12 R.A.primitive_zeta12 q (D.finiteData q).inducing
    (D.finiteData q).inducing.polarization (D.finiteData q).haar (D.finiteData q).haar_integer).1.2

theorem actualFinite_orbit_span (D : SourceFactorization R Q T) (q : KPFinitePlace F)
    (v : actualLocal R D.finiteData (Sum.inr q)) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun a => actualFiniteAction R D q a v)) = ⊤ :=
  irreducible_orbit_span _ (actualFinite_irreducible R D q) v hv
end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
