module

public import DedekindZetaZeroFree.Theta.Periods.NondegenerateCovariantTensorSource
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.HarishChandra.SimplicityAndScalarEndomorphisms

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.FourierContinuation.HCGeneration
open KPGlobalResidualConstruction

abbrev ComplexGenerator := KPCplxCharacterHaar.ComplexSU2 ⊕ Fin 6

def complexGenerator : ComplexGenerator → Module.End ℂ complexCore
  | Sum.inl k => complexCoreCompactLinearMap k
  | Sum.inr i => NativeComplexHCOperators.operators i

def complexWord : List ComplexGenerator → Module.End ℂ complexCore
  | [] => LinearMap.id
  | a :: w => (complexGenerator a).comp (complexWord w)

def complexWordSpan (v : complexCore) : Submodule ℂ complexCore :=
  Submodule.span ℂ (Set.range (fun w => complexWord w v))

theorem complexWordSpan_generator (v : complexCore) (a : ComplexGenerator)
    (x : complexCore) (hx : x ∈ complexWordSpan v) :
    complexGenerator a x ∈ complexWordSpan v := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    exact Submodule.subset_span ⟨a :: w, rfl⟩
  | zero => simpa using (complexWordSpan v).zero_mem
  | add x y hx hy ihx ihy =>
    simpa using (complexWordSpan v).add_mem ihx ihy
  | smul c x hx ih =>
    simpa using (complexWordSpan v).smul_mem c ih

private theorem complexWordSpan_algebra (v : complexCore)
    (a : NativeComplexHCSource.algebra NativeComplexHCOperators.operators)
    (x : complexCore) (hx : x ∈ complexWordSpan v) :
    a.val x ∈ complexWordSpan v := by
  obtain ⟨a, ha⟩ := a
  induction ha using Algebra.adjoin_induction generalizing x with
  | mem a ha =>
    rcases ha with ⟨k, rfl⟩ | ⟨i, rfl⟩
    · exact complexWordSpan_generator v (Sum.inl k) x hx
    · exact complexWordSpan_generator v (Sum.inr i) x hx
  | algebraMap c => exact (complexWordSpan v).smul_mem c hx
  | add a b ha hb iha ihb =>
    exact (complexWordSpan v).add_mem (iha x hx) (ihb x hx)
  | mul a b ha hb iha ihb => exact iha _ (ihb x hx)

theorem complexWordSpan_eq_top (v : complexCore) (hv : v ≠ 0) :
    complexWordSpan v = ⊤ := by
  letI := NativeComplexHCAlgebraic.native_operators_simple
  let W : Submodule (NativeComplexHCSource.algebra NativeComplexHCOperators.operators)
      complexCore := {
    carrier := complexWordSpan v
    zero_mem' := (complexWordSpan v).zero_mem
    add_mem' := (complexWordSpan v).add_mem
    smul_mem' := fun a x hx => complexWordSpan_algebra v a x hx }
  have hvW : v ∈ W := Submodule.subset_span ⟨[], rfl⟩
  have hW : W ≠ ⊥ := by
    intro h
    exact hv (show v ∈ (⊥ : Submodule _ complexCore) from h ▸ hvW)
  have ht : W = ⊤ := (eq_bot_or_eq_top W).resolve_left hW
  apply Submodule.eq_top_iff'.mpr
  intro x
  exact show x ∈ W from ht ▸ Submodule.mem_top

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
        obtain ⟨k, rfl⟩ := hx
        exact Submodule.subset_span ⟨g * k, by simp [map_mul]⟩
      | zero => simp
      | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
      | smul c x hx ih => simpa using Submodule.smul_mem _ c ih }
  have hvW : v ∈ W := Submodule.subset_span ⟨1, by simp⟩
  have hW : W = ⊤ := (eq_bot_or_eq_top W).resolve_left (by
    intro h
    exact hv (show v ∈ (⊥ : Subrepresentation ρ) from h ▸ hvW))
  exact congrArg Subrepresentation.toSubmodule hW

open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (M : ∀ q, LocalImageData R q)

theorem finite_orbit_span (q : KPFinitePlace F)
    (v : actualLocal R M (Sum.inr q)) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun a =>
      KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (M q).inducing (M q).inducing.polarization
        (M q).haar (M q).haar_integer a v)) = ⊤ := by
  apply irreducible_orbit_span _ _ v hv
  exact (KPRankOneShellRepair.ActualSourcePredicates.actual_images_irreducible_of_length
    F R.A.zeta12 R.A.primitive_zeta12 q (M q).inducing
    (M q).inducing.polarization (M q).haar (M q).haar_integer).1.2

end DedekindZetaZeroFree.FourierContinuation.HCGeneration

end
