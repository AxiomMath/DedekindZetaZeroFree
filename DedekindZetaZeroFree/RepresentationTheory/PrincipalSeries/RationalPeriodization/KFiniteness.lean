module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.Archimedean.FiniteDimensionalCompactOrbit
public import DedekindZetaZeroFree.Theta.Periods.CompactKernelOrbitData

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages KPAdelicCoverRestrictedProduct
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local notation "π₀" => fun g : Raw R => scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
  (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)

def rawPullback : Functions R →ₗ[ℂ] (Raw R → ℂ) where
  toFun f g := f (π₀ g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rawPullback_injective : Function.Injective (rawPullback R) := by
  intro f h he
  funext g
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g => exact congrFun he g

private theorem finiteQuotient_val_mul (g h : Raw R) :
    (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 (g*h)).val =
      (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 g).val *
      (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 h).val := by
  change (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12)
    ((amalgamation F R.A.zeta12 R.A.primitive_zeta12)
      ((EisensteinReferenceSections.FiniteSourceTopology.finiteProjection F R.A.zeta12 R.A.primitive_zeta12) (g*h))) = _
  rw [map_mul, map_mul, map_mul]
  rfl

theorem finiteComponent_finite_space (x : PlusCore R N P C) :
    ∃ V : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ V ∧
      ∀ k : ThetaExpansion.fullProductCompactPreimage R,
        (fun g : Raw R => scalarSourceEvaluator R N P C x
          (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 (g*k.val)).val) ∈ V := by
  let J := EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 ''
    (ThetaExpansion.fullProductCompactPreimage R : Set _)
  let L : Functions R →ₗ[ℂ] (Raw R → ℂ) :=
    { toFun := fun f g => f (EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 g).val
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let O := Set.range (fun b : J => KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
    b.val.val (scalarSourceEvaluator R N P C x))
  have hO : O.Finite := scalarSource_finiteOrbit_finite R N P C x
  let V := (Submodule.span ℂ O).map L
  letI : Module.Finite ℂ (Submodule.span ℂ O) := Module.Finite.of_fg (Submodule.fg_span hO)
  refine ⟨V, inferInstance, ?_⟩
  intro k
  let b : J := ⟨EisensteinReferenceSections.FiniteSourceTopology.finiteQuotient F R.A.zeta12 R.A.primitive_zeta12 k.val, ⟨k.val, k.property, rfl⟩⟩
  refine Submodule.mem_map.mpr ⟨_, Submodule.subset_span ⟨b, rfl⟩, ?_⟩
  funext g
  change scalarSourceEvaluator R N P C x (_ * _) = _
  rw [finiteQuotient_val_mul]

theorem pureSource_raw_finite_space (s : RestrictedTensorSimple.Level (bad R P C))
    (f : ∀ p : s.val, Plus R N P C p) :
    ∃ U : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ U ∧
      ∀ k : ThetaExpansion.fullProductCompactPreimage R,
        (fun g : Raw R => scalarSourceEvaluator R N P C
          (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ f)) (π₀ (g*k.val))) ∈ U := by
  obtain ⟨A, hA, ha⟩ := pureArchProduct_finite_space R N P C s f
  obtain ⟨B, hB, hb⟩ := finiteComponent_finite_space R N P C
    (RestrictedTensorSimple.stageInclusion _ _ _ s (PiTensorProduct.tprod ℂ (finitePure R N P C s f)))
  letI := hA
  letI := hB
  refine ⟨functionProduct A B, functionProduct_finite _ _, ?_⟩
  intro k
  convert mul_mem_functionProduct A B (ha k) (hb k) using 1
  ext g
  exact scalarSource_pure_raw_factor R N P C s f (g*k.val)

theorem scalarSource_raw_finite_space (x : PlusCore R N P C) :
    ∃ U : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ U ∧
      ∀ k : ThetaExpansion.fullProductCompactPreimage R,
        (fun g : Raw R => scalarSourceEvaluator R N P C x (π₀ (g*k.val))) ∈ U := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  change ∃ U : Submodule ℂ (Raw R → ℂ), Module.Finite ℂ U ∧
    ∀ k : ThetaExpansion.fullProductCompactPreimage R,
      (fun g : Raw R => scalarSourceEvaluator R N P C (RestrictedTensorSimple.stageInclusion _ _ _ s z) (π₀ (g*k.val))) ∈ U
  induction z using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    obtain ⟨U, hU, hu⟩ := pureSource_raw_finite_space R N P C s f
    refine ⟨U, hU, ?_⟩
    intro k
    convert U.smul_mem c (hu k) using 1
    ext g
    simp only [map_smul, Pi.smul_apply]
  | add x y hx hy =>
    obtain ⟨U, hU, hu⟩ := hx
    obtain ⟨V, hV, hv⟩ := hy
    letI := hU
    letI := hV
    refine ⟨U ⊔ V, inferInstance, ?_⟩
    intro k
    convert (U ⊔ V).add_mem
      (Submodule.mem_sup_left (hu k)) (Submodule.mem_sup_right (hv k)) using 1
    ext g
    simp only [map_add, Pi.add_apply]

theorem scalarSource_kfinite (x : PlusCore R N P C) :
    KPLiteralRaw.KFinite F R.A.zeta12 R.A.primitive_zeta12 (ThetaExpansion.fullProductCompact R)
      (scalarSourceEvaluator R N P C x) := by
  let f := scalarSourceEvaluator R N P C x
  let O := Set.range (fun k : ThetaExpansion.fullProductCompact R =>
    KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 k.val f)
  let W := Submodule.span ℂ O
  obtain ⟨U, hU, hu⟩ := scalarSource_raw_finite_space R N P C x
  letI := hU
  have hle : W.map (rawPullback R) ≤ U := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, ⟨k, rfl⟩, rfl⟩
    obtain ⟨a, ha, he⟩ := k.property
    have heq : rawPullback R (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 k.val f) =
        (fun g : Raw R => scalarSourceEvaluator R N P C x (π₀ (g*a))) := by
      funext g
      change f (π₀ g * k.val) = f (π₀ (g*a))
      rw [← he]
      change f ((scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)) *
        scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (amalgamation F R.A.zeta12 R.A.primitive_zeta12 a)) =
        f (scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (amalgamation F R.A.zeta12 R.A.primitive_zeta12 (g*a)))
      rw [map_mul, map_mul]
    rw [heq]
    exact hu ⟨a, ha⟩
  haveI : Module.Finite ℂ (W.map (rawPullback R)) := Submodule.finiteDimensional_of_le hle
  haveI : Module.Finite ℂ W := FiniteDimensional.of_injective
    (((rawPullback R).comp W.subtype).codRestrict (W.map (rawPullback R))
      (fun w => Submodule.mem_map.mpr ⟨w.val, w.property, rfl⟩))
    (by
      intro u v h
      apply Subtype.ext
      apply rawPullback_injective R
      exact congrArg Subtype.val h)
  refine ⟨W, inferInstance, ?_, ?_⟩
  · have h : KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12
        (1 : ThetaExpansion.fullProductCompact R).val f ∈ W := Submodule.subset_span ⟨1, rfl⟩
    simpa using h
  · intro k v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      apply Submodule.subset_span
      refine ⟨k*l, ?_⟩
      change KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 (k.val*l.val) f =
        KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 k.val
          (KPLiteralRaw.rightAction F R.A.zeta12 R.A.primitive_zeta12 l.val f)
      rw [map_mul, Module.End.mul_apply]
    | zero => simpa using W.zero_mem
    | add a b ha hb hia hib => simpa using W.add_mem hia hib
    | smul c a ha hi => simpa using W.smul_mem c hi

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
