module

public import DedekindZetaZeroFree.Theta.Unfolding.OrbitExtractionDefinitions

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.OrbitExpansion
open NumberField IsDedekindDomain KPAdelicCoverRestrictedProduct
open scoped NumberField Classical Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
attribute [local instance] KPAdelicCoverRestrictedProduct.localTopology
  KPAdelicCoverRestrictedProduct.pglLocalTopology
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming good_A → good_A
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming integral_iff → integral_iff
open _root_.DedekindZetaZeroFree.KPRationalAdelicSplitting renaming eval_localIdele → eval_localIdele
variable {F : Type} [Field F] [NumberField F]

private theorem restricted_coordinates_continuous
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    {X : Type*} [TopologicalSpace X]
    (f : X → RestrictedCover F ζ hζ)
    (hc : ∀ v, Continuous (fun x => f x v))
    (hu : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ S : Set (KPHilbert.Place F), Filter.cofinite ≤ Filter.principal S ∧
        ∀ y ∈ U, ∀ v ∈ S, f y v ∈ compact F ζ hζ v) :
    Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨U, hU, hx, S, hS, hm⟩ := hu x
  let r : U → RestrictedProduct (fun v => KPLocalCover.CubicGL2Raw F ζ hζ v)
      (fun v => (compact F ζ hζ v : Set _)) (Filter.principal S) :=
    fun y => ⟨fun v => f y.val v, hm y.val y.property⟩
  have hr : Continuous r := RestrictedProduct.continuous_rng_of_principal.mpr
    (continuous_pi (fun v => (hc v).comp continuous_subtype_val))
  have hi := (RestrictedProduct.continuous_inclusion hS).comp hr
  have he : (fun y : U => f y.val) = fun y =>
      RestrictedProduct.inclusion _ _ hS (r y) := by
    funext y
    apply RestrictedProduct.ext
    intro v
    rfl
  change Continuous (fun y : U => RestrictedProduct.inclusion _ _ hS (r y)) at hi
  rw [← he] at hi
  exact (continuousOn_iff_continuous_domRestrict.mpr hi).continuousAt (hU.mem_nhds hx)

theorem pglA_continuous (A : SArithmeticData F) :
    Continuous (KPRationalAdelicSplitting.pglA F A.zeta12 A.primitive_zeta12) := by
  have hc (v : KPHilbert.Place F) :
      Continuous (fun y : (KPAdeles F)ˣ => KPRationalAdelicSplitting.ATuple
        F A.zeta12 A.primitive_zeta12 y v) := by
    cases v with
    | inl w =>
      exact (KPStandardLocalRootLifts.complex_A_continuous
        F A.zeta12 A.primitive_zeta12 w).comp
        (((continuous_apply w).comp continuous_fst).units_map _)
    | inr q =>
      exact (KPStandardLocalRootLifts.finite_A_continuous
        F A.zeta12 A.primitive_zeta12 q _
          (depth_admissible F A.zeta12 A.primitive_zeta12 q)).comp
        (((RestrictedProduct.continuous_eval q).comp continuous_snd).units_map _)
  have ht : Continuous (KPRationalAdelicSplitting.ATuple
      F A.zeta12 A.primitive_zeta12) := by
    apply restricted_coordinates_continuous A.zeta12 A.primitive_zeta12 _ hc
    intro x
    let p : KPFinitePlace F → Prop := fun q => ¬ Bad F q ∧
      (x : KPAdeles F).2 q ∈ q.adicCompletionIntegers F ∧
      (↑x⁻¹ : KPAdeles F).2 q ∈ q.adicCompletionIntegers F
    let S : Set (KPHilbert.Place F) := {v | match v with
      | Sum.inl _ => True | Sum.inr q => p q}
    have hp : ∀ᶠ q in Filter.cofinite, p q :=
      (show ∀ᶠ q in Filter.cofinite, ¬ Bad F q from
        Filter.eventually_cofinite.mpr (by simpa using bad_finite F)).and
        ((x : KPAdeles F).2.property.and (↑x⁻¹ : KPAdeles F).2.property)
    have hS : Filter.cofinite ≤ Filter.principal S := by
      rw [Filter.le_principal_iff]
      change ∀ᶠ v in Filter.cofinite, v ∈ S
      rw [Filter.eventually_cofinite, ← Set.finite_preimage_inl_and_inr]
      exact ⟨Set.toFinite _, by simpa [S] using Filter.eventually_cofinite.mp hp⟩
    let O : Set (KPAdeles F) := {y | ∀ q, p q → y.2 q ∈ q.adicCompletionIntegers F}
    have hO : IsOpen O :=
      (RestrictedProduct.isOpen_forall_imp_mem
        (fun q : KPFinitePlace F => Valued.isOpen_valuationSubring
          (q.adicCompletion F))).preimage continuous_snd
    let U : Set ((KPAdeles F)ˣ) := {y | (y : KPAdeles F) ∈ O ∧ (↑y⁻¹ : KPAdeles F) ∈ O}
    have hU : IsOpen U := (hO.preimage Units.continuous_val).inter
      (hO.preimage (Units.continuous_val.comp continuous_inv))
    refine ⟨U, hU, ⟨fun q hq => hq.2.1, fun q hq => hq.2.2⟩, S, hS, ?_⟩
    intro y hy v hv
    cases v with
    | inl w => exact Subgroup.mem_top _
    | inr q =>
      let u : (KPTameCompact.O F q)ˣ := {
        val := ⟨(y : KPAdeles F).2 q, (integral_iff F q _).mpr (hy.1 q hv)⟩
        inv := ⟨(↑y⁻¹ : KPAdeles F).2 q, (integral_iff F q _).mpr (hy.2 q hv)⟩
        val_inv := by apply Subtype.ext; exact congrArg (fun z : KPAdeles F => z.2 q) y.val_inv
        inv_val := by apply Subtype.ext; exact congrArg (fun z : KPAdeles F => z.2 q) y.inv_val }
      have he : Units.map (KPTameCompact.O F q).subtype u =
          Units.map (adeleEval F (Sum.inr q)).toMonoidHom y := by
        apply Units.ext
        rfl
      have hh := good_A F A.zeta12 A.primitive_zeta12 q hv.1 u
      rw [he] at hh
      exact hh
  exact QuotientGroup.continuous_mk.comp (QuotientGroup.continuous_mk.comp ht)

end DedekindZetaZeroFree.OrbitExpansion

end
