module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas

@[expose] public section

noncomputable section
open scoped Classical
open MeasureTheory
namespace DedekindZetaZeroFree.KPContGenericEndMapRigidity

private theorem actual_element_of_open_overlap
    {G X : Type*} [Group G] [Countable G] [TopologicalSpace X]
    [MeasurableSpace X] [MulAction G X] [ContinuousConstSMul G X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    (hnull : ∀ g : G, g ≠ 1 → μ {x : X | g • x = x} = 0)
    (Γ P : Subgroup G) (V : Set X) (hV : IsOpen V)
    (hlift : ∀ x ∈ V, ∀ y ∈ V, (∃ γ : Γ, γ • x = y) → ∃ p : P, p • x = y)
    (γ : Γ) (x : X) (hx : x ∈ V) (hγx : γ • x ∈ V) : (γ : G) ∈ P := by
  by_contra hnot
  let O := V ∩ ((fun y : X => (γ : G) • y) ⁻¹' V)
  have hO : IsOpen O := hV.inter (hV.preimage (continuous_const_smul (γ : G)))
  have hOne : O.Nonempty := ⟨x, hx, hγx⟩
  have hsub : O ⊆ ⋃ p : P, {y : X | ((p : G)⁻¹ * (γ : G)) • y = y} := by
    intro y hy
    obtain ⟨p, hp⟩ := hlift y hy.1 ((γ : G) • y) hy.2 ⟨γ, rfl⟩
    apply Set.mem_iUnion.mpr
    refine ⟨p, ?_⟩
    change ((p : G)⁻¹ * (γ : G)) • y = y
    change (p : G) • y = (γ : G) • y at hp
    rw [mul_smul, ← hp, inv_smul_smul]
  have hn : ∀ p : P, (p : G)⁻¹ * (γ : G) ≠ 1 := by
    intro p he
    have heq : (γ : G) = p := (inv_mul_eq_one.mp he).symm
    exact hnot (heq ▸ p.property)
  have hz : μ (⋃ p : P, {y : X | ((p : G)⁻¹ * (γ : G)) • y = y}) = 0 :=
    measure_iUnion_null (fun p => hnull _ (hn p))
  exact hO.measure_ne_zero μ hOne (measure_mono_null hsub hz)

theorem actual_high_intersection_of_endMap_injective
    (F : Type) [Field F] [NumberField F]
    (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ)
    (hembed : Function.Injective (KPFiniteCuspAtlas.endMap F Γ q σ T))
    (γ : Γ) (z : KPArch.Space (KPCuspLogShape.dimension F))
    (hz : z ∈ KPCuspSiegel.highCusp F σ T)
    (hγz : (γ : KPCuspArithmetic.PGL2 F) • z ∈ KPCuspSiegel.highCusp F σ T) :
    (γ : KPCuspArithmetic.PGL2 F) ∈ KPCuspSiegel.parabolic F Γ q := by
  let : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ) (M := F)
  let : Countable (Matrix (Fin 2) (Fin 2) F) := by
    change Countable (Fin 2 → Fin 2 → F); infer_instance
  let : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
    Function.Injective.countable Units.val_injective
  let : Countable (KPCuspArithmetic.PGL2 F) :=
    Function.Surjective.countable Matrix.ProjGenLinGroup.mk_surjective
  let := KPFiniteAdelicCuspEnds.canonicalAction_continuousConstSMul F
  apply actual_element_of_open_overlap (volume : Measure (KPArch.Space (KPCuspLogShape.dimension F)))
    (KPFiniteAdelicCuspEnds.FundamentalDomainGeometry.rationalProjective_fixed_locus_volume_zero F hd)
    Γ (KPCuspSiegel.parabolic F Γ q) (KPCuspSiegel.highCusp F σ T)
    (KPCuspSiegel.isOpen_highCusp F σ T) _ γ z hz hγz
  intro x hx y hy hxy
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  obtain ⟨y₀, hy₀, rfl⟩ := hy
  let c := (KPCuspCharts.toArchHomeomorph F hd).symm x₀
  let d := (KPCuspCharts.toArchHomeomorph F hd).symm y₀
  have hc : KPCuspCharts.toArch F c = x₀ :=
    (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply x₀
  have hd' : KPCuspCharts.toArch F d = y₀ :=
    (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply y₀
  have hcT : T < c.2 := by
    rw [← KPCuspCharts.toArch_meanHeight F hd c, hc]; exact hx₀
  have hdT : T < d.2 := by
    rw [← KPCuspCharts.toArch_meanHeight F hd d, hd']; exact hy₀
  have heq : KPFiniteCuspAtlas.endMap F Γ q σ T
      (Quotient.mk _ (⟨d, hdT⟩ : {p : KPCuspCharts.Coordinates F // T < p.2})) =
      KPFiniteCuspAtlas.endMap F Γ q σ T
      (Quotient.mk _ (⟨c, hcT⟩ : {p : KPCuspCharts.Coordinates F // T < p.2})) := by
    simp only [KPFiniteCuspAtlas.endMap, Quotient.lift_mk, hc, hd']
    exact Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr hxy))
  have hrel := Quotient.exact (hembed heq)
  obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hrel)
  refine ⟨⟨KPCuspGenuineMonodromy.cuspInclusion F Γ q σ p, ?_⟩, ?_⟩
  · change (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ p : KPCuspArithmetic.PGL2 F) ∈
      Γ ⊓ MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q
    obtain ⟨k, hk, he⟩ := Subgroup.mem_map.mp p.property
    have he' : (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ p : KPCuspArithmetic.PGL2 F) = k := by
      rw [KPCuspGenuineMonodromy.cuspInclusion_formula, ← he]
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
    rw [he']; exact hk
  · change (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ p : KPCuspArithmetic.PGL2 F) •
      (σ • x₀) = σ • y₀
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula, mul_smul, mul_smul, inv_smul_smul]
    change (p : KPCuspArithmetic.PGL2 F) • KPCuspCharts.toArch F c = KPCuspCharts.toArch F d at hp
    rw [← hc, ← hd', hp]

end DedekindZetaZeroFree.KPContGenericEndMapRigidity

end
