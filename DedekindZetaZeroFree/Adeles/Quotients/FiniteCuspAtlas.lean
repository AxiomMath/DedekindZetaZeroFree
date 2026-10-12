module

public import DedekindZetaZeroFree.Geometry.ArithmeticQuotients.Cusps.FiniteComponentCuspCharts

@[expose] public section

section

noncomputable section

open scoped Classical NumberField

open MeasureTheory

namespace DedekindZetaZeroFree

namespace KPFiniteCuspAtlas

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev FiniteCover := KPCuspGenuineMonodromy.FiniteCover F ζ hζ

abbrev SymmetricSpace := KPCuspGenuineMonodromy.SymmetricSpace F

theorem central_comm (ε : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

def sphericalRelation (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    Setoid (SymmetricSpace F × FiniteCover F ζ hζ) where
  r p p' := ∃ (γ : KPCuspArithmetic.PGL2 F) (ε : rootsOfUnity 3 F)
      (u : U.toOpenSubgroup),
    p'.1 = γ • p.1 ∧ p'.2 =
      KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε * p.2 * u
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact ⟨1, 1, 1, by simp, by simp⟩
    · rintro p p' ⟨γ, ε, u, hx, hc⟩
      refine ⟨γ⁻¹, ε⁻¹, u⁻¹, ?_, ?_⟩
      · rw [hx]; simp
      · rw [hc]
        rw [← central_comm F ζ hζ ε⁻¹
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ⁻¹)]
        simp [map_inv, mul_assoc]
    · rintro p p' p'' ⟨γ, ε, u, hx, hc⟩ ⟨δ, η, v, hy, hd⟩
      refine ⟨δ * γ, η * ε, u * v, ?_, ?_⟩
      · rw [hy, hx, mul_smul]
      · rw [hd, hc]
        simp only [map_mul]
        have hcomm := central_comm F ζ hζ η
          (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)
        simp only [mul_assoc]
        rw [← mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ η), hcomm]
        simp only [mul_assoc]
        rfl

abbrev rawXU (U : CompactOpenLevel (FiniteCover F ζ hζ)) :=
  Quotient (sphericalRelation F ζ hζ U)

end KPFiniteCuspAtlas

end DedekindZetaZeroFree

end

end

section

noncomputable section
open scoped Classical

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

theorem compact_core_of_finite_components
    {ι : Type*} [Finite ι] {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    {X : Type*} [TopologicalSpace X]
    (e : (Σ i, Y i) ≃ₜ X) (f : ∀ i, Y i → X)
    (hf : ∀ i y, e ⟨i,y⟩ = f i y)
    (J : ι → Type*) (E : ∀ i, J i → Set (Y i))
    (hc : ∀ i, IsCompact ((Set.univ : Set (Y i)) \ (⋃ a, E i a))) :
    IsCompact ((Set.univ : Set X) \ (⋃ i, ⋃ a, f i '' E i a)) := by
  have hcont : ∀ i, Continuous (f i) := by
    intro i
    have he := e.continuous.comp (continuous_sigmaMk (i := i))
    convert he using 1
    ext y
    exact (hf i y).symm
  have hset : ((Set.univ : Set X) \ (⋃ i, ⋃ a, f i '' E i a)) =
      ⋃ i, f i '' ((Set.univ : Set (Y i)) \ (⋃ a, E i a)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨i, y⟩, hy⟩ := e.surjective x
      have hfy : f i y = x := (hf i y).symm.trans hy
      apply Set.mem_iUnion.mpr
      refine ⟨i, y, ⟨Set.mem_univ _, ?_⟩, hfy⟩
      intro hE
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hE
      exact hx.2 (Set.mem_iUnion.mpr ⟨i,
        Set.mem_iUnion.mpr ⟨a, ⟨y, ha, hfy⟩⟩⟩)
    · intro hx
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨Set.mem_univ _, ?_⟩
      intro hE
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hE
      obtain ⟨a, z, hz, heq⟩ := Set.mem_iUnion.mp hj
      have hpair : (⟨j, z⟩ : Sigma Y) = ⟨i, y⟩ :=
        e.injective (by simpa only [hf] using heq)
      cases hpair
      exact hy.2 (Set.mem_iUnion.mpr ⟨a, hz⟩)
  rw [hset]
  exact isCompact_iUnion fun i => (hc i).image (hcont i)

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end
end

section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

open KPCuspGenuineMonodromy

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem central_comm (ε : rootsOfUnity 3 F) (c : FiniteCover F ζ hζ) :
    central F ζ hζ ε * c = c * central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

private theorem base_relation (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (c d : FiniteCover F ζ hζ) (γ : KPCuspArithmetic.PGL2 F) :
    (∃ u : U.toOpenSubgroup, finiteBase F ζ hζ d =
      KPFiniteComponents.diagonal F γ * finiteBase F ζ hζ c * finiteBase F ζ hζ u) ↔
    ∃ (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      d = finiteRationalLift F ζ hζ γ * central F ζ hζ ε * c * u := by
  have hd := (finite_cover_exact F ζ hζ).2.2.2.1
  have hc : ∀ ε, finiteBase F ζ hζ (central F ζ hζ ε) = 1 := by
    intro ε
    apply MonoidHom.mem_ker.mp
    rw [← (finite_cover_exact F ζ hζ).2.1]
    exact ⟨ε, rfl⟩
  constructor
  · rintro ⟨u, hu⟩
    let t := finiteRationalLift F ζ hζ γ * c * u
    have ht : finiteBase F ζ hζ d = finiteBase F ζ hζ t := by
      simpa only [t, map_mul, ← MonoidHom.comp_apply, hd] using hu
    have hk : d * t⁻¹ ∈ (central F ζ hζ).range := by
      rw [(finite_cover_exact F ζ hζ).2.1]
      change finiteBase F ζ hζ (d * t⁻¹) = 1
      rw [map_mul, map_inv, ht, mul_inv_cancel]
    obtain ⟨ε, he⟩ := hk
    refine ⟨ε, u, ?_⟩
    have he' := (eq_mul_inv_iff_mul_eq).mp he
    dsimp [t] at he'
    rw [← mul_assoc, ← mul_assoc, central_comm F ζ hζ ε (finiteRationalLift F ζ hζ γ)] at he'
    exact he'.symm
  · rintro ⟨ε, u, rfl⟩
    refine ⟨u, ?_⟩
    simp only [map_mul, hc, mul_one, ← MonoidHom.comp_apply, hd]

private theorem component_iff (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) (γ : KPCuspArithmetic.PGL2 F) :
    γ ∈ Component F ζ hζ U g ↔
      ∃ (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
        g = finiteRationalLift F ζ hζ γ * central F ζ hζ ε * g * u := by
  rw [← base_relation F ζ hζ U g g γ]
  change KPFiniteComponents.diagonal F γ ∈
    (U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)).map
      (MulAut.conj (finiteBase F ζ hζ g)).toMonoidHom ↔ _
  constructor
  · rintro ⟨b, ⟨u, hu, rfl⟩, hb⟩
    refine ⟨⟨u⁻¹, U.toOpenSubgroup.inv_mem hu⟩, ?_⟩
    simp only [MulAut.conj_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hb
    rw [← hb]
    simp [mul_assoc]
  · rintro ⟨u, hu⟩
    refine ⟨finiteBase F ζ hζ (u : FiniteCover F ζ hζ)⁻¹,
      ⟨(u : FiniteCover F ζ hζ)⁻¹, U.toOpenSubgroup.inv_mem u.property, rfl⟩, ?_⟩
    have hh := congrArg (fun b => b * (finiteBase F ζ hζ u)⁻¹ *
      (finiteBase F ζ hζ g)⁻¹) hu
    simpa [MulAut.conj_apply, mul_assoc] using hh

private theorem slice_open
    (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (s : Setoid (SymmetricSpace F × FiniteCover F ζ hζ))
    (hs : ∀ p p', s.r p p' ↔ ∃ (γ : KPCuspArithmetic.PGL2 F)
      (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      p'.1 = γ • p.1 ∧ p'.2 = finiteRationalLift F ζ hζ γ *
        central F ζ hζ ε * p.2 * u)
    (g : FiniteCover F ζ hζ) : IsOpenMap (fun x : SymmetricSpace F => Quotient.mk s (x,g)) := by
  letI : IsTopologicalGroup (Cover F ζ hζ) :=
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.1
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F) (SymmetricSpace F) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  intro O hO
  apply isQuotientMap_quotient_mk'.isCoinducing.isOpen_preimage.mp
  apply isOpen_iff_forall_mem_open.mpr
  rintro ⟨y,c⟩ ⟨x, hx, he⟩
  obtain ⟨γ, ε, u, hy, hc⟩ := (hs (x,g) (y,c)).mp (Quotient.exact he)
  let a := finiteRationalLift F ζ hζ γ * central F ζ hζ ε * g
  let V := (Homeomorph.smul γ '' O) ×ˢ
    (Homeomorph.mulLeft a '' (U.toOpenSubgroup : Set (FiniteCover F ζ hζ)))
  refine ⟨V, ?_, (Homeomorph.smul γ).isOpenMap O hO |>.prod
    ((Homeomorph.mulLeft a).isOpenMap _ U.toOpenSubgroup.isOpen), ?_⟩
  · rintro ⟨z,d⟩ ⟨⟨w, hw, rfl⟩, ⟨v, hv, rfl⟩⟩
    refine ⟨w, hw, Quotient.sound ((hs (w,g) (γ • w, a * v)).mpr ?_)⟩
    exact ⟨γ, ε, ⟨v,hv⟩, rfl, rfl⟩
  · exact ⟨⟨x,hx,hy.symm⟩, ⟨u,u.property,hc.symm⟩⟩

theorem finite_spherical_components
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (s : Setoid (KPCuspGenuineMonodromy.SymmetricSpace F ×
      KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (hs : ∀ p p', s.r p p' ↔ ∃ (γ : KPCuspArithmetic.PGL2 F)
      (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      p'.1 = γ • p.1 ∧ p'.2 =
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε * p.2 * u)
    (ι : ∀ g : KPCuspGenuineMonodromy.FiniteCover F ζ hζ,
      KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U g) →
        Quotient s)
    (hι : ∀ g x, ι g (KPCuspSiegel.projection F _ x) = Quotient.mk s (x,g)) :
    ∃ (n : ℕ) (hn : 0 < n)
      (g : Fin n → KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
      (e : (Σ i : Fin n, KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (g i))) ≃ₜ Quotient s),
      ∀ i x, e ⟨i,x⟩ = ι (g i) x := by
  classical
  let π := finiteBase F ζ hζ
  let H := U.toOpenSubgroup.toSubgroup.map π
  let D := (KPFiniteComponents.diagonal F).range
  let Q := DoubleCoset.Quotient (D : Set (KPFiniteComponents.FinitePGL2 F))
    (H : Set (KPFiniteComponents.FinitePGL2 F))
  obtain ⟨hcompact, hopen⟩ := KPCuspMonodromy.projected_finite_level_compact_open F ζ hζ U
  letI : Finite Q := kp_cusp_finite_adelic_components F H hcompact hopen
  letI : Fintype Q := Fintype.ofFinite Q
  let n := Fintype.card Q
  let r : Fin n ≃ Q := (Fintype.equivFin Q).symm
  have hπ := (finite_cover_exact F ζ hζ).2.2.1
  let g : Fin n → FiniteCover F ζ hζ := fun i => (hπ ((r i).out)).choose
  have hg : ∀ i, DoubleCoset.mk D H (π (g i)) = r i := by
    intro i
    dsimp [g]
    rw [(hπ ((r i).out)).choose_spec]
    exact Quotient.out_eq _
  have hn : 0 < n := Fintype.card_pos
  have hbase : ∀ {x y : SymmetricSpace F} {c d : FiniteCover F ζ hζ},
      s.r (x,c) (y,d) → DoubleCoset.mk D H (π c) = DoubleCoset.mk D H (π d) := by
    intro x y c d h
    obtain ⟨γ, ε, u, _, hc⟩ := (hs (x,c) (y,d)).mp h
    obtain ⟨v, hv⟩ := (base_relation F ζ hζ U c d γ).mpr ⟨ε,u,hc⟩
    exact DoubleCoset.eq.mpr ⟨_, ⟨γ,rfl⟩, _, ⟨v,v.property,rfl⟩, hv⟩
  have hinj : ∀ c, Function.Injective (ι c) := by
    intro c x y he
    induction x using Quotient.inductionOn with
    | h x =>
      induction y using Quotient.inductionOn with
      | h y =>
        change ι c (KPCuspSiegel.projection F _ x) = ι c (KPCuspSiegel.projection F _ y) at he
        rw [hι c x, hι c y] at he
        obtain ⟨γ, ε, u, hy, hc⟩ := (hs (x,c) (y,c)).mp (Quotient.exact he)
        have hγ := (component_iff F ζ hζ U c γ).mpr ⟨ε,u,hc⟩
        apply Quotient.sound
        apply MulAction.orbitRel_apply.mpr
        apply MulAction.mem_orbit_iff.mpr
        refine ⟨(⟨γ,hγ⟩ : Component F ζ hζ U c)⁻¹, ?_⟩
        change γ⁻¹ • y = x
        change y = γ • x at hy
        rw [hy, inv_smul_smul]
  let f : (Σ i : Fin n, KPCuspSiegel.OrbitQuotient F (Component F ζ hζ U (g i))) →
      Quotient s := fun p => ι (g p.1) p.2
  have hfi : Function.Injective f := by
    rintro ⟨i,x⟩ ⟨j,y⟩ he
    have hij : i = j := by
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y =>
          change ι (g i) (KPCuspSiegel.projection F _ x) =
            ι (g j) (KPCuspSiegel.projection F _ y) at he
          rw [hι, hι] at he
          apply r.injective
          rw [← hg i, ← hg j]
          exact hbase (Quotient.exact he)
    subst j
    have hxy : x = y := hinj (g i) he
    subst y
    rfl
  have hfs : Function.Surjective f := by
    intro z
    induction z using Quotient.inductionOn with
    | h p =>
      obtain ⟨i, hi⟩ := r.surjective (DoubleCoset.mk D H (π p.2))
      have he : DoubleCoset.mk D H (π (g i)) = DoubleCoset.mk D H (π p.2) := by
        rw [hg i, hi]
      obtain ⟨a, ⟨γ,rfl⟩, b, ⟨u,hu,rfl⟩, hp⟩ := DoubleCoset.eq.mp he
      obtain ⟨ε,v,hv⟩ := (base_relation F ζ hζ U (g i) p.2 γ).mp ⟨⟨u,hu⟩,hp⟩
      refine ⟨⟨i,KPCuspSiegel.projection F _ (γ⁻¹ • p.1)⟩, ?_⟩
      change ι (g i) (KPCuspSiegel.projection F _ (γ⁻¹ • p.1)) = _
      rw [hι]
      apply Quotient.sound
      exact (hs _ _).mpr ⟨γ,ε,v,by simp,hv⟩
  have hfcont : Continuous f := by
    apply continuous_sigma
    intro i
    letI := MulAction.orbitRel (Component F ζ hζ U (g i)) (SymmetricSpace F)
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    have hh : (ι (g i)) ∘ Quotient.mk' =
        (fun x : SymmetricSpace F => Quotient.mk s (x,g i)) := by
      funext x
      exact hι (g i) x
    rw [hh]
    exact continuous_quotient_mk'.comp (continuous_id.prodMk continuous_const)
  have hfopen : IsOpenMap f := by
    apply isOpenMap_sigma.mpr
    intro i
    letI := MulAction.orbitRel (Component F ζ hζ U (g i)) (SymmetricSpace F)
    apply IsOpenMap.of_comp continuous_quotient_mk' Quotient.mk'_surjective
    have hh : (ι (g i)) ∘ Quotient.mk' =
        (fun x : SymmetricSpace F => Quotient.mk s (x,g i)) := by
      funext x
      exact hι (g i) x
    rw [hh]
    exact slice_open F ζ hζ U s hs (g i)
  exact ⟨n,hn,g,(Equiv.ofBijective f ⟨hfi,hfs⟩).toHomeomorphOfContinuousOpen hfcont hfopen,
    fun _ _ => rfl⟩

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end
end

section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

open KPCuspGenuineMonodromy

private theorem central_comm' (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (ε : rootsOfUnity 3 F)
    (c : FiniteCover F ζ hζ) : central F ζ hζ ε * c = c * central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ
      ⟨ε, rfl⟩) c).symm

private theorem component_of_compare (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (γ : KPCuspArithmetic.PGL2 F) (ε η : rootsOfUnity 3 F) (u v : U.toOpenSubgroup)
    (h : finiteRationalLift F ζ hζ γ * (central F ζ hζ ε * g * u) =
      central F ζ hζ η * g * v) : γ ∈ Component F ζ hζ U g := by
  have hc : ∀ δ, finiteBase F ζ hζ (central F ζ hζ δ) = 1 := by
    intro δ
    have : central F ζ hζ δ ∈ (finiteBase F ζ hζ).ker := by
      rw [← (finite_cover_exact F ζ hζ).2.1]
      exact ⟨δ, rfl⟩
    exact this
  have hp := congrArg (finiteBase F ζ hζ) h
  simp only [map_mul, hc, one_mul] at hp
  rw [← MonoidHom.comp_apply, (finite_cover_exact F ζ hζ).2.2.2.1] at hp
  change KPFiniteComponents.diagonal F γ ∈
    (U.toOpenSubgroup.toSubgroup.map (finiteBase F ζ hζ)).map
      (MulAut.conj (finiteBase F ζ hζ g)).toMonoidHom
  refine ⟨finiteBase F ζ hζ ((v : FiniteCover F ζ hζ) * u⁻¹),
    ⟨(v : FiniteCover F ζ hζ) * u⁻¹, U.toOpenSubgroup.mul_mem v.property
      (U.toOpenSubgroup.inv_mem u.property), rfl⟩, ?_⟩
  change finiteBase F ζ hζ g * finiteBase F ζ hζ ((v : FiniteCover F ζ hζ) * u⁻¹) *
    (finiteBase F ζ hζ g)⁻¹ = KPFiniteComponents.diagonal F γ
  rw [map_mul]
  change finiteBase F ζ hζ g * (finiteBase F ζ hζ v * finiteBase F ζ hζ (u : FiniteCover F ζ hζ)⁻¹) *
    (finiteBase F ζ hζ g)⁻¹ = KPFiniteComponents.diagonal F γ
  rw [map_inv]
  apply mul_right_cancel (b := finiteBase F ζ hζ g * finiteBase F ζ hζ u)
  calc
    _ = finiteBase F ζ hζ g * finiteBase F ζ hζ v := by group
    _ = _ := hp.symm

theorem finite_component_scalar_descent
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (s : Setoid (KPCuspGenuineMonodromy.SymmetricSpace F ×
      KPCuspGenuineMonodromy.FiniteCover F ζ hζ))
    (hs : ∀ p p', s.r p p' ↔ ∃ (γ : KPCuspArithmetic.PGL2 F)
      (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup),
      p'.1 = γ • p.1 ∧ p'.2 =
        KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ *
        KPCuspGenuineMonodromy.central F ζ hζ ε * p.2 * u)
    (n : ℕ) (g : Fin n → KPCuspGenuineMonodromy.FiniteCover F ζ hζ)
    (e : (Σ i : Fin n, KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (g i))) ≃ₜ Quotient s)
    (he : ∀ i x, e ⟨i, KPCuspSiegel.projection F _ x⟩ = Quotient.mk s (x,g i))
    (L : ∀ i, KPCuspGenuineMonodromy.LineOutput F ζ hζ U (g i))
    (S : Submodule ℂ (KPCuspGenuineMonodromy.SymmetricSpace F ×
      KPCuspGenuineMonodromy.FiniteCover F ζ hζ → ℂ))
    (hS : ∀ H, H ∈ S ↔
      (∀ x c (γ : KPCuspArithmetic.PGL2 F),
        H (γ • x, KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c) = H (x,c)) ∧
      (∀ x c (ε : rootsOfUnity 3 F),
        H (x, KPCuspGenuineMonodromy.central F ζ hζ ε * c) =
          (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * H (x,c)) ∧
      (∀ x c (u : U.toOpenSubgroup), H (x, c * u) = H (x,c))) :
    ∃ r : S ≃ₗ[ℂ] (∀ i : Fin n,
      KPCuspGenuineMonodromy.sections F ζ hζ U (g i) (L i).rho),
      ∀ H i x, (r H i).val x = H.val (x,g i) := by
  classical
  let R := fun (p : SymmetricSpace F × FiniteCover F ζ hζ) (i : Fin n)
    (x : SymmetricSpace F) (γ : KPCuspArithmetic.PGL2 F)
    (ε : rootsOfUnity 3 F) (u : U.toOpenSubgroup) =>
      p.1 = γ • x ∧ p.2 = finiteRationalLift F ζ hζ γ * (central F ζ hζ ε * g i * u)
  have hex : ∀ p, ∃ i x γ ε u, R p i x γ ε u := by
    intro p
    obtain ⟨⟨i, q⟩, hq⟩ := e.surjective (Quotient.mk s p)
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    change e ⟨i, KPCuspSiegel.projection F _ x⟩ = Quotient.mk s p at hq
    rw [he] at hq
    obtain ⟨γ, ε, u, hx, hc⟩ := (hs _ _).mp (Quotient.exact hq)
    exact ⟨i, x, γ, ε, u, hx, by simpa [mul_assoc] using hc⟩
  have hind : ∀ p i x γ ε u j y δ η v,
      R p i x γ ε u → R p j y δ η v → i = j := by
    intro p i x γ ε u j y δ η v hi hj
    have hqi : e ⟨i, KPCuspSiegel.projection F _ x⟩ = Quotient.mk s p := by
      rw [he]
      apply Quotient.sound
      apply (hs _ _).mpr
      exact ⟨γ, ε, u, hi.1, by simpa [mul_assoc] using hi.2⟩
    have hqj : e ⟨j, KPCuspSiegel.projection F _ y⟩ = Quotient.mk s p := by
      rw [he]
      apply Quotient.sound
      apply (hs _ _).mpr
      exact ⟨δ, η, v, hj.1, by simpa [mul_assoc] using hj.2⟩
    exact congrArg Sigma.fst (e.injective (hqi.trans hqj.symm))
  have hvalue : ∀ p i x γ ε u y δ η v
      (A : automorphicScalars F ζ hζ U (g i)),
      R p i x γ ε u → R p i y δ η v →
      A.val (x, central F ζ hζ ε * g i * u) =
        A.val (y, central F ζ hζ η * g i * v) := by
    intro p i x γ ε u y δ η v A hi hj
    have hc : finiteRationalLift F ζ hζ (δ⁻¹ * γ) *
        (central F ζ hζ ε * g i * u) = central F ζ hζ η * g i * v := by
      rw [map_mul, map_inv, mul_assoc, ← hi.2, hj.2]
      group
    let k : Component F ζ hζ U (g i) :=
      ⟨δ⁻¹ * γ, component_of_compare F ζ hζ U (g i) _ ε η u v hc⟩
    have hx : (k : KPCuspArithmetic.PGL2 F) • x = y := by
      change (δ⁻¹ * γ) • x = y
      rw [mul_smul, ← hi.1, hj.1, inv_smul_smul]
    have hv := A.property.2.2.2 k x (central F ζ hζ ε * g i * u)
    rw [hx, hc] at hv
    exact hv.symm
  let ri := fun p => (hex p).choose
  let rx := fun p => (hex p).choose_spec.choose
  let rg := fun p => (hex p).choose_spec.choose_spec.choose
  let re := fun p => (hex p).choose_spec.choose_spec.choose_spec.choose
  let ru := fun p => (hex p).choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hr : ∀ p, R p (ri p) (rx p) (rg p) (re p) (ru p) := fun p =>
    (hex p).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  let V := ∀ i : Fin n, sections F ζ hζ U (g i) (L i).rho
  let a : V → ∀ i, automorphicScalars F ζ hζ U (g i) := fun f i =>
    (sectionEquiv F ζ hζ U (g i) (L i).rho (L i).finite_comparison).symm (f i)
  have ha : ∀ f i x, (a f i).val (x,g i) = (f i).val x := by
    intro f i x
    exact congrArg (fun t : sections F ζ hζ U (g i) (L i).rho => t.val x)
      ((sectionEquiv F ζ hζ U (g i) (L i).rho (L i).finite_comparison).apply_symm_apply (f i))
  let E : V → (SymmetricSpace F × FiniteCover F ζ hζ → ℂ) := fun f p =>
    (a f (ri p)).val (rx p, central F ζ hζ (re p) * g (ri p) * ru p)
  have hE : ∀ f p i x γ ε u, R p i x γ ε u →
      E f p = (a f i).val (x, central F ζ hζ ε * g i * u) := by
    intro f p i x γ ε u hp
    have hi := hind p (ri p) (rx p) (rg p) (re p) (ru p) i x γ ε u (hr p) hp
    have hrp := hr p
    dsimp only [E]
    rw [hi] at hrp ⊢
    exact hvalue p i (rx p) (rg p) (re p) (ru p) x γ ε u (a f i) hrp hp
  have hEmem : ∀ f : V, E f ∈ S := by
    intro f
    apply (hS _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro x c γ
      obtain ⟨i, y, δ, ε, u, hp⟩ := hex (x,c)
      dsimp only [R, Prod.fst, Prod.snd] at hp
      rw [hE f (x,c) i y δ ε u hp]
      apply hE f _ i y (γ * δ) ε u
      exact ⟨by change γ • x = (γ * δ) • y; rw [hp.1, mul_smul],
        by simp only [Prod.snd]; rw [hp.2, map_mul]; simp only [mul_assoc]⟩
    · intro x c ε
      obtain ⟨i, y, δ, η, u, hp⟩ := hex (x,c)
      dsimp only [R, Prod.fst, Prod.snd] at hp
      have ht : R (x, central F ζ hζ ε * c) i y δ (ε * η) u := by
        refine ⟨hp.1, ?_⟩
        dsimp only [Prod.snd]
        rw [hp.2, map_mul]
        simp only [← mul_assoc]
        rw [central_comm' F ζ hζ ε (finiteRationalLift F ζ hζ δ)]
      rw [hE f _ i y δ (ε * η) u ht, hE f _ i y δ η u hp]
      rw [map_mul]
      have hv := (a f i).property.2.1 y (central F ζ hζ η * g i * u) ε
      simpa only [mul_assoc] using hv
    · intro x c u
      obtain ⟨i, y, δ, ε, v, hp⟩ := hex (x,c)
      dsimp only [R, Prod.fst, Prod.snd] at hp
      have ht : R (x, c * u) i y δ ε (v * u) := by
        refine ⟨hp.1, ?_⟩
        change c * (u : FiniteCover F ζ hζ) = finiteRationalLift F ζ hζ δ *
          (central F ζ hζ ε * g i * ((v : FiniteCover F ζ hζ) * u))
        rw [hp.2]
        simp only [mul_assoc]
      rw [hE f _ i y δ ε (v * u) ht, hE f _ i y δ ε v hp]
      have hv := (a f i).property.2.2.1 y (central F ζ hζ ε * g i * v) u
      change (a f i).val (y, central F ζ hζ ε * g i * ((v : FiniteCover F ζ hζ) * u)) = _
      simpa only [mul_assoc] using hv
  let T : S →ₗ[ℂ] V := {
    toFun := fun H i => ⟨fun x => H.val (x,g i), by
      have hH := (hS H.val).mp H.property
      refine ⟨?_, ?_⟩
      · intro x ε hε
        have hc := hH.2.1 x (g i) ε
        rw [central_comm' F ζ hζ ε (g i)] at hc
        exact hc.symm.trans (hH.2.2 x (g i) ⟨central F ζ hζ ε, hε⟩)
      · intro γ x
        obtain ⟨u, hu⟩ := (L i).finite_comparison γ
        have hv := hH.1 x (g i) γ
        rw [hu, hH.2.2, hH.2.1] at hv
        have hv' := congrArg (fun z : ℂ => (chi F ζ hζ ((L i).rho γ) : ℂ) * z) hv
        simpa [map_inv, mul_assoc] using hv'⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hTinj : Function.Injective T := by
    intro H J ht
    apply Subtype.ext
    funext p
    obtain ⟨i, x, γ, ε, u, hp⟩ := hex p
    have hH := (hS H.val).mp H.property
    have hJ := (hS J.val).mp J.property
    rcases p with ⟨y,c⟩
    dsimp only [R, Prod.fst, Prod.snd] at hp
    rw [hp.1, hp.2, hH.1, hJ.1, hH.2.2, hJ.2.2, hH.2.1, hJ.2.1]
    exact congrArg ((chi F ζ hζ ε : ℂ) * ·)
      (congrArg (fun f : V => (f i).val x) ht)
  have hTsurj : Function.Surjective T := by
    intro f
    refine ⟨⟨E f, hEmem f⟩, ?_⟩
    funext i
    apply Subtype.ext
    funext x
    change E f (x,g i) = (f i).val x
    have hp : R (x,g i) i x 1 1 1 := by simp [R]
    rw [hE f _ i x 1 1 1 hp]
    simpa using ha f i x
  exact ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, fun H i x => rfl⟩

end DedekindZetaZeroFree.KPFiniteAdelicCuspEnds

end
end

section

noncomputable section
open scoped Classical NumberField
open MeasureTheory

namespace DedekindZetaZeroFree
namespace KPFiniteCuspAtlas

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def genuineScalars (U : CompactOpenLevel (FiniteCover F ζ hζ)) :
    Submodule ℂ (SymmetricSpace F × FiniteCover F ζ hζ → ℂ) where
  carrier := {H |
    (∀ x c (γ : KPCuspArithmetic.PGL2 F),
      H (γ • x, KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ * c) = H (x,c)) ∧
    (∀ x c (ε : rootsOfUnity 3 F),
      H (x, KPCuspGenuineMonodromy.central F ζ hζ ε * c) =
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * H (x,c)) ∧
    (∀ x c (u : U.toOpenSubgroup), H (x,c * u) = H (x,c))}
  zero_mem' := ⟨by intro x c γ; simp, by intro x c ε; simp,
    by intro x c u; simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x c γ; simp only [Pi.add_apply]; rw [hf1 x c γ, hg1 x c γ]
    · intro x c ε; simp only [Pi.add_apply]; rw [hf2 x c ε, hg2 x c ε, mul_add]
    · intro x c u; simp only [Pi.add_apply]; rw [hf3 x c u, hg3 x c u]
  smul_mem' := by
    rintro a f ⟨hf1, hf2, hf3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x c γ; simp only [Pi.smul_apply]; rw [hf1 x c γ]
    · intro x c ε; simp only [Pi.smul_apply, smul_eq_mul]; rw [hf2 x c ε]; ring
    · intro x c u; simp only [Pi.smul_apply]; rw [hf3 x c u]

def componentMap (U : CompactOpenLevel (FiniteCover F ζ hζ))
    (g : FiniteCover F ζ hζ) :
    KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U g) →
      rawXU F ζ hζ U :=
  Quotient.lift (fun x => Quotient.mk _ (x,g)) (by
    intro x y h
    obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    obtain ⟨ε, u, hu⟩ := KPCuspGenuineMonodromy.finiteComparison_exists F ζ hζ U g γ
    apply Eq.symm
    apply Quotient.sound
    refine ⟨γ, ε⁻¹, u⁻¹, hγ.symm, ?_⟩
    change g = _
    rw [← central_comm F ζ hζ ε⁻¹
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ)]
    rw [mul_assoc (KPCuspGenuineMonodromy.central F ζ hζ ε⁻¹)
      (KPCuspGenuineMonodromy.finiteRationalLift F ζ hζ γ) g, hu]
    simp [map_inv, mul_assoc])

def endSet (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    Set (KPCuspSiegel.OrbitQuotient F Γ) :=
  KPCuspSiegel.projection F Γ '' KPCuspSiegel.highCusp F σ T

def endMap (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    KPCuspCharts.HighQuotient F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ) T →
        KPCuspSiegel.OrbitQuotient F Γ :=
  Quotient.lift (fun p => KPCuspSiegel.projection F Γ
    (KPCuspSiegel.action F σ (KPCuspCharts.toArch F p.val))) (by
    intro p p' h
    obtain ⟨s, hs⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨KPCuspGenuineMonodromy.cuspInclusion F Γ q σ s, ?_⟩
    change (KPCuspGenuineMonodromy.cuspInclusion F Γ q σ s :
      KPCuspArithmetic.PGL2 F) • (σ • KPCuspCharts.toArch F p'.val) =
        σ • KPCuspCharts.toArch F p.val
    rw [KPCuspGenuineMonodromy.cuspInclusion_formula]
    simp only [mul_smul, inv_smul_smul]
    exact congrArg (fun z => σ • z) hs)

theorem endMap_range (hd : 0 < KPCuspLogShape.dimension F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) (T : ℝ) :
    Set.range (endMap F Γ q σ T) = endSet F Γ σ T := by
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    induction p using Quotient.inductionOn with
    | h p =>
      refine ⟨σ • KPCuspCharts.toArch F p.val, ?_, rfl⟩
      refine ⟨KPCuspCharts.toArch F p.val, ?_, rfl⟩
      change T < KPCuspLogShape.meanHeight _ (KPCuspCharts.toArch F p.val)
      rw [KPCuspCharts.toArch_meanHeight F hd]
      exact p.property
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    let p := (KPCuspCharts.toArchHomeomorph F hd).symm y
    have hp : KPCuspCharts.toArch F p = y :=
      (KPCuspCharts.toArchHomeomorph F hd).apply_symm_apply y
    have ht : T < p.2 := by
      rw [← KPCuspCharts.toArch_meanHeight F hd p, hp]
      exact hy
    refine ⟨Quotient.mk _ (⟨p, ht⟩ : {p : KPCuspCharts.Coordinates F // T < p.2}), ?_⟩
    change KPCuspSiegel.projection F Γ (σ • KPCuspCharts.toArch F p) = _
    rw [hp]
    rfl

def quotientVolume (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (A : Set (SymmetricSpace F)) : Measure (KPCuspSiegel.OrbitQuotient F Γ) :=
  Measure.map (KPCuspSiegel.projection F Γ)
    ((KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict A)

structure ComponentAtlas
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g) where
  cuspCount : ℕ
  positive_cuspCount : 0 < cuspCount
  cusp : Fin cuspCount → KPCuspArithmetic.Cusp F
  representative : Fin cuspCount → KPCuspArithmetic.PGL2 F
  representative_formula : ∀ a, representative a • KPCuspArithmetic.infinity F = cusp a
  exhaustive : ∀ q : KPCuspArithmetic.Cusp F,
    ∃ (a : Fin cuspCount) (γ : KPCuspGenuineMonodromy.Component F ζ hζ U g),
      γ • cusp a = q
  inequivalent : ∀ (a b : Fin cuspCount), a ≠ b →
    ∀ γ : KPCuspGenuineMonodromy.Component F ζ hζ U g, γ • cusp a ≠ cusp b
  threshold : ℝ
  parabolic : ∀ a, KPCuspCharts.ParabolicData F
    (KPCuspArithmetic.conjugatedStabilizer F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a))
  geometry : ∀ a, KPCuspCharts.ChartOutput F hF _ (parabolic a)
  monodromy : ∀ a, KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ)
    _ (parabolic a)
    (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
  frequencies : ∀ a, KPCuspFrequencyGap.CuspOutput (ζ := ζ) (hζ := hζ)
    _ (parabolic a)
    (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
      (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) (monodromy a)
  boundedShapes : Fin cuspCount → Set (KPCuspCharts.Shape F)
  compact_boundedShapes : ∀ a, IsCompact (boundedShapes a)
  shapes_cover : ∀ a (b : KPCuspCharts.Shape F), ∃ b' ∈ boundedShapes a,
    (QuotientAddGroup.mk b : KPCuspCharts.Base F hF
      (parabolic a).E (parabolic a).integralUnits) = QuotientAddGroup.mk b'

  frequencyGap : ℝ
  positive_frequencyGap : 0 < frequencyGap
  shortest_frequency : ∀ a (b : KPCuspCharts.Shape F), b ∈ boundedShapes a →
    ∀ ξ : KPCuspFrequencyGap.Frequency _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a))),
    (ξ : KPCuspFrequencyGap.Euclidean (KPCuspLogShape.dimension F)) ≠ 0 →
      frequencyGap ≤ KPCuspFrequencyGap.shapeEnergy b ξ

  constant_rank : ∀ a, Module.finrank ℂ
    (KPCuspFrequencyGap.constantSections (ζ := ζ) (hζ := hζ) _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)) ≤ 1
  constant_finite : ∀ a, FiniteDimensional ℂ
    (KPCuspFrequencyGap.constantSections (ζ := ζ) (hζ := hζ) _ (parabolic a)
      (line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F
        (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a)))
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U))
  open_ends : ∀ a, IsOpen (endSet F
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)
  disjoint_ends : Pairwise fun a b : Fin cuspCount => Disjoint
    (endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)
    (endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative b) threshold)
  compact_core : IsCompact ((Set.univ :
    Set (KPCuspSiegel.OrbitQuotient F (KPCuspGenuineMonodromy.Component F ζ hζ U g))) \
      (⋃ a, endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U g)
        (representative a) threshold))
  end_embedding : ∀ a, Topology.IsEmbedding (endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a) threshold)
  end_range : ∀ a, Set.range (endMap F
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) (cusp a) (representative a) threshold) =
      endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold
  fundamentalDomain : Set (SymmetricSpace F)
  measurable_fundamentalDomain : MeasurableSet fundamentalDomain
  isFundamentalDomain : IsFundamentalDomain
    (KPCuspGenuineMonodromy.Component F ζ hζ U g) fundamentalDomain
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))

  end_volume : ∀ a,
    Measure.map (endMap F (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      (cusp a) (representative a) threshold)
      (Measure.map ((geometry a).highPresentation threshold)
        ((geometry a).sectionMeasure.prod
          (Measure.comap (Subtype.val : Set.Ioi threshold → ℝ)
            (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))))) =
    (quotientVolume F (KPCuspGenuineMonodromy.Component F ζ hζ U g)
      fundamentalDomain).restrict
      (endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U g) (representative a) threshold)

structure Atlas (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) where
  componentCount : ℕ
  positive_componentCount : 0 < componentCount
  representative : Fin componentCount → FiniteCover F ζ hζ
  components : (Σ i : Fin componentCount,
    KPCuspSiegel.OrbitQuotient F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (representative i))) ≃ₜ rawXU F ζ hζ U
  components_formula : ∀ i x, components ⟨i,x⟩ = componentMap F ζ hζ U (representative i) x
  line : ∀ i, KPCuspGenuineMonodromy.LineOutput F ζ hζ U (representative i)
  scalar_realization : genuineScalars F ζ hζ U ≃ₗ[ℂ]
    (∀ i : Fin componentCount, KPCuspGenuineMonodromy.sections F ζ hζ U
      (representative i) (line i).rho)
  scalar_realization_formula : ∀ H i x,
    (scalar_realization H i).val x = H.val (x, representative i)
  cuspAtlas : ∀ i, ComponentAtlas F ζ hζ hF U (representative i) (line i)

  threshold : ℝ
  common_threshold : ∀ i, (cuspAtlas i).threshold = threshold

  compact_core : IsCompact ((Set.univ : Set (rawXU F ζ hζ U)) \
    (⋃ i : Fin componentCount, ⋃ a : Fin (cuspAtlas i).cuspCount,
      componentMap F ζ hζ U (representative i) ''
        endSet F (KPCuspGenuineMonodromy.Component F ζ hζ U (representative i))
          ((cuspAtlas i).representative a) threshold))

  norm_transitions : ∀ i (b : SymmetricSpace F → rootsOfUnity 3 F),
    IsLocallyConstant b → ∀ (γ : KPCuspGenuineMonodromy.Component F ζ hζ U (representative i))
      (x : SymmetricSpace F) (a : ℂ),
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ
      (KPCuspGenuineMonodromy.chartMultiplier F ζ hζ U (representative i)
        (line i).rho b γ x) : ℂ) * a‖ = ‖a‖

private def componentAtlasOfEndData
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : CompactOpenLevel (FiniteCover F ζ hζ)) (g : FiniteCover F ζ hζ)
    (line : KPCuspGenuineMonodromy.LineOutput F ζ hζ U g)
    (D : KPFiniteAdelicCuspEnds.ComponentEndData F ζ hζ hF U g line
      (endSet F) (endMap F) (quotientVolume F)) :
    ComponentAtlas F ζ hζ hF U g line where
  cuspCount := D.cuspCount
  positive_cuspCount := D.positive_cuspCount
  cusp := D.cusp
  representative := D.representative
  representative_formula := D.representative_formula
  exhaustive := D.exhaustive
  inequivalent := D.inequivalent
  threshold := D.threshold
  parabolic := D.parabolic
  geometry := D.geometry
  monodromy := D.monodromy
  frequencies := D.frequencies
  boundedShapes := D.boundedShapes
  compact_boundedShapes := D.compact_boundedShapes
  shapes_cover := D.shapes_cover
  frequencyGap := D.frequencyGap
  positive_frequencyGap := D.positive_frequencyGap
  shortest_frequency := D.shortest_frequency
  constant_rank := D.constant_rank
  constant_finite := D.constant_finite
  open_ends := D.open_ends
  disjoint_ends := D.disjoint_ends
  compact_core := D.compact_core
  end_embedding := D.end_embedding
  end_range := D.end_range
  fundamentalDomain := D.fundamentalDomain
  measurable_fundamentalDomain := D.measurable_fundamentalDomain
  isFundamentalDomain := D.isFundamentalDomain
  end_volume := D.end_volume

end KPFiniteCuspAtlas

set_option maxHeartbeats 800000 in

theorem kp_cont_finite_cusp_atlas
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)) :
    ∃ hF : NumberField.InfinitePlace.nrRealPlaces F = 0,
      KPCuspLogShape.dimension F = Module.finrank ℚ F / 2 ∧
      Nonempty (KPFiniteCuspAtlas.Atlas F ζ hζ hF U) := by
  letI := primitive12_totallyComplex F ζ hζ
  refine ⟨NumberField.IsTotallyComplex.nrRealPlaces_eq_zero F,
    ?_, ?_⟩
  · change NumberField.InfinitePlace.nrComplexPlaces F = Module.finrank ℚ F / 2
    rw [NumberField.IsTotallyComplex.finrank]
    omega
  · let hF := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero F
    obtain ⟨n, hn, g, e, he⟩ :=
      KPFiniteAdelicCuspEnds.finite_spherical_components F ζ hζ U
        (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (fun _ _ => Iff.rfl)
        (KPFiniteCuspAtlas.componentMap F ζ hζ U) (fun _ _ => rfl)
    let L : ∀ i : Fin n, KPCuspGenuineMonodromy.LineOutput F ζ hζ U (g i) :=
      fun i => Classical.choice (KPCuspGenuineMonodromy.lineOutput_exists F ζ hζ U (g i))
    obtain ⟨r, hr⟩ := KPFiniteAdelicCuspEnds.finite_component_scalar_descent F ζ hζ U
      (KPFiniteCuspAtlas.sphericalRelation F ζ hζ U) (fun _ _ => Iff.rfl)
      n g e (fun i x => he i (KPCuspSiegel.projection F _ x)) L
      (KPFiniteCuspAtlas.genuineScalars F ζ hζ U) (fun _ => Iff.rfl)
    have hdata := fun i : Fin n =>
      KPFiniteAdelicCuspEnds.component_ends_exist F ζ hζ hF U (g i) (L i)
        (KPFiniteCuspAtlas.endSet F) (KPFiniteCuspAtlas.endMap F)
        (KPFiniteCuspAtlas.quotientVolume F)
        (fun _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl)
    choose T₀ hT₀ using hdata
    obtain ⟨T, hT⟩ := Finite.exists_le T₀
    choose D hD using fun i : Fin n => hT₀ i T (hT i)
    let A : ∀ i : Fin n, KPFiniteCuspAtlas.ComponentAtlas F ζ hζ hF U (g i) (L i) :=
      fun i => KPFiniteCuspAtlas.componentAtlasOfEndData F ζ hζ hF U (g i) (L i) (D i)
    have hA : ∀ i, (A i).threshold = T := hD
    refine ⟨{
      componentCount := n
      positive_componentCount := hn
      representative := g
      components := e
      components_formula := he
      line := L
      scalar_realization := r
      scalar_realization_formula := hr
      cuspAtlas := A
      threshold := T
      common_threshold := hA
      compact_core := ?_
      norm_transitions := ?_ }⟩
    · apply KPFiniteAdelicCuspEnds.compact_core_of_finite_components e
        (fun i => KPFiniteCuspAtlas.componentMap F ζ hζ U (g i)) he
        (fun i => Fin (A i).cuspCount)
        (fun i a => KPFiniteCuspAtlas.endSet F
          (KPCuspGenuineMonodromy.Component F ζ hζ U (g i)) ((A i).representative a) T)
      intro i
      rw [← hA i]
      exact (A i).compact_core
    · intro i b hb γ x a
      rw [norm_mul, (L i).unitary, one_mul]

end DedekindZetaZeroFree

end
end
