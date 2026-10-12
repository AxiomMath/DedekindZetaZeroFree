module

public import DedekindZetaZeroFree.Metaplectic.Torus.Charts.WeightedJetEstimates

@[expose] public section

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem exists_conjugate_finite_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ t : KPGlobalTorusFunctionData.globalLevel F ζ hζ U,
        g⁻¹ * t.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
  have hn : (KPGlobalTorusFunctionData.finitePart F ζ hζ).Normal := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.finiteSubgroup_normal F ζ hζ
  let e : KPGlobalTorusFunctionData.finitePart F ζ hζ ≃ₜ*
      KPGlobalTorusFunctionData.finitePart F ζ hζ :=
    { toFun := fun u => ⟨g⁻¹ * u.val * g, by
        simpa only [inv_inv, mul_assoc] using hn.conj_mem u.val u.property g⁻¹⟩
      invFun := fun u => ⟨g * u.val * g⁻¹, hn.conj_mem u.val u.property g⟩
      left_inv := by intro u; apply Subtype.ext; dsimp; group
      right_inv := by intro u; apply Subtype.ext; dsimp; group
      map_mul' := by intro u v; apply Subtype.ext; dsimp; group
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ :=
    ⟨J.toOpenSubgroup.comap e.toMonoidHom e.continuous,
      e.toHomeomorph.isCompact_preimage.mpr J.isCompact⟩
  refine ⟨U, ?_⟩
  intro t
  obtain ⟨u, hu, he⟩ := t.property
  refine ⟨e u, hu, ?_⟩
  change g⁻¹ * u.val * g = g⁻¹ * t.val * g
  change u.val = t.val at he
  rw [he]

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

private theorem ordinaryTorus_isClosed :
    IsClosed (KPGlobalTorusFunctionData.ordinaryTorus F :
      Set (KPAdelicCoverRestrictedProduct.AdelicPGL2 F)) := by
  let q := QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
  apply (QuotientGroup.isQuotientMap_mk
    (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).isClosed_preimage.mp
  have he : q ⁻¹' (KPGlobalTorusFunctionData.ordinaryTorus F : Set _) =
      {A : KPGlobalTorusFunctionData.AdelicMatrixGroup F | A 1 0 = 0 ∧ A 0 1 = 0} := by
    ext A
    constructor
    · intro h
      obtain ⟨B, hB, h10, h01⟩ := h
      rw [QuotientGroup.mk'_eq_mk'] at hB
      obtain ⟨z, hz, he⟩ := hB
      obtain ⟨u, rfl⟩ := hz
      rw [← he]
      simp [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Matrix.scalar, Fin.sum_univ_two, h01, h10]
    · intro h
      exact ⟨A, rfl, h⟩
  change IsClosed (q ⁻¹' (KPGlobalTorusFunctionData.ordinaryTorus F : Set _))
  rw [he]
  have hc (i j : Fin 2) : Continuous
      (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val : Continuous
        (fun A : KPGlobalTorusFunctionData.AdelicMatrixGroup F => A.val)))
  exact (isClosed_eq (hc 1 0) continuous_const).inter
    (isClosed_eq (hc 0 1) continuous_const)

theorem actualTorus_isClosed :
    IsClosed ((KPGlobalTorusFunctionData.torus F ζ hζ) : Set (G F ζ hζ)) :=
  (ordinaryTorus_isClosed F).preimage
    (KPAdelicCoverRestrictedProduct.adelic_pgl_topological_cover F ζ hζ).2.2.2.continuous

theorem exists_compact_conjugate_torus_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      IsCompact (((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) : Set (E F ζ hζ)) ∧
      ∀ t : (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
          (KPGlobalTorusFunctionData.torus F ζ hζ).subtype,
        g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
  obtain ⟨U, hU⟩ := exists_conjugate_finite_level F ζ hζ J g
  refine ⟨U, ?_, ?_⟩
  · exact (actualTorus_isClosed F ζ hζ).isClosedEmbedding_subtypeVal.isCompact_preimage
      (globalLevel_isCompact F ζ hζ U)
  · intro t
    exact hU ⟨t.val.val, t.property⟩

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end

section

open scoped NumberField Classical NNReal BigOperators
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel
open KPGlobalTorusBorelNormTwistTransport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2000

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem fiber_rightAction_of_conjugate_mem (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (f : InducedLevel F ζ hζ P J) (g : G F ζ hζ) (t : E F ζ hζ)
    (hδ : KPGlobalTorusFunctionData.delta F ζ hζ t = 1)
    (ht : g⁻¹ * t.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J) :
    KPGlobalTorusPeriodizationInverse.rightAction F ζ hζ P t (f.val.val g) =
      f.val.val g := by
  have hc := f.val.property t 0 g
  have hn : KPGlobalTorusFunctionData.N F ζ hζ
      (0 : KPGlobalTorusFunctionData.Adeles F) = 1 :=
    (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
  have hhalf : KPGlobalTorusFunctionData.deltaHalf F ζ hζ t = 1 := by
    simp [KPGlobalTorusFunctionData.deltaHalf, hδ]
  have hm : t.val * g = g * (g⁻¹ * t.val * g) := by group
  simp only [hn, mul_one, hhalf, one_smul] at hc
  rw [hm, f.property.2 g ⟨_, ht⟩] at hc
  exact hc.symm

theorem chart_fiber_rightLevel_of_compact_conjugate (P : Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (g : G F ζ hζ) (H : Subgroup (E F ζ hζ))
    (hc : IsCompact (H : Set (E F ζ hζ)))
    (hfin : ∀ t : H, t.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (hconj : ∀ t : H,
      g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) :
    ∀ (t : H) (x : E F ζ hζ),
      (f.val.val (groupArchChart F ζ hζ z * g)).val.val (x * t.val) =
        (f.val.val (groupArchChart F ζ hζ z * g)).val.val x := by
  intro t x
  have hcomm := TorusChartTransport.groupArchChart_commutes_finite
    F ζ hζ t.val.val (hfin t) z
  have hm : (groupArchChart F ζ hζ z * g)⁻¹ * t.val.val *
      (groupArchChart F ζ hζ z * g) = g⁻¹ * t.val.val * g := by
    have he : t.val.val * groupArchChart F ζ hζ z =
        groupArchChart F ζ hζ z * t.val.val := hcomm.symm.eq
    calc
      _ = g⁻¹ * (groupArchChart F ζ hζ z)⁻¹ *
          (t.val.val * groupArchChart F ζ hζ z) * g := by group
      _ = _ := by rw [he]; group
  have hi := fiber_rightAction_of_conjugate_mem F ζ hζ P J f
    (groupArchChart F ζ hζ z * g) t.val
    (delta_compact_subgroup F ζ hζ H hc t) (hm ▸ hconj t)
  exact congrArg (fun v : Smooth F ζ hζ P => v.val.val x) hi

theorem chart_fiber_mem_torusSmoothLevel (P : Polarization F ζ hζ)
    (J U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ)
    (hc : IsCompact (((KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
      (KPGlobalTorusFunctionData.torus F ζ hζ).subtype) : Set (E F ζ hζ)))
    (hconj : ∀ t : (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype,
      g⁻¹ * t.val.val * g ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J)
    (f : InducedLevel F ζ hζ P J) (z : GroupArch F) :
    (f.val.val (groupArchChart F ζ hζ z * g)).val ∈
      KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P U := by
  constructor
  · have hle : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ P ≤
        KPGlobalTorusFunctionData.ArchSmooth P.H P.character.toMonoidHom
          (KPGlobalTorusFunctionData.torusArchChart F ζ hζ)
          (KPGlobalTorusFunctionData.torusArchDomain F) :=
      iSup_le fun _ => inf_le_left
    exact hle (f.val.val (groupArchChart F ζ hζ z * g)).property
  · intro t
    apply Subtype.ext
    funext x
    have hfin : ∀ t : (KPGlobalTorusFunctionData.globalLevel F ζ hζ U).comap
        (KPGlobalTorusFunctionData.torus F ζ hζ).subtype,
        t.val.val ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
      intro t
      rcases t.property with ⟨a, ha, he⟩
      change a.val = t.val.val at he
      rw [← he]
      exact a.property
    exact chart_fiber_rightLevel_of_compact_conjugate F ζ hζ P J g _ hc hfin hconj
      f z t x

theorem exists_uniform_chart_fiber_level
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) (g : G F ζ hζ) :
    ∃ U : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ,
      ∀ (P : Polarization F ζ hζ) (f : InducedLevel F ζ hζ P J) (z : GroupArch F),
        (f.val.val (groupArchChart F ζ hζ z * g)).val ∈
          KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ P U := by
  obtain ⟨U, hc, hconj⟩ := exists_compact_conjugate_torus_level F ζ hζ J g
  exact ⟨U, fun P f z =>
    chart_fiber_mem_torusSmoothLevel F ζ hζ P J U g hc hconj f z⟩

end
end DedekindZetaZeroFree.KPGlobalTorusBorelTwistCompatibilityBorelInduction.UniformFiberLevel

end
