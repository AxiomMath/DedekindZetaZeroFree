module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.SphericalCoefficientSupport
public import DedekindZetaZeroFree.Metaplectic.Intertwining.CompactOrbits.FiniteDimensionality

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

namespace UniformCompactSeparation

 def pointEvaluation {X : Type*} (S : Submodule ℂ (X → ℂ)) (x : X) :
    Module.Dual ℂ S := (LinearMap.proj x).comp S.subtype

private theorem finite_evaluation_dual_span {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (m : ℕ) (x : Fin m → X),
      Submodule.span ℂ (Set.range (fun i => pointEvaluation S (x i))) = ⊤ := by
  have htop : Submodule.span ℂ (Set.range (pointEvaluation S)) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro h hh
    have hx : ∃ x, h.val x ≠ 0 := by
      by_contra! hn
      apply hh
      apply Subtype.ext
      funext x
      exact hn x
    obtain ⟨x, hx⟩ := hx
    exact ⟨pointEvaluation S x, ⟨x, rfl⟩, hx⟩
  have hfg : (Submodule.span ℂ (Set.range (pointEvaluation S))).FG := by
    rw [htop]
    exact Module.Finite.fg_top
  obtain ⟨s, hs, he⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hfg
  have hx : ∀ e : s, ∃ x, pointEvaluation S x = e.val := by
    intro e
    exact hs e.property
  choose x hx using hx
  let E := Fintype.equivFin s
  refine ⟨Fintype.card s, fun i => x (E.symm i), ?_⟩
  have hr : Set.range (fun i => pointEvaluation S (x (E.symm i))) = (s : Set (Module.Dual ℂ S)) := by
    ext e
    constructor
    · rintro ⟨i, rfl⟩
      dsimp only
      rw [hx]
      exact (E.symm i).property
    · intro he
      refine ⟨E ⟨e, he⟩, ?_⟩
      simp only [Equiv.symm_apply_apply]
      exact hx ⟨e, he⟩
  rw [hr, ← he, htop]

theorem finite_evaluation_reconstruction {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (n m : ℕ) (x : Fin m → X) (A : Fin n → Fin m → ℂ)
      (b : Fin n → S),
      ∀ (h : S) (y : X), h.val y = ∑ j, (∑ i, A j i * h.val (x i)) * (b j).val y := by
  obtain ⟨m, x, hx⟩ := finite_evaluation_dual_span S
  let b := Module.finBasis ℂ S
  have hc : ∀ j, ∃ A : Fin m → ℂ,
      ∑ i, A i • pointEvaluation S (x i) = b.coord j := by
    intro j
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mp
    rw [hx]
    exact Submodule.mem_top
  choose A hA using hc
  refine ⟨Module.finrank ℂ S, m, x, A, b, ?_⟩
  intro h y
  have hr := congrArg (fun z : S => z.val y) (b.sum_repr h)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul] at hr
  rw [← hr]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have he := congrArg (fun e : Module.Dual ℂ S => e h) (hA j)
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    pointEvaluation, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, Module.Basis.coord_apply] using he.symm

private theorem finite_evaluation_interpolation {X : Type*}
    (S : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ S] :
    ∃ (m : ℕ) (x : Fin m → X) (B : Fin m → X → ℂ),
      ∀ (h : S) (y : X), h.val y = ∑ i, B i y * h.val (x i) := by
  obtain ⟨n, m, x, A, b, hb⟩ := finite_evaluation_reconstruction S
  refine ⟨m, x, fun i y => ∑ j, A j i * (b j).val y, ?_⟩
  intro h y
  rw [hb]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))

def actualCompactTranslateSpace : Submodule ℂ (KPContSectorArchSphericalFibers.KInfinity F → ℂ) :=
  Submodule.span ℂ (Set.range (fun p :
    KPGlobalTorusFunctionData.finitePart F ζ hζ × KPContSectorArchSphericalFibers.KInfinity F =>
    fun k : KPContSectorArchSphericalFibers.KInfinity F =>
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * p.2).val * p.1.val)))

private theorem insertion_commutes_finite
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    Commute (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a) c.val := by
  apply DedekindZetaZeroFree.RepresentationTheory.ArchFiniteSplitting.insertion_commutes_finite
    F ζ hζ a ⟨c.val, ?_⟩
  obtain ⟨x, hx, he⟩ := c.property
  exact Subgroup.mem_map.mpr ⟨x, fun w => Subgroup.mem_iInf.mp hx w, he⟩

theorem actualCompactTranslateSpace_finiteDimensional :
    FiniteDimensional ℂ (actualCompactTranslateSpace F ζ hζ t) := by
  let O := Submodule.span ℂ (Set.range (fun u : (KPContFlatSourceRecipe.D F ζ hζ).K =>
    fun g => t.val.val (g * u.val)))
  letI : FiniteDimensional ℂ O :=
    KPGlobalResidualKernel.ScatteringResidue.source_raw_compact_orbit_finiteDimensional_public t
  obtain ⟨m, x, B, hB⟩ := finite_evaluation_interpolation O
  let L : (Fin m → O) →ₗ[ℂ] (KPContSectorArchSphericalFibers.KInfinity F → ℂ) :=
    { toFun := fun q k => ∑ i, (q i).val
        (x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val)
      map_add' := by intros; ext k; simp [Finset.sum_add_distrib]
      map_smul' := by intros; ext k; simp [Finset.mul_sum] }
  have hle : actualCompactTranslateSpace F ζ hζ t ≤ L.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨c, u⟩, rfl⟩
    let tu : O := ⟨fun g => t.val.val
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val),
      Submodule.subset_span ⟨⟨_,
        KPContinuation.ArchCompact.archimedeanInsertion_mem_iwasawaCompact F ζ hζ u⟩, rfl⟩⟩
    refine ⟨fun i => B i c.val • tu, ?_⟩
    funext k
    let v : O := ⟨fun g => t.val.val
      (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val),
      Submodule.subset_span ⟨⟨_,
        KPContinuation.ArchCompact.archimedeanInsertion_mem_iwasawaCompact F ζ hζ (k * u)⟩, rfl⟩⟩
    have hv := hB v c.val
    have hi := (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1 k.val u.val
    have hc := insertion_commutes_finite F ζ hζ (k * u).val c
    change (∑ i, B i c.val * t.val.val
      ((x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val)) = _
    have he : KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val =
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val := hi
    change (∑ i, B i c.val * t.val.val
      ((x i * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ k.val) *
        KPSmoothActualFlowData.archimedeanInsertion F ζ hζ u.val)) =
      t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (k * u).val * c.val)
    rw [hc.eq]
    simpa only [v, he, mul_assoc] using hv.symm
  exact Submodule.finiteDimensional_of_le hle

theorem actualCompactTranslateSpace_right_invariant
    (h : actualCompactTranslateSpace F ζ hζ t)
    (u : KPContSectorArchSphericalFibers.KInfinity F) :
    (fun k => h.val (k * u)) ∈ actualCompactTranslateSpace F ζ hζ t := by
  refine Submodule.span_induction (p := fun f _ =>
    (fun k => f (k * u)) ∈ actualCompactTranslateSpace F ζ hζ t) ?_ ?_ ?_ ?_ h.property
  · rintro f ⟨⟨c, v⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨(c, u * v), ?_⟩
    funext k
    simp only [mul_assoc]
  · exact Submodule.zero_mem _
  · intro f g hf hg htf htg
    exact Submodule.add_mem _ htf htg
  · intro a f hf htf
    exact Submodule.smul_mem _ a htf

theorem actual_source_uniform_compact_evaluation_reconstruction :
    ∃ (n m : ℕ) (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
      (A : Fin n → Fin m → ℂ)
      (b : Fin n → actualCompactTranslateSpace F ζ hζ t),
      ∀ (a : KPContSectorArchSphericalFibers.KInfinity F)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val * c.val) =
          ∑ j, evalCoefficient F ζ hζ t k (A j) c * (b j).val a := by
  let S := actualCompactTranslateSpace F ζ hζ t
  letI : FiniteDimensional ℂ S := actualCompactTranslateSpace_finiteDimensional F ζ hζ t
  obtain ⟨n, m, k, A, b, hb⟩ := finite_evaluation_reconstruction S
  refine ⟨n, m, k, A, b, ?_⟩
  intro a c
  have hh : (fun a : KPContSectorArchSphericalFibers.KInfinity F => t.val.val
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val * c.val)) ∈ S := by
    exact Submodule.subset_span ⟨(c, 1), by simp⟩
  exact hb ⟨_, hh⟩ a

end UniformCompactSeparation

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

end
