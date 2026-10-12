module

public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.CotangentCutoffSupport
public import DedekindZetaZeroFree.Adeles.Quotients.GreenIdentities.ChartLocalization

@[expose] public section

noncomputable section
open scoped Classical NumberField
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorGlobalGreen

attribute [local instance 2000]
  KPContSectorQuotientRelationsComparison.instMeasurableSpaceRawXU

open KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies KPContActualCotangentChartRestriction

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

structure Properties : Prop where
  cotangent_pair_integrable : ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    Integrable (pair (D_U φ).val W.val) (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  scalar_pair_integrable : ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    Integrable (scalarPair φ (δ_U W)) (KPContActualSectorCotangentL2.muU F ζ hζ U R P)
  local_cotangent_pair_integrable : ∀ (a : ActualChart (U := U) (H := H))
      (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    Integrable (fun y => inner ℂ (localCoefficient a (D_U φ).val y)
      (localCoefficient a W.val y)) a.liftedMeasure
  local_scalar_pair_integrable : ∀ (a : ActualChart (U := U) (H := H))
      (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    Integrable (fun y => inner ℂ (localScalarCoefficient a φ y)
      (localScalarCoefficient a (δ_U W) y)) a.liftedMeasure
  green_integral : ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    (∫ x, pair (D_U φ).val W.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ x, scalarPair φ (δ_U W) x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P
  green : ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
    inner ℂ (j (D_U φ)) (j W) = inner ℂ (iota φ) (iota (δ_U W))
  iota_injective : Function.Injective (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
  j_injective : Function.Injective (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
  formal_adjoint : (KPTestOperator.descend (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
      (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) iota_injective
      (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) D_U).IsFormalAdjoint
    (KPTestOperator.descend (S := T_U F ζ hζ U R P H) (T := S_U F ζ hζ U R P H)
      (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) j_injective
      (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
      (δ_U (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)))
  laplacian_pairing : ∀ φ ψ : S_U F ζ hζ U R P H,
    inner ℂ (j (D_U φ)) (j (D_U ψ)) = inner ℂ (iota φ) (iota (δ_U (D_U ψ)))
  descended_laplacian_pairing : ∀ φ ψ : KPTestOperator.testDomain
      (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)),
    inner ℂ (KPTestOperator.descend (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
        iota iota_injective j D_U φ)
        (KPTestOperator.descend (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
          iota iota_injective j D_U ψ) =
      inner ℂ (φ : KPContSectorClosedLpSubspace.H F ζ hζ R U)
        (KPTestOperator.laplacian (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
          iota iota_injective D_U δ_U ψ)

end DedekindZetaZeroFree.KPContActualSectorGlobalGreen

namespace DedekindZetaZeroFree.KPContActualGlobalGreen
open KPContActualCotangentCountableShrinking KPContActualCotangentMeasurableFamilies
open KPContActualSectorTestDifferentialDescent KPContActualSectorSmoothTestModules
open KPContActualSectorTestEmbeddings KPContCotangentActualOverlap KPContCotangentOverlapRationalBranches
open KPContActualCotangentPieceHilbertSum
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
set_option maxHeartbeats 1000000 in
private theorem localized_green
    (emb : KPContActualSectorTestEmbeddings.Properties (U := U) (H := H))
    (dif : KPContActualSectorTestDifferentialDescent.Properties (U := U) (H := H))
    (a : ShrunkChart F ζ hζ U R P H) (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H)
    (η : RealSmoothCutoff F ζ hζ U R P H) (hηc : HasCompactSupport η.val)
    (hηs : tsupport η.val ⊆ a.baseDomain)
    (L : KPCuspGenuineMonodromy.SymmetricSpace F → ℝ) (hLs : tsupport L ⊆ a.domain)
    (hLq : ∀ x : omega a, L (labeledA (placeEquiv F ζ hζ) x.val) = η.val (q a x.val)) :
    (∫ x, pair (D_U φ).val (cotangentMultiply η W).val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      ∫ x, scalarPair φ (δ_U (cotangentMultiply η W)) x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  let Z := cotangentMultiply η W
  have hZs : cotangentSupport Z.val ⊆ tsupport η.val := cotangentMultiply_support η W
  have hcover : tsupport η.val ⊆ ⋃ _i : Fin 1, a.baseDomain := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0, hηs hx⟩
  obtain ⟨Q⟩ := kp_cont_actual_sector_finite_support_partition_in_charts F ζ hζ U R P H 1 (fun _ => a)
    (tsupport η.val) a.baseDomain hηc (every_shrunkChart_properties F ζ hζ U R P H a).base_open hηs hcover
  let θ : RealSmoothCutoff F ζ hζ U R P H := multiplierCutoff (Q.multiplier 0) (Q.smooth 0)
  let ψ := scalarMultiply θ φ
  have hθone : ∀ x ∈ Q.neighborhood, θ.val x = 1 := by
    intro x hx
    simpa [θ, multiplierCutoff, Fin.sum_univ_one] using Q.partition x hx
  have hθφ : tsupport (liftExtension a (ψ.val a)) ⊆ omega a := by
    have hs : Function.support (liftExtension a (ψ.val a)) ⊆
        labeledA (placeEquiv F ζ hζ) ⁻¹' tsupport (Q.lift 0) := by
      intro y hy
      have hym : y ∈ omega a := by
        by_contra hn
        exact hy (by simp [liftExtension, hn])
      have hc : θ.val (q a y) ≠ 0 := by
        intro hn
        apply hy
        simp [ψ, scalarMultiply, liftExtension, hym, cutoffLift, hn]
      apply subset_tsupport
      have hr := Q.lift_restriction 0 ⟨labeledA (placeEquiv F ζ hζ) y, hym⟩
      change Q.lift 0 (labeledA (placeEquiv F ζ hζ) y) = Q.multiplier 0 (q a y) at hr
      simpa [θ, multiplierCutoff, hr] using hc
    exact (closure_minimal hs ((isClosed_tsupport _).preimage continuous_labeledA_actual)).trans
      (fun y hy => Q.lift_support_subset 0 hy)
  have hZlift := liftExtension_cutoff_tsupport a η L hLs hLq W
  have hcompact (V : Type) [Zero V] (f : omega a → V) : HasCompactSupport (liftExtension a f) := by
    have hc : Continuous (labeledAInv (placeEquiv F ζ hζ)) := by
      apply (CotangentLogCoframe.A (d F)).symm.continuous.comp
      exact continuous_pi fun k => continuous_apply _
    have hK := a.closure_compact.image hc
    refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
    apply closure_minimal _ hK.isClosed
    intro y hy
    have hym : y ∈ omega a := by
      by_contra hn
      exact hy (by simp [liftExtension, hn])
    refine ⟨labeledA (placeEquiv F ζ hζ) y, subset_closure hym, ?_⟩
    simp [labeledA, labeledAInv]
  have hjSupport : tsupport (fun p : M F => (CotangentLogCoframe.j (d F)).symm
      (liftExtension a (coefficient Z.val a) p)) ⊆ omega a := by
    apply Set.Subset.trans _ hZlift
    apply closure_mono
    intro x hx hn
    apply hx
    change (CotangentLogCoframe.j (d F)).symm (liftExtension a (coefficient (cotangentMultiply η W).val a) x) = 0
    rw [hn, map_zero]
  have hgreen := local_chart_green a ψ Z (hcompact _ _) hθφ
    ((hcompact _ _).comp_left (g := (CotangentLogCoframe.j (d F)).symm) (map_zero _)) hjSupport
  have hqcont (b : ShrunkChart F ζ hζ U R P H) : Continuous (q b) := by
    exact continuous_quot_mk.comp (continuous_labeledA_actual.prodMk continuous_const)
  have hD (b : ShrunkChart F ζ hζ U R P H) (y : omega b)
      (hy : q b y.val ∈ tsupport η.val) : coefficient (D_U ψ).val b y = coefficient (D_U φ).val b y := by
    have he : liftExtension b (ψ.val b) =ᶠ[𝓝 y.val] liftExtension b (φ.val b) := by
      have hn : q b y.val ∈ Q.neighborhood := Q.contains_compact hy
      filter_upwards [(isOpen_omega_actual b).mem_nhds y.property,
        (hqcont b).continuousAt.preimage_mem_nhds (Q.neighborhood_open.mem_nhds hn)] with z hz hm
      simp [ψ, scalarMultiply, liftExtension, hz, cutoffLift, hθone (q b z) hm]
    rw [dif.differential_chart, dif.differential_chart]
    unfold chartDifferential HyperbolicChart.differential HyperbolicChart.coordinateDerivative
    simp only [he.fderiv_eq]
  have hleft : pair (D_U φ).val Z.val = pair (D_U ψ).val Z.val := by
    funext x
    obtain ⟨b,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    rw [pair_chart, pair_chart]
    by_cases hz : coefficient Z.val b y = 0
    · simp [hz]
    · have hs : q b y.val ∈ cotangentSupport Z.val := subset_closure ⟨b,y,rfl,hz⟩
      rw [hD b y (hZs hs)]
  have hright : scalarPair φ (δ_U Z) = scalarPair ψ (δ_U Z) := by
    funext x
    obtain ⟨b,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    rw [emb.scalar_pair_chart, emb.scalar_pair_chart]
    by_cases hz : (δ_U Z).val b y = 0
    · simp [hz]
    · have hs : q b y.val ∈ scalarSupport (δ_U Z).val := subset_closure ⟨b,y,rfl,hz⟩
      have hn := Q.contains_compact (hZs (dif.codifferential_support Z hs))
      have hψ : ψ.val b y = φ.val b y := by
        simp [ψ, scalarMultiply, cutoffLift, hθone _ hn]
      rw [hψ]
  have hpairzero : ∀ x, x ∉ a.baseDomain → pair (D_U ψ).val Z.val x = 0 := by
    intro x hx
    obtain ⟨b,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    rw [pair_chart]
    have hz : coefficient Z.val b y = 0 := by
      by_contra hn
      exact hx (hηs (hZs (subset_closure ⟨b,y,rfl,hn⟩)))
    simp [hz]
  have hscalarzero : ∀ x, x ∉ a.baseDomain → scalarPair ψ (δ_U Z) x = 0 := by
    intro x hx
    obtain ⟨b,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    rw [emb.scalar_pair_chart]
    have hz : (δ_U Z).val b y = 0 := by
      by_contra hn
      exact hx (hηs (hZs (dif.codifferential_support Z (subset_closure ⟨b,y,rfl,hn⟩))))
    simp [hz]
  rw [hleft, hright, ← setIntegral_eq_integral_of_forall_compl_eq_zero hpairzero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hscalarzero,
    emb.cotangent_chart_integral, emb.scalar_chart_integral]
  exact hgreen
end DedekindZetaZeroFree.KPContActualGlobalGreen

namespace DedekindZetaZeroFree

open KPContActualGlobalGreen KPContActualCotangentCountableShrinking
open KPContCotangentOverlapRationalBranches KPContCotangentActualOverlap
open scoped BigOperators

open KPContActualSectorSmoothTestModules
open KPContActualSectorTestDifferentialDescent KPContActualSectorTestEmbeddings
open KPContActualCotangentMeasurableFamilies KPContActualCotangentChartRestriction

set_option maxHeartbeats 1000000 in

theorem kp_cont_actual_sector_global_green_equation
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
      (∫ x, pair (D_U φ).val W.val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
        ∫ x, scalarPair φ (δ_U W) x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
  intro φ W
  have emb := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have dif := kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization
  let K := scalarSupport φ.val ∪ tsupport (normSquare W.val)
  have hK : IsCompact K := φ.property.2.2.union W.property.2
  obtain ⟨n,C,_,_,⟨Q⟩⟩ := kp_cont_actual_sector_finite_support_partition F ζ hζ U R P H K Set.univ
    hK isOpen_univ (Set.subset_univ _)
  let η : Fin n → RealSmoothCutoff F ζ hζ U R P H := fun i => multiplierCutoff (Q.multiplier i) (Q.smooth i)
  let Z : Fin n → T_U F ζ hζ U R P H := fun i => cotangentMultiply (η i) W
  have hsum : ∑ i, Z i = W := by
    apply Subtype.ext
    apply Subtype.ext
    funext a y
    simp only [Submodule.coe_sum, Finset.sum_apply]
    change (∑ i, (cutoffLift (η i) a y) • coefficient W.val a y) = coefficient W.val a y
    rw [← Finset.sum_smul]
    by_cases hw : coefficient W.val a y = 0
    · simp [hw]
    · have hx : q a y.val ∈ K := Or.inr (subset_tsupport _ (by
        change normSquare W.val (q a y.val) ≠ 0
        rw [normSquare_chart]
        exact pow_ne_zero 2 (nnnorm_ne_zero_iff.mpr hw)))
      have hpart := Q.partition _ (Q.contains_compact hx)
      have he : (∑ i, cutoffLift (η i) a y) = 1 := by
        simp only [cutoffLift, η, multiplierCutoff, ← Complex.ofReal_sum]
        rw [hpart, Complex.ofReal_one]
      rw [he, one_smul]
  have hloc (i : Fin n) :
      (∫ x, pair (D_U φ).val (Z i).val x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
        ∫ x, scalarPair φ (δ_U (Z i)) x ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P := by
    apply localized_green emb dif (C i) φ W (η i) (Q.compact_support i)
      (fun x hx => (Q.support_subset i hx).1) (Q.lift i) (Q.lift_support_subset i)
    intro x
    have hr := Q.lift_restriction i ⟨labeledA (placeEquiv F ζ hζ) x.val,x.property⟩
    exact hr
  have hleft : (fun x => ∑ i, pair (D_U φ).val (Z i).val x) = pair (D_U φ).val W.val := by
    funext x
    obtain ⟨a,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    simp only [pair_chart]
    rw [← inner_sum]
    have hc : (∑ i, coefficient (Z i).val a y) = coefficient W.val a y := by
      have he := congrArg (fun Z : T_U F ζ hζ U R P H => coefficient Z.val a y) hsum
      simpa only [map_sum, Submodule.coe_sum, Finset.sum_apply, coefficient] using he
    rw [hc]
  have hright : (fun x => ∑ i, scalarPair φ (δ_U (Z i)) x) = scalarPair φ (δ_U W) := by
    funext x
    obtain ⟨a,y,rfl⟩ := base_covered (R := R) (P := P) (H := H) x
    simp only [emb.scalar_pair_chart]
    rw [← inner_sum]
    have he := congrArg (fun f : S_U F ζ hζ U R P H => f.val a y) (congrArg δ_U hsum)
    simp only [map_sum, Submodule.coe_sum, Finset.sum_apply] at he
    rw [he]
  rw [← hleft, ← hright, integral_finset_sum _ (fun i _ => emb.cotangent_pair_integrable _ _),
    integral_finset_sum _ (fun i _ => emb.scalar_pair_integrable _ _)]
  exact Finset.sum_congr rfl (fun i _ => hloc i)

theorem kp_cont_actual_sector_global_green
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ) (hR : R.adelicHaar = μG)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H) :
    KPContActualSectorGlobalGreen.Properties (F := F) (ζ := ζ) (hζ := hζ)
      (U := U) (R := R) (P := P) (H := H) := by
  have emb := kp_cont_actual_sector_test_embeddings F ζ hζ μG hμG U R hR P H realization
  have hgi := kp_cont_actual_sector_global_green_equation
    F ζ hζ μG hμG U R hR P H realization
  have hgreen : ∀ (φ : S_U F ζ hζ U R P H) (W : T_U F ζ hζ U R P H),
      inner ℂ (j (D_U φ)) (j W) = inner ℂ (iota φ) (iota (δ_U W)) := by
    intro φ W
    rw [emb.cotangent_inner (D_U φ) W, emb.scalar_inner φ (δ_U W)]
    exact hgi φ W
  refine
    { cotangent_pair_integrable := fun φ W => emb.cotangent_pair_integrable (D_U φ) W
      scalar_pair_integrable := fun φ W => emb.scalar_pair_integrable φ (δ_U W)
      local_cotangent_pair_integrable := fun a φ W =>
        KPTestL2.integrable_pairing a.liftedMeasure
          (localCoefficient a (D_U φ).val) (localCoefficient a W.val)
          (emb.cotangent_local_memLp a (D_U φ)) (emb.cotangent_local_memLp a W)
      local_scalar_pair_integrable := fun a φ W =>
        KPTestL2.integrable_pairing a.liftedMeasure
          (localScalarCoefficient a φ) (localScalarCoefficient a (δ_U W))
          (emb.scalar_local_memLp a φ) (emb.scalar_local_memLp a (δ_U W))
      green_integral := fun φ W => hgi φ W
      green := fun φ W => hgreen φ W
      iota_injective := emb.iota_injective
      j_injective := emb.j_injective
      formal_adjoint :=
        KPTestOperator.descend_formalAdjoint _ emb.iota_injective _ emb.j_injective
          _ _ hgreen
      laplacian_pairing := fun φ ψ => hgreen φ (D_U ψ)
      descended_laplacian_pairing := fun φ ψ =>
        KPTestGreenTransfer.laplacian_pairing _ emb.iota_injective _ emb.j_injective
          _ _ hgreen φ ψ }

end DedekindZetaZeroFree

end
