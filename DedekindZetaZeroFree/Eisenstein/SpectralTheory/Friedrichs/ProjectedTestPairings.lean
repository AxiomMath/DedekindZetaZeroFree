module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.TensorReynoldsCancellation
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Friedrichs.WeakGradientCoordinates

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff ENNReal
open MeasureTheory Topology
namespace DedekindZetaZeroFree.KPContFriedrichsChartProjectedPairings
open KPContLocalNorm KPContActualChartRestrictionDensity
open KPContSectorCoveredQuotientVocabulary KPContSectorPhaseComponentCharts
open KPContSectorSmoothFramesSupport KPContSectorLineL2Isometry
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
private theorem overlap_mul (i : Fin (H.atlas U).componentCount)
    (γ δ : Component F ζ hζ U R P H i) (p : Space (KPCuspLogShape.dimension F * 3)) :
    overlapCoordinate F ζ hζ U R P H i (γ * δ) p =
      overlapCoordinate F ζ hζ U R P H i γ (overlapCoordinate F ζ hζ U R P H i δ p) := by
  simp only [overlapCoordinate, Homeomorph.apply_symm_apply, Subgroup.coe_mul, mul_smul]

def reynolds (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ) :
    Space (KPCuspLogShape.dimension F * 3) → ℂ := fun p =>
  (Nat.card (MulAction.stabilizer (Component F ζ hζ U R P H i) x) : ℂ)⁻¹ *
    ∑ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
      (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ *
        (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
          (φ (overlapCoordinate F ζ hζ U R P H i σ.val p))

theorem reynolds_covariant (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (δ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    reynolds i x φ (overlapCoordinate F ζ hζ U R P H i δ.val p) =
      (chi F ζ hζ (((H.atlas U).line i).rho δ.val) : ℂ) * reynolds i x φ p := by
  unfold reynolds
  rw [mul_left_comm (chi F ζ hζ (((H.atlas U).line i).rho δ.val) : ℂ)]
  congr 1
  rw [Finset.mul_sum]
  apply Fintype.sum_equiv (Equiv.mulRight δ)
  intro σ
  change (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ *
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
      (φ (overlapCoordinate F ζ hζ U R P H i σ.val
        (overlapCoordinate F ζ hζ U R P H i δ.val p))) =
    (chi F ζ hζ (((H.atlas U).line i).rho δ.val) : ℂ) *
    ((chi F ζ hζ (((H.atlas U).line i).rho (σ.val * δ.val)) : ℂ)⁻¹ *
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
        (φ (overlapCoordinate F ζ hζ U R P H i (σ.val * δ.val) p)))
  rw [overlap_mul, map_mul, map_mul, Circle.coe_mul, mul_inv_rev]
  have hd : (chi F ζ hζ (((H.atlas U).line i).rho δ.val) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp

theorem reynolds_mem_fiber (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    reynolds i x φ p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
  unfold reynolds
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  exact Submodule.smul_mem _ _ (Submodule.starProjection_apply_mem _ _)

private theorem overlap_smooth (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) :
    ContDiff ℝ (⊤ : ℕ∞) (overlapCoordinate F ζ hζ U R P H i γ) := by
  exact (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff _).comp
    ((CoreChartLocalizers.CutoffConstruction.StabilizerLinearization.rational_action_contDiff F γ.val).comp
      (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_contDiff _))

theorem reynolds_smooth (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (reynolds i x φ) := by
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  exact ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection.restrictScalars ℝ).contDiff.comp
    (hφ.comp (overlap_smooth i σ.val))

def overlapHomeomorph (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) :
    Space (KPCuspLogShape.dimension F * 3) ≃ₜ Space (KPCuspLogShape.dimension F * 3) := by
  letI : ContinuousConstSMul (KPCuspArithmetic.PGL2 F) (SymmetricSpace F) :=
    ⟨KPCuspSiegel.continuous_action F⟩
  exact ((coordinates F).trans (Homeomorph.smul γ.val)).trans (coordinates F).symm

theorem reynolds_support (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hφ : HasCompactSupport φ) :
    HasCompactSupport (reynolds i x φ) ∧
      tsupport (reynolds i x φ) ⊆ ⋃ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
        overlapHomeomorph i σ.val⁻¹ '' tsupport φ := by
  let K := ⋃ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
    overlapHomeomorph i σ.val⁻¹ '' tsupport φ
  have hK : IsCompact K := isCompact_iUnion fun σ =>
    hφ.image (overlapHomeomorph i σ.val⁻¹).continuous
  have hz : ∀ p ∉ K, reynolds i x φ p = 0 := by
    intro p hp
    have hzero : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
        φ (overlapCoordinate F ζ hζ U R P H i σ.val p) = 0 := by
      intro σ
      apply image_eq_zero_of_notMem_tsupport
      intro hn
      apply hp
      refine Set.mem_iUnion.mpr ⟨σ, overlapCoordinate F ζ hζ U R P H i σ.val p, hn, ?_⟩
      change overlapCoordinate F ζ hζ U R P H i σ.val⁻¹
        (overlapCoordinate F ζ hζ U R P H i σ.val p) = p
      simp only [overlapCoordinate, Homeomorph.apply_symm_apply, Subgroup.coe_inv,
        inv_smul_smul, Homeomorph.symm_apply_apply]
    simp [reynolds, hzero]
  have hs : tsupport (reynolds i x φ) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro p hp
    by_contra hn
    exact hp (hz p hn)
  exact ⟨hK.of_isClosed_subset isClosed_closure hs, hs⟩

theorem overlap_preserving (i : Fin (H.atlas U).componentCount)
    (γ : Component F ζ hζ U R P H i) :
    MeasurePreserving (overlapCoordinate F ζ hζ U R P H i γ)
      (volume.withDensity (fun p => ENNReal.ofReal (density F p)))
      (volume.withDensity (fun p => ENNReal.ofReal (density F p))) := by
  have hc : MeasurePreserving (coordinates F)
      (volume.withDensity (fun p => ENNReal.ofReal (density F p)))
      (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)) :=
    ⟨(coordinates F).continuous.measurable, metric_volume F⟩
  exact (hc.symm (coordinates F).toMeasurableEquiv).comp
    ((KPFiniteAdelicCuspEnds.arch_smul_measurePreserving F γ.val).comp hc)
private theorem fiber_projection_pairing (w t : ℂ)
    (hw : w ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) :
    w * star ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection t) =
      w * star t := by
  have h := Submodule.inner_starProjection_left_eq_right
    (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) w t
  rw [Submodule.starProjection_eq_self_iff.mpr hw] at h
  have hc := congrArg star h
  simpa only [RCLike.inner_apply', Complex.star_def, star_mul, map_mul, Complex.conj_conj, mul_comm] using hc.symm

theorem reynolds_fixed (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hφ : ∀ p, φ p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (hcov : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x, ∀ p,
      φ (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * φ p)
    (p : Space (KPCuspLogShape.dimension F * 3)) : reynolds i x φ p = φ p := by
  have hterm : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x,
    (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ *
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
        (φ (overlapCoordinate F ζ hζ U R P H i σ.val p)) = φ p := by
    intro σ
    rw [Submodule.starProjection_eq_self_iff.mpr (hφ _), hcov]
    rw [← mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), one_mul]
  simp only [reynolds, hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos :
      0 < Fintype.card (MulAction.stabilizer (Component F ζ hζ U R P H i) x)).ne'), one_mul]
private theorem chart_action_mem (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : p ∈ chartDomain F ζ hζ U R P H i x O) :
    overlapCoordinate F ζ hζ U R P H i σ.val p ∈ chartDomain F ζ hζ U R P H i x O := by
  let τ : MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x :=
    ⟨⟨complexProjectiveEmbedding F σ.val.val,
      ⟨σ.val.val, σ.val.property, rfl⟩⟩, by
      change complexProjectiveEmbedding F σ.val.val • x = x
      rw [complexProjectiveEmbedding_smul]
      exact σ.property⟩
  have h := Set.mem_image_of_mem (fun z : SymmetricSpace F => τ • z)
    (show coordinates F p ∈ O.neighborhood from hp)
  rw [O.invariant τ] at h
  change complexProjectiveEmbedding F σ.val.val • coordinates F p ∈ O.neighborhood at h
  simpa only [chartDomain, Set.mem_preimage, overlapCoordinate,
    Homeomorph.apply_symm_apply, complexProjectiveEmbedding_smul] using h

theorem reynolds_support_inside_chart (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ) (hφ : HasCompactSupport φ)
    (hs : tsupport φ ⊆ chartDomain F ζ hζ U R P H i x O) :
    tsupport (reynolds i x φ) ⊆ chartDomain F ζ hζ U R P H i x O := by
  intro p hp
  obtain ⟨σ, q, hq, rfl⟩ := Set.mem_iUnion.mp ((reynolds_support i x φ hφ).2 hp)
  exact chart_action_mem i x O σ⁻¹ q (hs hq)

theorem chart_action_preserving (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x) :
    MeasurePreserving (overlapCoordinate F ζ hζ U R P H i σ.val)
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        (chartDomain F ζ hζ U R P H i x O))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        (chartDomain F ζ hζ U R P H i x O)) := by
  have he : overlapCoordinate F ζ hζ U R P H i σ.val ⁻¹'
      chartDomain F ζ hζ U R P H i x O = chartDomain F ζ hζ U R P H i x O := by
    ext p
    constructor
    · intro hp
      have h := chart_action_mem i x O σ⁻¹ _ hp
      simpa only [overlapCoordinate, Homeomorph.apply_symm_apply, Subgroup.coe_inv,
        inv_smul_smul, Homeomorph.symm_apply_apply] using h
    · exact chart_action_mem i x O σ p
  have h := (overlap_preserving i σ.val).restrict_preimage_emb
    (overlapHomeomorph i σ.val).measurableEmbedding (chartDomain F ζ hζ U R P H i x O)
  rwa [he] at h
private theorem reynolds_pairing_term (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F)
    (φ w : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hw : ∀ p, w p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (hcov : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x, ∀ p,
      w (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * w p)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    w p * star ((chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ *
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
        (φ (overlapCoordinate F ζ hζ U R P H i σ.val p))) =
    w (overlapCoordinate F ζ hζ U R P H i σ.val p) *
      star (φ (overlapCoordinate F ζ hζ U R P H i σ.val p)) := by
  have hc : star (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ =
      (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) := by
    rw [← Circle.coe_inv, Complex.star_def, ← Circle.coe_inv_eq_conj, inv_inv]
  rw [star_mul, hc, hcov]
  calc
    _ = (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) *
        (w p * star ((KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
          (φ (overlapCoordinate F ζ hζ U R P H i σ.val p)))) := by ring
    _ = _ := by rw [fiber_projection_pairing _ _ (hw p)]; ring

theorem reynolds_integral_pairing (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ w : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hw : ∀ p, w p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (hcov : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x, ∀ p,
      w (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * w p)
    (hi : Integrable (fun p => w p * star (φ p))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        (chartDomain F ζ hζ U R P H i x O))) :
    (∫ p in chartDomain F ζ hζ U R P H i x O, w p * star (reynolds i x φ p)
      ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
    ∫ p in chartDomain F ζ hζ U R P H i x O, w p * star (φ p)
      ∂volume.withDensity (fun p => ENNReal.ofReal (density F p)) := by
  let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
  have he : ∀ p, w p * star (reynolds i x φ p) =
      (Nat.card G : ℂ)⁻¹ * ∑ σ : G,
        w (overlapCoordinate F ζ hζ U R P H i σ.val p) *
          star (φ (overlapCoordinate F ζ hζ U R P H i σ.val p)) := by
    intro p
    simp only [reynolds, Complex.star_def, map_mul, map_inv₀, map_natCast, map_sum]
    rw [mul_left_comm (w p), Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro σ _
    simpa only [Complex.star_def, map_mul, map_inv₀] using
      reynolds_pairing_term i x φ w hw hcov σ p
  simp_rw [he]
  have hci : ∀ σ : G, Integrable (fun p =>
      w (overlapCoordinate F ζ hζ U R P H i σ.val p) *
        star (φ (overlapCoordinate F ζ hζ U R P H i σ.val p)))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        (chartDomain F ζ hζ U R P H i x O)) := fun σ =>
    (chart_action_preserving i x O σ).integrable_comp_emb
      (overlapHomeomorph i σ.val).measurableEmbedding |>.mpr hi
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun σ _ => hci σ)]
  simp_rw [(chart_action_preserving i x O _).integral_comp
    (overlapHomeomorph i _).measurableEmbedding (fun p => w p * star (φ p))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, ← mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G).ne'), one_mul]

open KPContActualCotangentCountableShrinking KPContCotangentActualOverlap
open KPContCotangentActualGenuineTwistIsotropy KPContCotangentOverlapRationalBranches
open KPContActualSectorSmoothTestModules

private theorem central_commute (ε : rootsOfUnity 3 F)
    (c : KPCuspGenuineMonodromy.FiniteCover F ζ hζ) :
    KPCuspGenuineMonodromy.central F ζ hζ ε * c =
      c * KPCuspGenuineMonodromy.central F ζ hζ ε := by
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩) c).symm

set_option maxHeartbeats 1000000 in
private theorem root_ambiguity {i} {a b : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i} (e : Arrow a b)
    (v : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) :
    (KPCuspGenuineMonodromy.chi F ζ hζ (((H.atlas U).line i).rho e.gamma) : ℂ) * v.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * v.val := by
  let ρ := ((H.atlas U).line i).rho
  obtain ⟨u, hu⟩ := ((H.atlas U).line i).finite_comparison e.gamma
  have he := e.finite_comparison.symm.trans hu
  rw [central_commute, central_commute] at he
  have hc : KPCuspGenuineMonodromy.central F ζ hζ e.root⁻¹ * e.levelLift.val =
      KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma)⁻¹ * u.val := by
    apply mul_left_cancel (a := (H.atlas U).representative i)
    simpa [mul_assoc] using he
  have hh : KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma * e.root⁻¹) =
      u.val * e.levelLift.val⁻¹ := by
    have hd := congrArg (fun z : KPCuspGenuineMonodromy.FiniteCover F ζ hζ =>
      KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma) * z * e.levelLift.val⁻¹) hc
    simpa [map_mul, map_inv, mul_assoc] using hd
  have hm : KPCuspGenuineMonodromy.central F ζ hζ (ρ e.gamma * e.root⁻¹) ∈ U.toOpenSubgroup := by
    rw [hh]
    exact U.toOpenSubgroup.mul_mem u.property (U.toOpenSubgroup.inv_mem e.levelLift.property)
  have hv := v.property (ρ e.gamma * e.root⁻¹) hm
  have hd := congrArg (fun z : ℂ => (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * z) hv
  change (KPCuspGenuineMonodromy.chi F ζ hζ (ρ e.gamma) : ℂ) * v.val =
    (KPCuspGenuineMonodromy.chi F ζ hζ e.root : ℂ) * v.val
  simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val] at hd
  rw [mul_comm (KPCuspGenuineMonodromy.chi F ζ hζ (ρ e.gamma) : ℂ),
    ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), one_mul] at hd
  exact hd

private theorem labeledA_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (labeledA (placeEquiv F ζ hζ)) := by
  unfold labeledA
  fun_prop

private theorem labeledA_roundtrip (p : SymmetricSpace F) :
    labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) p) = p := by
  funext k
  simp [labeledA, labeledAInv]

private theorem lifted_scalar_covariant
    (a : ShrunkChart F ζ hζ U R P H)
    (f : SymmetricSpace F → ℂ)
    (hf : ∀ p, f p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (he : ∀ σ : a.Isotropy, ∀ p,
      f ((σ.val : KPCuspArithmetic.PGL2 F) • p) =
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) * f p) :
    ScalarEquivariant a (fun p => f (labeledA (placeEquiv F ζ hζ) p.val)) := by
  intro γ p hp
  have h := he γ.val.1 (labeledA (placeEquiv F ζ hζ) p)
  have hr := root_ambiguity (isotropyArrow a γ)
    (⟨f (labeledA (placeEquiv F ζ hζ) p), hf _⟩ : KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
  change _ = (chi F ζ hζ (((H.atlas U).line a.component).rho γ.val.1.val) : ℂ) *
      f (labeledA (placeEquiv F ζ hζ) p) at h
  change (chi F ζ hζ (((H.atlas U).line a.component).rho γ.val.1.val) : ℂ) *
    f (labeledA (placeEquiv F ζ hζ) p) =
      (chi F ζ hζ γ.val.2 : ℂ) * f (labeledA (placeEquiv F ζ hζ) p) at hr
  rw [hr] at h
  simpa only [Arrow.psi, coordinateMap, isotropyArrow, isotropyChart,
    ChartKind.representative, inv_one, mul_one, one_mul,
    labeledA_roundtrip, Arrow.phase, mul_inv_cancel, map_one,
    chi_coe] using h

private theorem local_support_compact (a : ShrunkChart F ζ hζ U R P H)
    (f : SymmetricSpace F → ℂ) (hcompact : HasCompactSupport f)
    (hs : tsupport f ⊆ a.domain) :
    IsCompact (localSupport a (fun p => f (labeledA (placeEquiv F ζ hζ) p.val))) ∧
      localSupport a (fun p => f (labeledA (placeEquiv F ζ hζ) p.val)) ⊆ a.baseDomain := by
  let projection : SymmetricSpace F → KPFiniteCuspAtlas.rawXU F ζ hζ U :=
    fun p => (H.atlas U).components ⟨a.component, Quotient.mk _ p⟩
  have hp : Continuous projection :=
    (H.atlas U).components.continuous.comp (continuous_sigmaMk.comp continuous_quot_mk)
  have hK := hcompact.image hp
  have hsubset : localSupport a (fun p => f (labeledA (placeEquiv F ζ hζ) p.val)) ⊆
      projection '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    rintro z ⟨p, ⟨hp, hn⟩, rfl⟩
    refine ⟨labeledA (placeEquiv F ζ hζ) p, subset_tsupport f hn, ?_⟩
    simp only [projection, KPContCotangentOverlapRationalBranches.q,
      (H.atlas U).components_formula]
    rfl
  refine ⟨hK.of_isClosed_subset isClosed_closure hsubset, ?_⟩
  intro z hz
  obtain ⟨p, hp, rfl⟩ := hsubset hz
  refine ⟨⟨p, hs hp⟩, ?_⟩
  simp only [projection, ShrunkChart.toBase, (H.atlas U).components_formula]
  rfl

theorem local_test_of_coefficient (a : ShrunkChart F ζ hζ U R P H)
    (f : SymmetricSpace F → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hs : tsupport f ⊆ a.domain)
    (hf : ∀ p, f p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (he : ∀ σ : a.Isotropy, ∀ p,
      f ((σ.val : KPCuspArithmetic.PGL2 F) • p) =
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) * f p) :
    (fun p : omega a => f (labeledA (placeEquiv F ζ hζ) p.val)) ∈ localScalarTests a := by
  refine ⟨?_, lifted_scalar_covariant a f hf he, local_support_compact a f hcompact hs⟩
  exact ⟨_, (hsm.comp labeledA_smooth).contDiffOn, fun _ => rfl⟩

theorem global_test_of_coefficient
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H)
    (f : SymmetricSpace F → ℂ) (hsm : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (hs : tsupport f ⊆ a.domain)
    (hf : ∀ p, f p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
    (he : ∀ σ : a.Isotropy, ∀ p,
      f ((σ.val : KPCuspArithmetic.PGL2 F) • p) =
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) * f p) :
    ∃ t : S_U F ζ hζ U R P H,
      (∀ p : omega a, t.val a p = f (labeledA (placeEquiv F ζ hζ) p.val)) ∧
      scalarSupport t.val ⊆ a.baseDomain := by
  let l : localScalarTests a := ⟨_, local_test_of_coefficient a f hsm hcompact hs hf he⟩
  let t := scalarZeroExtension a l
  have h := kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization
  refine ⟨t, ?_, ?_⟩
  · intro p
    exact congrFun (h.scalar_restriction_extension a l) p
  · rw [h.scalar_extension_support a l]
    exact (local_support_compact a f hcompact hs).2

theorem reynolds_global_test
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H)
    [Fintype a.Isotropy]
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : coordinates F '' tsupport φ ⊆ a.domain) :
    ∃ t : S_U F ζ hζ U R P H,
      (∀ p : omega a, t.val a p =
        reynolds a.component a.center φ
          ((coordinates F).symm (labeledA (placeEquiv F ζ hζ) p.val))) ∧
      scalarSupport t.val ⊆ a.baseDomain := by
  let f := fun p : SymmetricSpace F =>
    reynolds a.component a.center φ ((coordinates F).symm p)
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) f :=
    (reynolds_smooth a.component a.center φ hsm).comp
      (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_symm_contDiff _)
  have hfc : HasCompactSupport f :=
    (reynolds_support a.component a.center φ hc).1.comp_homeomorph (coordinates F).symm
  have hfs : tsupport f ⊆ a.domain := by
    have hsupport : tsupport f = (coordinates F).symm ⁻¹' tsupport (reynolds a.component a.center φ) :=
      tsupport_comp_eq_preimage (reynolds a.component a.center φ) (coordinates F).symm
    rw [hsupport]
    intro p hp
    obtain ⟨σ, q, hq, heq⟩ := Set.mem_iUnion.mp
      ((reynolds_support a.component a.center φ hc).2 hp)
    have hqdom := hs (Set.mem_image_of_mem (coordinates F) hq)
    have hmem := Set.mem_image_of_mem
      (fun p : SymmetricSpace F => (σ.val⁻¹ : KPCuspArithmetic.PGL2 F) • p) hqdom
    have hinv := a.invariant σ⁻¹
    simp only [Subgroup.coe_inv] at hinv
    rw [hinv] at hmem
    have hpcoord := congrArg (coordinates F) heq
    simp only [overlapHomeomorph, Homeomorph.trans_apply, Homeomorph.smul_apply,
      Homeomorph.apply_symm_apply, Subgroup.coe_inv] at hpcoord
    rwa [hpcoord] at hmem
  have hff : ∀ p, f p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U :=
    fun p => reynolds_mem_fiber a.component a.center φ _
  have hfe : ∀ σ : a.Isotropy, ∀ p,
      f ((σ.val : KPCuspArithmetic.PGL2 F) • p) =
        (chi F ζ hζ (((H.atlas U).line a.component).rho σ.val) : ℂ) * f p := by
    intro σ p
    simpa only [f, overlapCoordinate, Homeomorph.apply_symm_apply] using
      reynolds_covariant a.component a.center φ σ ((coordinates F).symm p)
  exact global_test_of_coefficient μG hμG hR realization a f hfsm hfc hfs hff hfe

private theorem sectionFields_apply (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) :=
    rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

theorem reynolds_phase_test
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H) [Fintype a.Isotropy]
    (m : PhaseSheets F ζ hζ U)
    (φ : Space (KPCuspLogShape.dimension F * 3) → ℂ)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (hs : coordinates F '' tsupport φ ⊆ a.domain) :
    ∃ t : S_U F ζ hζ U R P H,
      (∀ p, coordinates F p ∈ a.domain →
        frameCoefficient F ζ hζ U R P H (scalarCovered t) a.component m p =
          reynolds a.component a.center φ p) ∧ scalarSupport t.val ⊆ a.baseDomain := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  obtain ⟨t, ht, hts⟩ := reynolds_global_test μG hμG hR realization a φ hsm hc hs
  let t' : S_U F ζ hζ U R P H := (chi F ζ hζ ε : ℂ)⁻¹ • t
  have hP := kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization
  refine ⟨t', ?_, (hP.scalar_smul_support _ t).trans hts⟩
  intro p hp
  have htval := ht (KPContActualCotangentPieceHilbertSum.coordinates a ⟨coordinates F p, hp⟩)
  have hsection : (scalarSections t a.component).val (coordinates F p) =
      reynolds a.component a.center φ p := by
    have hrep := congrFun (congrFun (hP.scalar_represented t) a)
      (KPContActualCotangentPieceHilbertSum.coordinates a ⟨coordinates F p, hp⟩)
    rw [sectionFields_apply] at hrep
    have he : labeledA (placeEquiv F ζ hζ)
      (KPContActualCotangentPieceHilbertSum.coordinates a ⟨coordinates F p, hp⟩).val = coordinates F p := by
      funext k
      simp [KPContActualCotangentPieceHilbertSum.coordinates, labeledA, labeledAInv]
    rw [he] at hrep htval
    simpa only [Homeomorph.symm_apply_apply] using hrep.trans htval
  change frameCoefficient F ζ hζ U R P H (scalarCovered t') a.component
    (phaseClass F ζ hζ U ε) p = _
  rw [frameCoefficient_class, hP.covered_realization]
  have hsmul : (scalarSections t' a.component).val (coordinates F p) =
      (chi F ζ hζ ε : ℂ)⁻¹ * (scalarSections t a.component).val (coordinates F p) := by
    simp only [t', map_smul, Pi.smul_apply]
    rfl
  rw [hsmul, hsection, ← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]

private theorem orbifold_action_mem (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    (y : SymmetricSpace F) (hy : y ∈ O.neighborhood) :
    (σ.val : KPCuspArithmetic.PGL2 F) • y ∈ O.neighborhood := by
  let τ : MulAction.stabilizer (ArchComponent F ζ hζ U R P H i) x :=
    ⟨⟨complexProjectiveEmbedding F σ.val.val,
      ⟨σ.val.val, σ.val.property, rfl⟩⟩, by
      change complexProjectiveEmbedding F σ.val.val • x = x
      rw [complexProjectiveEmbedding_smul]
      exact σ.property⟩
  have h := Set.mem_image_of_mem (fun z : SymmetricSpace F => τ • z) hy
  rw [O.invariant τ] at h
  change complexProjectiveEmbedding F σ.val.val • y ∈ O.neighborhood at h
  simpa only [complexProjectiveEmbedding_smul] using h

private theorem supplied_compact_shrinking (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P) (i : Fin (H.atlas U).componentCount)
    (x : SymmetricSpace F) (O : OrbifoldChart F ζ hζ U R P H i x)
    (K : Set (SymmetricSpace F)) (hK : IsCompact K) (hKO : K ⊆ O.neighborhood) :
    ∃ a : ShrunkChart F ζ hζ U R P H,
      a.component = i ∧ a.center = x ∧ K ⊆ a.domain ∧ a.domain ⊆ O.neighborhood := by
  let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
  letI : Finite G := chart_stabilizer_finite F ζ hζ U R P H i x O
  letI := Fintype.ofFinite G
  let L := ⋃ g : G, (fun y : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • y) '' K
  have hLc : IsCompact L := isCompact_iUnion fun g =>
    hK.image (KPCuspSiegel.continuous_action F g.val.val)
  have hLO : L ⊆ O.neighborhood := by
    intro y hy
    obtain ⟨g, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
    exact orbifold_action_mem F ζ hζ U R P H i x O g z (hKO hz)
  obtain ⟨W, hWo, hLW, hWsub, hWc⟩ :=
    exists_open_between_and_isCompact_closure hLc O.isOpen hLO
  let V := ⋂ g : G, (fun y : SymmetricSpace F => (g.val : KPCuspArithmetic.PGL2 F) • y) ⁻¹' W
  have hVo : IsOpen V := isOpen_iInter_of_finite fun g =>
    hWo.preimage (KPCuspSiegel.continuous_action F g.val.val)
  have hVW : V ⊆ W := by
    intro y hy
    simpa using Set.mem_iInter.mp hy (1 : G)
  have hKV : K ⊆ V := by
    intro y hy
    apply Set.mem_iInter.mpr
    intro g
    exact hLW (Set.mem_iUnion.mpr ⟨g, y, hy, rfl⟩)
  refine ⟨⟨i, x, O, V, hVo,
    hWc.of_isClosed_subset isClosed_closure (closure_mono hVW),
    (closure_mono hVW).trans hWsub, ?_⟩, rfl, rfl, hKV, subset_closure.trans ((closure_mono hVW).trans hWsub)⟩
  intro g
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    apply Set.mem_iInter.mpr
    intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, ← mul_smul] using
      Set.mem_iInter.mp hz (h * g)
  · intro hy
    refine ⟨(g.val : KPCuspArithmetic.PGL2 F)⁻¹ • y, ?_, smul_inv_smul _ _⟩
    apply Set.mem_iInter.mpr
    intro h
    simpa only [Set.mem_preimage, Subgroup.coe_mul, Subgroup.coe_inv, ← mul_smul] using
      Set.mem_iInter.mp hy (h * g⁻¹)

private theorem shrinking_saturated (a : ShrunkChart F ζ hζ U R P H)
    (O : OrbifoldChart F ζ hζ U R P H a.component a.center)
    (hdom : a.domain ⊆ O.neighborhood) (p : SymmetricSpace F)
    (hp : p ∈ O.neighborhood)
    (hbase : (H.atlas U).components ⟨a.component, Quotient.mk _ p⟩ ∈ a.baseDomain) :
    p ∈ a.domain := by
  obtain ⟨y, hy⟩ := hbase
  have hh : Quotient.mk (MulAction.orbitRel
      (Component F ζ hζ U R P H a.component) (SymmetricSpace F)) y.val =
      Quotient.mk _ p := by
    have he : (H.atlas U).components ⟨a.component, Quotient.mk _ y.val⟩ =
      (H.atlas U).components ⟨a.component, Quotient.mk _ p⟩ := by
      simpa only [ShrunkChart.toBase, KPCuspSiegel.projection,
        (H.atlas U).components_formula] using hy
    exact eq_of_heq (Sigma.mk.inj ((H.atlas U).components.injective he)).2
  obtain ⟨g, hg⟩ := Quotient.exact hh
  change g • p = y.val at hg
  let g' : ArchComponent F ζ hζ U R P H a.component :=
    ⟨complexProjectiveEmbedding F g.val, Subgroup.mem_map.mpr ⟨g.val, g.property, rfl⟩⟩
  have hstab : g' ∈ MulAction.stabilizer _ a.center := by
    apply O.separated g'
    refine ⟨y.val, ⟨p, hp, ?_⟩, hdom y.property⟩
    change complexProjectiveEmbedding F g.val • p = y.val
    rw [complexProjectiveEmbedding_smul]
    exact hg
  have hgc : g ∈ a.Isotropy := by
    apply MulAction.mem_stabilizer_iff.mpr
    have h := MulAction.mem_stabilizer_iff.mp hstab
    change complexProjectiveEmbedding F g.val • a.center = a.center at h
    rwa [complexProjectiveEmbedding_smul] at h
  have h := Set.mem_image_of_mem
    (fun z : SymmetricSpace F => ((g⁻¹ : Component F ζ hζ U R P H a.component) :
      KPCuspArithmetic.PGL2 F) • z) y.property
  have hinv := a.invariant (⟨g, hgc⟩ : a.Isotropy)⁻¹
  simp only [Subgroup.coe_inv] at hinv
  simp only [Subgroup.coe_inv] at h
  rw [hinv] at h
  change g⁻¹ • y.val ∈ a.domain at h
  simpa only [← hg, inv_smul_smul] using h

private theorem test_coefficient_zero_off_base
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (t : S_U F ζ hζ U R P H) (a : ShrunkChart F ζ hζ U R P H)
    (ht : scalarSupport t.val ⊆ a.baseDomain)
    (m : PhaseSheets F ζ hζ U) (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : basePoint F ζ hζ U R P H a.component p ∉ a.baseDomain) :
    frameCoefficient F ζ hζ U R P H (scalarCovered t) a.component m p = 0 := by
  have hP := kp_cont_actual_sector_smooth_test_modules F ζ hζ μG hμG U R hR P H realization
  have hn : sectionNorm F ζ hζ U R P H (scalarSections t)
      (basePoint F ζ hζ U R P H a.component p) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    rw [← hP.scalar_support t]
    exact fun h => hp (ht h)
  rw [basePoint, sectionNorm_component, norm_eq_zero] at hn
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change frameCoefficient F ζ hζ U R P H (scalarCovered t) a.component
    (phaseClass F ζ hζ U ε) p = _
  rw [frameCoefficient_class, hP.covered_realization, hn, mul_zero]

theorem projected_test_exists
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
    letI : Finite G := chart_stabilizer_finite F ζ hζ U R P H i x O
    letI := Fintype.ofFinite G
    ∀ φ : TestFunction A.toOpens ℂ ⊤, ∃ t : S_U F ζ hζ U R P H,
      (∀ p ∈ chartDomain F ζ hζ U R P H i x O,
        frameCoefficient F ζ hζ U R P H (scalarCovered t) i m p = reynolds i x φ p) ∧
      scalarSupport t.val ⊆ baseChartImage F ζ hζ U R P H i x O := by
  dsimp only
  intro φ
  obtain ⟨a, ha, hx, hK, hdom⟩ := supplied_compact_shrinking F ζ hζ U R P H i x O
    (coordinates F '' KPContLocalCubeEmbedding.closedCarrier A)
    ((isCompact_closedBall A.center A.radius).image (coordinates F).continuous)
    (by rintro y ⟨p, hp, rfl⟩; exact hA hp)
  rcases a with ⟨j, y, O', V, hVo, hVc, hVsub, hVi⟩
  dsimp only at ha hx
  subst j
  subst y
  let a : ShrunkChart F ζ hζ U R P H := ⟨i, x, O', V, hVo, hVc, hVsub, hVi⟩
  letI : Finite a.Isotropy := by
    change Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    exact chart_stabilizer_finite F ζ hζ U R P H i x O
  letI : Fintype a.Isotropy := Fintype.ofFinite a.Isotropy
  have hs : coordinates F '' tsupport (fun p => φ p) ⊆ a.domain :=
    (Set.image_mono (φ.tsupport_subset.trans Metric.ball_subset_closedBall)).trans hK
  obtain ⟨t, ht, hts⟩ := reynolds_phase_test μG hμG hR realization a m φ φ.contDiff
    φ.hasCompactSupport hs
  have hbase : a.baseDomain ⊆ baseChartImage F ζ hζ U R P H i x O := by
    rintro z ⟨q, rfl⟩
    refine ⟨Quotient.mk _ q.val, ⟨q.val, hdom q.property, rfl⟩, ?_⟩
    simp only [ShrunkChart.toBase, (H.atlas U).components_formula]
    rfl
  refine ⟨t, ?_, hts.trans hbase⟩
  intro p hp
  by_cases hpa : coordinates F p ∈ a.domain
  · exact ht p hpa
  have hb : basePoint F ζ hζ U R P H i p ∉ a.baseDomain := by
    intro hb
    exact hpa (shrinking_saturated a O hdom _ hp hb)
  rw [test_coefficient_zero_off_base μG hμG hR realization t a hts m p hb]
  symm
  apply image_eq_zero_of_notMem_tsupport
  intro hpn
  obtain ⟨σ, q, hq, heq⟩ := Set.mem_iUnion.mp ((reynolds_support i x φ φ.hasCompactSupport).2 hpn)
  have hqdom := hs (Set.mem_image_of_mem (coordinates F) hq)
  have hmem := Set.mem_image_of_mem
    (fun p : SymmetricSpace F => (σ.val⁻¹ : KPCuspArithmetic.PGL2 F) • p) hqdom
  have hinv := a.invariant σ⁻¹
  simp only [Subgroup.coe_inv] at hinv
  rw [hinv] at hmem
  have hpcoord := congrArg (coordinates F) heq
  simp only [overlapHomeomorph, Homeomorph.trans_apply, Homeomorph.smul_apply,
    Homeomorph.apply_symm_apply, Subgroup.coe_inv] at hpcoord
  exact hpa (hpcoord ▸ hmem)

open KPContActualSectorTestEmbeddings
open TopologicalSpace

private theorem scalarPairing_continuous_iff_isQuotientMap {X Y Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] {q : X → Y} (hq : IsQuotientMap q)
    (f : Y → Z) : Continuous f ↔ Continuous (f ∘ q) := by
  refine ⟨fun h => h.comp hq.continuous, fun h => ?_⟩
  exact Continuous.mk fun s hs => by
    rw [← hq.isOpen_preimage]
    exact h.isOpen_preimage s hs

private theorem scalarPairing_chi_unit (i : Fin (H.atlas U).componentCount) (ε : rootsOfUnity 3 F) :
    ‖(KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ)‖ = 1 :=
  ((H.atlas U).line i).unitary ε

private theorem scalarPairing_inner_mul_mul_of_norm_one (c a b : ℂ) (hc : ‖c‖ = 1) :
    inner ℂ (c * a) (c * b) = inner ℂ a b := by
  rw [← smul_eq_mul, ← smul_eq_mul, inner_smul_left, inner_smul_right, ← mul_assoc]
  have h : (starRingEnd ℂ) c * c = 1 := by
    rw [RCLike.conj_mul, hc]
    simp
  rw [h, one_mul]

private theorem scalarPairing_scalarPair_covariant (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount)
    (γ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
    (x : SymmetricSpace F) :
    inner ℂ ((s i).val ((γ : KPCuspArithmetic.PGL2 F) • x))
        ((t i).val ((γ : KPCuspArithmetic.PGL2 F) • x)) =
      inner ℂ ((s i).val x) ((t i).val x) := by
  rw [(s i).property.2 γ x, (t i).property.2 γ x]
  exact scalarPairing_inner_mul_mul_of_norm_one _ _ _ (scalarPairing_chi_unit (H := H) i (((H.atlas U).line i).rho γ))

 theorem scalarPairing_scalarPair_invariant (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x y : SymmetricSpace F)
    (hxy : MulAction.orbitRel
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (SymmetricSpace F) x y) :
    inner ℂ ((s i).val x) ((t i).val x) = inner ℂ ((s i).val y) ((t i).val y) := by
  obtain ⟨γ, hγ⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hxy)
  rw [← hγ]
  exact scalarPairing_scalarPair_covariant s t i γ y

 def scalarPairing_pairOnSigma (s t : Sections F ζ hζ U R P H) :
    (Σ i : Fin (H.atlas U).componentCount,
      KPCuspSiegel.OrbitQuotient F
        (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))) → ℂ :=
  fun p => Quotient.lift (fun x => inner ℂ ((s p.1).val x) ((t p.1).val x))
    (scalarPairing_scalarPair_invariant s t p.1) p.2

 def scalarPairing_scalarPairSections (s t : Sections F ζ hζ U R P H) :
    KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ :=
  fun b => scalarPairing_pairOnSigma s t ((H.atlas U).components.symm b)

private theorem scalarPairing_scalarPairSections_components (s t : Sections F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (z : SymmetricSpace F) :
    scalarPairing_scalarPairSections s t ((H.atlas U).components ⟨i, Quotient.mk _ z⟩) =
      inner ℂ ((s i).val z) ((t i).val z) := by
  have h1 : scalarPairing_pairOnSigma s t
      ((H.atlas U).components.symm ((H.atlas U).components ⟨i, Quotient.mk _ z⟩)) =
      scalarPairing_pairOnSigma s t ⟨i, Quotient.mk _ z⟩ :=
    congrArg (scalarPairing_pairOnSigma s t) (Homeomorph.symm_apply_apply _ _)
  refine h1.trans ?_
  exact Quotient.lift_mk
    (s := MulAction.orbitRel
      (KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i))
      (SymmetricSpace F))
    (f := fun x => inner ℂ ((s i).val x) ((t i).val x))
    (h := scalarPairing_scalarPair_invariant s t i) z

private theorem scalarPairing_sectionFields_apply (s : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    sectionFields s a x = (s a.component).val (labeledA (placeEquiv F ζ hζ) x.val) := by
  have hcoe : (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).coefficient s x.val =
      (KPCuspGenuineMonodromy.chi F ζ hζ
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).splitting x.val) : ℂ) *
        (s a.component).val
          ((KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).kind.representative •
            labeledA (KPContCotangentActualGenuineTwistIsotropy.isotropyChart a).places x.val) :=
    rfl
  rw [sectionFields, hcoe]
  simp [KPContCotangentActualGenuineTwistIsotropy.isotropyChart, ChartKind.representative]

private theorem scalarPairing_scalarPairSections_chart (s t : Sections F ζ hζ U R P H)
    (a : ActualChart (U := U) (H := H)) (x : omega a) :
    scalarPairing_scalarPairSections s t (q a x.val) =
      inner ℂ (sectionFields s a x) (sectionFields t a x) := by
  have hq : q a x.val = (H.atlas U).components
      ⟨a.component, Quotient.mk _ (labeledA (placeEquiv F ζ hζ) x.val)⟩ := by
    simp only [KPContCotangentOverlapRationalBranches.q, KPCuspSiegel.projection,
      (H.atlas U).components_formula]
  rw [hq, scalarPairing_scalarPairSections_components, scalarPairing_sectionFields_apply, scalarPairing_sectionFields_apply]

private theorem scalarPairing_scalarPair_eq_sections (f g : S_U F ζ hζ U R P H) :
    scalarPair f g = scalarPairing_scalarPairSections (scalarSections f) (scalarSections g) := by
  have hfs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) f)
  have hgs := Classical.choose_spec (scalar_gluing (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) g)
  have hfsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections f) := hfs.1.1
  have hgsmooth : IsSmoothSections F ζ hζ U R P H (scalarSections g) := hgs.1.1
  have hfval : sectionFields (scalarSections f) = f.val := hfs.1.2.2
  have hgval : sectionFields (scalarSections g) = g.val := hgs.1.2.2
  have hcont : Continuous (scalarPairing_scalarPairSections (scalarSections f) (scalarSections g)) := by
    let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
    refine continuous_of_cover_nhds (s := fun n => (cover.chart n).baseDomain) ?_ ?_
    · intro x
      have hx : x ∈ ⋃ n, (cover.chart n).baseDomain := by
        rw [cover.covers]; exact Set.mem_univ x
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
      exact ⟨n, (cover.properties n).base_open.mem_nhds hn⟩
    · intro n
      set a := cover.chart n
      have hP := every_shrunkChart_properties F ζ hζ U R P H a
      rw [continuousOn_iff_continuous_domRestrict]
      refine (scalarPairing_continuous_iff_isQuotientMap hP.quotient
        (fun z : a.baseDomain =>
          scalarPairing_scalarPairSections (scalarSections f) (scalarSections g) z.val)).mpr ?_
      change Continuous (fun y : a.domain =>
        scalarPairing_scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y))
      have hbase : (fun y : a.domain =>
            scalarPairing_scalarPairSections (scalarSections f) (scalarSections g) (a.toBase y)) =
          fun y : a.domain => inner ℂ ((scalarSections f a.component).val y.val)
            ((scalarSections g a.component).val y.val) := by
        funext y
        have h1 : a.toBase y = (H.atlas U).components
            ⟨a.component, Quotient.mk _ y.val⟩ := by
          simp only [ShrunkChart.toBase, KPCuspSiegel.projection,
            (H.atlas U).components_formula]
        rw [h1, scalarPairing_scalarPairSections_components]
      rw [hbase]
      exact continuous_inner.comp
        (((hfsmooth a.component).continuous.comp continuous_subtype_val).prodMk
          ((hgsmooth a.component).continuous.comp continuous_subtype_val))
  have hchart : ∀ (a : ActualChart (U := U) (H := H)) (x : omega a),
      scalarPairing_scalarPairSections (scalarSections f) (scalarSections g) (q a x.val) =
        inner ℂ (f.val a x) (g.val a x) := by
    intro a x
    rw [scalarPairing_scalarPairSections_chart, hfval, hgval]
  exact ((Classical.choose_spec (scalarPair_descends f g)).2
    (scalarPairing_scalarPairSections (scalarSections f) (scalarSections g)) ⟨hcont, hchart⟩).symm

private theorem scalarPairing_scalarPair_coordinates (f g : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U)
    (p : Space (KPCuspLogShape.dimension F * 3)) :
    scalarPair f g (basePoint F ζ hζ U R P H i p) =
      inner ℂ (frameCoefficient F ζ hζ U R P H (scalarCovered f) i m p)
        (frameCoefficient F ζ hζ U R P H (scalarCovered g) i m p) := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  change _ = inner ℂ (frameCoefficient F ζ hζ U R P H (scalarCovered f) i (phaseClass F ζ hζ U ε) p)
    (frameCoefficient F ζ hζ U R P H (scalarCovered g) i (phaseClass F ζ hζ U ε) p)
  rw [frameCoefficient_class, frameCoefficient_class, S_scalarCovered, S_scalarCovered,
    scalarPairing_inner_mul_mul_of_norm_one _ _ _ (Circle.norm_coe _), scalarPairing_scalarPair_eq_sections]
  exact scalarPairing_scalarPairSections_components _ _ i _

set_option maxHeartbeats 1000000 in

theorem scalar_test_chart_pairing
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (f g : S_U F ζ hζ U R P H)
    (hg : scalarSupport g.val ⊆ baseChartImage F ζ hζ U R P H i x O) :
    star (inner ℂ (iota f) (iota g)) =
      (((H.disintegration U).componentWeight i /
        (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ) *
      ∫ p in chartDomain F ζ hζ U R P H i x O, (density F p : ℂ) *
        frameCoefficient F ζ hζ U R P H (scalarCovered f) i m p *
        star (frameCoefficient F ζ hζ U R P H (scalarCovered g) i m p) := by
  have he := scalar_inner realization f g
  have hz : ∀ b ∉ baseChartImage F ζ hζ U R P H i x O, scalarPair f g b = 0 := by
    intro b hb
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hb (hg (tsupport_scalarPair_subset f g h))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz] at he
  change _ = ∫ b in baseChartImage F ζ hζ U R P H i x O, scalarPair f g b
    ∂KPMsFixedHaarDisintegration.sphericalMeasure F ζ hζ R P U at he
  rw [← quotient_measure F ζ hζ U R P H i x O,
    integral_map (basePoint_measurable F ζ hζ U R P H i).aemeasurable
      (scalar_pair_continuous f g).aestronglyMeasurable,
    chartMeasure, integral_smul_measure] at he
  have hd := integral_withDensity_eq_integral_toReal_smul₀
    (μ := volume.restrict (chartDomain F ζ hζ U R P H i x O))
    (f := fun p => ENNReal.ofReal (density F p))
    (ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun p => scalarPair f g (basePoint F ζ hζ U R P H i p))
  rw [hd] at he
  have hstar := congrArg star he
  simp only [Complex.star_def, map_mul, RCLike.real_smul_eq_coe_mul,
    ENNReal.toReal_ofReal (density_positive F _).le, Complex.conj_ofReal,
    ← integral_conj] at hstar
  rw [Complex.star_def]
  rw [hstar]
  congr 1
  · exact RCLike.conj_ofReal _
  apply integral_congr_ae
  filter_upwards with p
  rw [scalarPairing_scalarPair_coordinates f g i m p]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_conj, Complex.star_def,
    RCLike.conj_ofReal]
  exact (mul_assoc (density F p : ℂ)
    (frameCoefficient F ζ hζ U R P H (scalarCovered f) i m p)
    (starRingEnd ℂ (frameCoefficient F ζ hζ U R P H (scalarCovered g) i m p))).symm

open KPContSectorScalarLineAlgebra
private theorem smooth_frameCoefficient (f : S_U F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (m : PhaseSheets F ζ hζ U) :
    ContDiff ℝ (⊤ : ℕ∞) (frameCoefficient F ζ hζ U R P H (scalarCovered f) i m) := by
  obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
  have he : frameCoefficient F ζ hζ U R P H (scalarCovered f) i
      ((QuotientGroup.mk' (centralLevel F ζ hζ U)) ε) =
      fun p => (chi F ζ hζ ε : ℂ) * (scalarSections f i).val (coordinates F p) := by
    funext p
    change frameCoefficient F ζ hζ U R P H (scalarCovered f) i (phaseClass F ζ hζ U ε) p = _
    rw [frameCoefficient_class, S_scalarCovered]
  rw [he]
  apply ContDiff.mul contDiff_const
  exact (Classical.choose_spec (scalar_gluing f)).1.1 i |>.comp
    (CoreChartLocalizers.CutoffConstruction.ChartDensityConstruction.coordinates_contDiff _)

set_option maxHeartbeats 1500000 in

theorem projected_scalar_pairing_on_tests
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : TestFunction A.toOpens ℂ ⊤) (g : S_U F ζ hζ U R P H)
    (hgc : ∀ p ∈ chartDomain F ζ hζ U R P H i x O,
      frameCoefficient F ζ hζ U R P H (scalarCovered g) i m p = reynolds i x φ p)
    (hgs : scalarSupport g.val ⊆ baseChartImage F ζ hζ U R P H i x O)
    (f : S_U F ζ hζ U R P H) :
    star (inner ℂ (iota f) (iota g)) =
      (((H.disintegration U).componentWeight i /
        (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ) *
      ∫ p in A.carrier, (density F p : ℂ) *
        frameCoefficient F ζ hζ U R P H (scalarCovered f) i m p * star (φ p) := by
  let w := frameCoefficient F ζ hζ U R P H (scalarCovered f) i m
  have hw : ∀ p, w p ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U := by
    intro p
    exact (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H (scalarCovered f)) i m
      (coordinates F p)).property
  have hc : ∀ σ : MulAction.stabilizer (Component F ζ hζ U R P H i) x, ∀ p,
      w (overlapCoordinate F ζ hζ U R P H i σ.val p) =
        (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ) * w p := by
    intro σ p
    obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
    change frameCoefficient F ζ hζ U R P H (scalarCovered f) i (phaseClass F ζ hζ U ε) _ =
      _ * frameCoefficient F ζ hζ U R P H (scalarCovered f) i (phaseClass F ζ hζ U ε) _
    rw [frameCoefficient_class, frameCoefficient_class]
    simp only [overlapCoordinate, Homeomorph.apply_symm_apply]
    rw [(S F ζ hζ U R P H (scalarCovered f) i).property.2]
    exact mul_left_comm _ _ _
  have hi : Integrable (fun p => w p * star (φ p))
      ((volume.withDensity (fun p => ENNReal.ofReal (density F p))).restrict
        (chartDomain F ζ hζ U R P H i x O)) := by
    have hD : MeasurableSet (chartDomain F ζ hζ U R P H i x O) :=
      (O.isOpen.preimage (coordinates F).continuous).measurableSet
    rw [restrict_withDensity hD]
    apply (integrable_withDensity_iff_integrable_smul₀'
      (μ := volume.restrict (chartDomain F ζ hζ U R P H i x O))
      (f := fun p => ENNReal.ofReal (density F p))
      ((ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    have hi : Integrable (fun p => (density F p : ℂ) * (w p * star (φ p))) volume := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((Complex.ofRealCLM.continuous.comp (density_smooth F).continuous).mul
          ((smooth_frameCoefficient f i m).continuous.mul φ.continuous.star))
      · apply φ.hasCompactSupport.of_isClosed_subset isClosed_closure
        apply closure_mono
        intro p hp
        contrapose! hp
        have hz : φ p = 0 := Function.notMem_support.mp hp
        apply Function.notMem_support.mpr
        rw [hz]
        simp only [star_zero, mul_zero]
    have hr := hi.mono_measure (Measure.restrict_le_self (s := chartDomain F ζ hζ U R P H i x O))
    convert hr using 1
    funext p
    simp only [ENNReal.toReal_ofReal (density_positive F p).le,
      RCLike.real_smul_eq_coe_mul]
    rfl
  rw [scalar_test_chart_pairing realization i x O m f g hgs]
  congr 1
  have hd : ∀ (b : Space (KPCuspLogShape.dimension F * 3) → ℂ),
      (∫ p in chartDomain F ζ hζ U R P H i x O, b p
        ∂volume.withDensity (fun p => ENNReal.ofReal (density F p))) =
      ∫ p in chartDomain F ζ hζ U R P H i x O, (density F p : ℂ) * b p := by
    intro b
    have hD : MeasurableSet (chartDomain F ζ hζ U R P H i x O) :=
      (O.isOpen.preimage (coordinates F).continuous).measurableSet
    have hd := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
      (μ := volume) (f := fun p => ENNReal.ofReal (density F p))
      ((ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) b hD
    simp only [ENNReal.toReal_ofReal (density_positive F _).le,
      RCLike.real_smul_eq_coe_mul] at hd
    exact hd
  have he := reynolds_integral_pairing i x O φ w hw hc hi
  rw [hd, hd] at he
  calc
    _ = ∫ p in chartDomain F ζ hζ U R P H i x O,
        (density F p : ℂ) * (w p * star (reynolds i x φ p)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (O.isOpen.preimage (coordinates F).continuous).measurableSet] with p hp
      rw [hgc p hp]
      exact mul_assoc _ _ _
    _ = _ := he
    _ = ∫ p in A.carrier, (density F p : ℂ) * (w p * star (φ p)) := by
      apply setIntegral_eq_of_subset_of_ae_diff_eq_zero
        (O.isOpen.preimage (coordinates F).continuous).measurableSet.nullMeasurableSet
        (Metric.ball_subset_closedBall.trans hA)
      filter_upwards with p hp
      have hz : φ p = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hp.2 (φ.tsupport_subset ht))
      simp only [hz, star_zero, mul_zero]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with p
      exact (mul_assoc _ _ _).symm

private theorem restriction_iota_ae (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    (f : S_U F ζ hζ U R P H) :
    restriction F ζ hζ U R P H i x O m A hA (iota f) =ᵐ[volume.restrict A.carrier]
      frameCoefficient F ζ hζ U R P H (scalarCovered f) i m := by
  have hfcont : Continuous (scalarCovered f).val := by
    change Continuous (scalarRepresentative F ζ hζ U R P H (scalarSections f)).val
    exact (KPContSectorLineL2Isometry.continuous_iff F ζ hζ U R P H _).mp
      (fun i => ((Classical.choose_spec (scalar_gluing f)).1.1 i).continuous)
  let b : BorelL2Scalars F ζ hζ U R := ⟨scalarCovered f, hfcont.measurable, scalar_memLp f⟩
  apply restriction_representative F ζ hζ U R P H i x O m A hA (iota f) b
  apply Subtype.ext
  rw [scalarEmbedding_coe, scalar_represented]

private theorem weighted_test_memLp (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (φ : TestFunction A.toOpens ℂ ⊤) :
    MemLp (fun p => (density F p : ℂ) * φ p) 2 (volume.restrict A.carrier) := by
  apply Continuous.memLp_of_hasCompactSupport
  · exact (Complex.ofRealCLM.continuous.comp (density_smooth F).continuous).mul φ.continuous
  · exact φ.hasCompactSupport.mul_left

set_option maxHeartbeats 1200000 in

theorem projected_scalar_pairing
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O)
    [Fintype (MulAction.stabilizer (Component F ζ hζ U R P H i) x)]
    (φ : TestFunction A.toOpens ℂ ⊤) (g : S_U F ζ hζ U R P H)
    (hgc : ∀ p ∈ chartDomain F ζ hζ U R P H i x O,
      frameCoefficient F ζ hζ U R P H (scalarCovered g) i m p = reynolds i x φ p)
    (hgs : scalarSupport g.val ⊆ baseChartImage F ζ hζ U R P H i x O)
    (w : KPContSectorClosedLpSubspace.H F ζ hζ R U) :
    star (inner ℂ w (iota g)) =
      (((H.disintegration U).componentWeight i /
        (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ) *
      ∫ p in A.carrier, (density F p : ℂ) *
        restriction F ζ hζ U R P H i x O m A hA w p * star (φ p) := by
  let b : BallL2 A := (weighted_test_memLp A φ).toLp (fun p => (density F p : ℂ) * φ p)
  have hb : ∀ v : BallL2 A, inner ℂ b v =
      ∫ p in A.carrier, (density F p : ℂ) * v p * star (φ p) := by
    intro v
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(weighted_test_memLp A φ).coeFn_toLp] with p hp
    rw [hp]
    simp only [RCLike.inner_apply', map_mul, RCLike.conj_ofReal, Complex.star_def]
    have hreal : starRingEnd ℂ (density F p : ℂ) = (density F p : ℂ) := RCLike.conj_ofReal _
    rw [hreal]
    exact mul_right_comm (density F p : ℂ) (starRingEnd ℂ (φ p)) (v p)
  let c : ℂ := (((H.disintegration U).componentWeight i /
    (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ)
  have he : (fun v : KPContSectorClosedLpSubspace.H F ζ hζ R U => star (inner ℂ v (iota g))) =
      (fun v => c * inner ℂ b (restriction F ζ hζ U R P H i x O m A hA v)) := by
    apply (KPContActualSectorFriedrichsSynthesis.scalarDense F ζ hζ U R P H μG hμG hR realization).equalizer
    · have h : Continuous (fun v : KPContSectorClosedLpSubspace.H F ζ hζ R U =>
          inner ℂ (v : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) (iota g)) :=
        continuous_subtype_val.inner continuous_const
      exact h.star
    · exact continuous_const.mul (continuous_const.inner
        (restriction F ζ hζ U R P H i x O m A hA).continuous)
    · funext f
      simp only [Function.comp_apply]
      rw [projected_scalar_pairing_on_tests realization i x O m A hA φ g hgc hgs f, hb]
      congr 1
      apply integral_congr_ae
      filter_upwards [restriction_iota_ae i x O m A hA f] with p hp
      rw [hp]
  rw [congrFun he w, hb]

open KPContActualCotangentChartRestriction KPContActualCotangentMeasurableFamilies

 def cotangentDecode (p : Space (KPCuspLogShape.dimension F * 3))
    (v : KPContCotangentActualGenuineTwistIsotropy.E F)
    (j : Fin (KPCuspLogShape.dimension F * 3)) : ℂ :=
  let ik := finProdFinEquiv.symm j
  let q := labeledAInv (placeEquiv F ζ hζ) (coordinates F p)
  let k := (placeEquiv F ζ hζ).symm ik.1
  ![(Real.exp (-q (k, 2)) : ℂ) * v (k, 1),
    (Real.exp (-q (k, 2)) : ℂ) * v (k, 2), v (k, 0)] ik.2
private theorem cotangent_inv_height (p : Space (KPCuspLogShape.dimension F * 3))
    (i : Fin (d F)) :
    (labeledAInv (placeEquiv F ζ hζ) (coordinates F p)) (i, 2) =
      (coordinates F p ((placeEquiv F ζ hζ) i)).2 := by
  simp [labeledAInv, CotangentLogCoframe.A]
private theorem cotangent_exp_cancel (t : ℝ) :
    (Real.exp (2 * t) : ℂ) * (Real.exp (-t) : ℂ) * (Real.exp (-t) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
  convert Complex.ofReal_one using 1
  ring_nf
  simp
private theorem cotangent_decode_pair (p : Space (KPCuspLogShape.dimension F * 3))
    (v w : KPContCotangentActualGenuineTwistIsotropy.E F) :
    (∑ j : Fin (KPCuspLogShape.dimension F * 3),
      ((if (finProdFinEquiv.symm j).2 = 2 then 1 else
        Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
      cotangentDecode (ζ := ζ) (hζ := hζ) p v j * star (cotangentDecode (ζ := ζ) (hζ := hζ) p w j)) =
      inner ℂ w v := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (placeEquiv F ζ hζ)]
  rw [PiLp.inner_apply]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.sum_univ_three, cotangentDecode, Equiv.symm_apply_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, cotangent_inv_height]
  simp only [show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide,
    ite_false, ite_true, star_mul, Complex.star_def,
    Complex.conj_ofReal, RCLike.inner_apply']
  dsimp only [Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  simp only [Matrix.cons_val_succ, Matrix.cons_val_zero]
  have he := cotangent_exp_cancel (coordinates F p ((placeEquiv F ζ hζ) i)).2
  calc
    _ = ((Real.exp (2 * (coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) *
      (Real.exp (-(coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ) *
      (Real.exp (-(coordinates F p ((placeEquiv F ζ hζ) i)).2) : ℂ)) *
      (starRingEnd ℂ (w (i, 1)) * v (i, 1) + starRingEnd ℂ (w (i, 2)) * v (i, 2)) +
      starRingEnd ℂ (w (i, 0)) * v (i, 0) := by ring
    _ = _ := by rw [he]; ring

private theorem shrinking_coordinate_integral (a : ShrunkChart F ζ hζ U R P H)
    (f : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℂ) (hf : Measurable f) :
    (∫ z in a.baseDomain, f z ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      (((H.disintegration U).componentWeight a.component /
        (Nat.card a.Isotropy : ℝ≥0∞)).toReal : ℂ) *
      ∫ p in (coordinates F) ⁻¹' a.domain,
        (density F p : ℂ) * f (basePoint F ζ hζ U R P H a.component p) := by
  have hP := every_shrunkChart_properties F ζ hζ U R P H a
  rw [← hP.exact_pushforward,
    integral_map hP.measurable.aemeasurable hf.aestronglyMeasurable,
    ShrunkChart.liftedMeasure, integral_smul_measure]
  simp only [RCLike.real_smul_eq_coe_mul]
  congr 1
  have hsub := integral_subtype_comap (μ :=
    (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F)).restrict a.domain)
    a.domain_open.measurableSet
    (fun z => f ((H.atlas U).components ⟨a.component, Quotient.mk _ z⟩))
  have hbase : a.toBase = fun z : a.domain =>
      (H.atlas U).components ⟨a.component, Quotient.mk _ z.val⟩ := by
    funext z
    simp only [ShrunkChart.toBase, KPCuspSiegel.projection, (H.atlas U).components_formula]
  rw [hbase]
  rw [hsub, Measure.restrict_restrict a.domain_open.measurableSet, Set.inter_self]
  rw [← metric_volume F, Measure.restrict_map (coordinates F).continuous.measurable
      a.domain_open.measurableSet]
  have hmeas : Measurable (fun z : SymmetricSpace F =>
      f ((H.atlas U).components ⟨a.component, Quotient.mk _ z⟩)) := by
    have hb := hf.comp ((basePoint_measurable F ζ hζ U R P H a.component).comp
      (coordinates F).symm.continuous.measurable)
    have he : (f ∘ basePoint F ζ hζ U R P H a.component ∘ (coordinates F).symm) =
        (fun z => f ((H.atlas U).components ⟨a.component, Quotient.mk _ z⟩)) := by
      funext z
      simp only [basePoint, Function.comp_apply, Homeomorph.apply_symm_apply]
    rw [he] at hb
    exact hb
  rw [integral_map (coordinates F).continuous.measurable.aemeasurable hmeas.aestronglyMeasurable]
  have hD : MeasurableSet ((coordinates F) ⁻¹' a.domain) :=
    (coordinates F).continuous.measurable a.domain_open.measurableSet
  have hd := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (μ := volume) (f := fun p => ENNReal.ofReal (density F p))
    (ENNReal.measurable_ofReal.comp (density_smooth F).continuous.measurable).aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)
    (fun p => f (basePoint F ζ hζ U R P H a.component p)) hD
  simp only [basePoint] at hd
  rw [hd]
  simp only [ENNReal.toReal_ofReal (density_positive F _).le,
    RCLike.real_smul_eq_coe_mul, basePoint]
  rfl
open KPContActualSectorSmoothTestModules KPContCotangentOverlapRationalBranches
open KPContActualSectorTestDifferentialDescent
private theorem cotangent_pair_zero_off_support
    (r z : Family (U := U) (H := H))
    (b : KPFiniteCuspAtlas.rawXU F ζ hζ U) (hb : b ∉ cotangentSupport z) :
    pair r z b = 0 := by
  let cover := KPContActualSectorCotangentL2.chosenCover F ζ hζ U R P H
  have hbcover : b ∈ ⋃ n, (cover.chart n).baseDomain := by rw [cover.covers]; trivial
  obtain ⟨n, y, hy⟩ := Set.mem_iUnion.mp hbcover
  let a := cover.chart n
  let x := KPContActualCotangentPieceHilbertSum.coordinates a y
  have hq : q a x.val = b := by
    have hround : ∀ y : SymmetricSpace F,
        labeledA (placeEquiv F ζ hζ) (labeledAInv (placeEquiv F ζ hζ) y) = y := by
      intro y
      funext k
      simp [labeledA, labeledAInv]
    change q a (labeledAInv (placeEquiv F ζ hζ) y.val) = b
    rw [KPContCotangentOverlapRationalBranches.q, hround]
    exact hy
  have hz : coefficient z a x = 0 := by
    by_contra hn
    exact hb (subset_closure ⟨a, x, hq, hn⟩)
  rw [← hq, pair_chart, hz, inner_zero_right]

private theorem cotangent_chart_normalization (a : ShrunkChart F ζ hζ U R P H)
    (r z : Family (U := U) (H := H)) (hz : cotangentSupport z ⊆ a.baseDomain) :
    star (∫ b, pair r z b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      (((H.disintegration U).componentWeight a.component /
        (Nat.card a.Isotropy : ℝ≥0∞)).toReal : ℂ) *
      ∫ p in (coordinates F) ⁻¹' a.domain,
        (density F p : ℂ) * star (pair r z (basePoint F ζ hζ U R P H a.component p)) := by
  have hout : ∀ b ∉ a.baseDomain, pair r z b = 0 := by
    intro b hb
    exact cotangent_pair_zero_off_support r z b (fun hc => hb (hz hc))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout,
    shrinking_coordinate_integral a _ (measurable_pair r z)]
  simp only [Complex.star_def, map_mul, Complex.conj_ofReal, ← integral_conj]

private theorem cotangent_pair_coordinates (a : ShrunkChart F ζ hζ U R P H)
    (r z : Family (U := U) (H := H))
    (p : Space (KPCuspLogShape.dimension F * 3)) (hp : coordinates F p ∈ a.domain) :
    pair r z (basePoint F ζ hζ U R P H a.component p) =
      inner ℂ
        (liftExtension a (coefficient r a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p)))
        (liftExtension a (coefficient z a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) := by
  have hround : labeledA (placeEquiv F ζ hζ)
      (labeledAInv (placeEquiv F ζ hζ) (coordinates F p)) = coordinates F p := by
    funext k
    simp [labeledA, labeledAInv]
  have hq : labeledAInv (placeEquiv F ζ hζ) (coordinates F p) ∈ omega a := by
    change labeledA (placeEquiv F ζ hζ) _ ∈ a.domain
    rwa [hround]
  have he : basePoint F ζ hζ U R P H a.component p =
      q a (labeledAInv (placeEquiv F ζ hζ) (coordinates F p)) := by
    simp only [basePoint, KPContCotangentOverlapRationalBranches.q, hround, KPCuspSiegel.projection, (H.atlas U).components_formula]
  rw [he, pair_chart r z a ⟨_, hq⟩, liftExtension, liftExtension,
    dite_eq_left hq, dite_eq_left hq]

private theorem projected_test_in_shrinking
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
    letI : Finite G := chart_stabilizer_finite F ζ hζ U R P H i x O
    letI := Fintype.ofFinite G
    ∀ φ : TestFunction A.toOpens ℂ ⊤,
      ∃ a : ShrunkChart F ζ hζ U R P H,
        a.component = i ∧ a.center = x ∧
        coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain ∧
        a.domain ⊆ O.neighborhood ∧ ∃ t : S_U F ζ hζ U R P H,
          (∀ p ∈ chartDomain F ζ hζ U R P H i x O,
            frameCoefficient F ζ hζ U R P H (scalarCovered t) i m p = reynolds i x φ p) ∧
          scalarSupport t.val ⊆ a.baseDomain := by
  dsimp only
  intro φ
  obtain ⟨a, ha, hx, hK, hdom⟩ := supplied_compact_shrinking F ζ hζ U R P H i x O
    (coordinates F '' KPContLocalCubeEmbedding.closedCarrier A)
    ((isCompact_closedBall A.center A.radius).image (coordinates F).continuous)
    (by rintro y ⟨p, hp, rfl⟩; exact hA hp)
  rcases a with ⟨j, y, O', V, hVo, hVc, hVsub, hVi⟩
  dsimp only at ha hx
  subst j
  subst y
  let a : ShrunkChart F ζ hζ U R P H := ⟨i, x, O', V, hVo, hVc, hVsub, hVi⟩
  letI : Finite a.Isotropy := by
    change Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
    exact chart_stabilizer_finite F ζ hζ U R P H i x O
  letI : Fintype a.Isotropy := Fintype.ofFinite a.Isotropy
  have hs : coordinates F '' tsupport (fun p => φ p) ⊆ a.domain :=
    (Set.image_mono (φ.tsupport_subset.trans Metric.ball_subset_closedBall)).trans hK
  obtain ⟨t, ht, hts⟩ := reynolds_phase_test μG hμG hR realization a m φ φ.contDiff
    φ.hasCompactSupport hs
  have hbase : a.baseDomain ⊆ baseChartImage F ζ hζ U R P H i x O := by
    rintro z ⟨q, rfl⟩
    refine ⟨Quotient.mk _ q.val, ⟨q.val, hdom q.property, rfl⟩, ?_⟩
    simp only [ShrunkChart.toBase, (H.atlas U).components_formula]
    rfl
  refine ⟨a, rfl, rfl, hK, hdom, t, ?_, hts⟩
  intro p hp
  by_cases hpa : coordinates F p ∈ a.domain
  · exact ht p hpa
  have hb : basePoint F ζ hζ U R P H i p ∉ a.baseDomain := by
    intro hb
    exact hpa (shrinking_saturated a O hdom _ hp hb)
  rw [test_coefficient_zero_off_base μG hμG hR realization t a hts m p hb]
  symm
  apply image_eq_zero_of_notMem_tsupport
  intro hpn
  obtain ⟨σ, q, hq, heq⟩ := Set.mem_iUnion.mp ((reynolds_support i x φ φ.hasCompactSupport).2 hpn)
  have hqdom := hs (Set.mem_image_of_mem (coordinates F) hq)
  have hmem := Set.mem_image_of_mem
    (fun p : SymmetricSpace F => (σ.val⁻¹ : KPCuspArithmetic.PGL2 F) • p) hqdom
  have hinv := a.invariant σ⁻¹
  simp only [Subgroup.coe_inv] at hinv
  rw [hinv] at hmem
  have hpcoord := congrArg (coordinates F) heq
  simp only [overlapHomeomorph, Homeomorph.trans_apply, Homeomorph.smul_apply,
    Homeomorph.apply_symm_apply, Subgroup.coe_inv] at hpcoord
  exact hpa (hpcoord ▸ hmem)

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
 def canonicalLinear : Space (KPCuspLogShape.dimension F * 3) ≃ₗᵢ[ℝ] M F :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (placeEquiv F ζ hζ).symm (Equiv.refl (Fin 3))))
private theorem canonicalLinear_apply (p : Space (KPCuspLogShape.dimension F * 3)) :
    canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) p =
      labeledAInv (placeEquiv F ζ hζ) (coordinates F p) := by
  ext ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [canonicalLinear, LinearIsometryEquiv.piLpCongrLeft_apply,
    labeledAInv, coordinates, KPArchRealCoordinates.coordinates, CotangentLogCoframe.A]
private theorem canonicalLinear_single (j : Fin (KPCuspLogShape.dimension F * 3)) :
    canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) (EuclideanSpace.single j 1) =
      HyperbolicChart.coordinateVector (d F) ((placeEquiv F ζ hζ).symm (finProdFinEquiv.symm j).1)
        (finProdFinEquiv.symm j).2 := by
  ext ik
  simp only [canonicalLinear, LinearIsometryEquiv.piLpCongrLeft_apply, HyperbolicChart.coordinateVector]
  simp only [EuclideanSpace.single, Equiv.piCongrLeft'_apply, PiLp.ofLp_single, Pi.single_apply]
  change (if finProdFinEquiv ((placeEquiv F ζ hζ) ik.1,ik.2) = j then 1 else 0) =
    (if ik = ((placeEquiv F ζ hζ).symm (finProdFinEquiv.symm j).1, (finProdFinEquiv.symm j).2) then 1 else 0)
  congr 1
  exact propext (Equiv.apply_eq_iff_eq_symm_apply
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (placeEquiv F ζ hζ).symm (Equiv.refl (Fin 3)))).symm)

private theorem decode_differential (a : ShrunkChart F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : coordinates F p ∈ a.domain) (j : Fin (KPCuspLogShape.dimension F * 3)) :
    cotangentDecode (ζ := ζ) (hζ := hζ) p
      (liftExtension a (coefficient (D_U f).val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j =
      coordinateDerivativeList [j] (fun p => (scalarSections f a.component).val (coordinates F p)) p := by
  let q := labeledAInv (placeEquiv F ζ hζ) (coordinates F p)
  have hq : q ∈ omega a := by change labeledA (placeEquiv F ζ hζ) q ∈ a.domain; rwa [labeledA_roundtrip]
  have hg : (fun y => liftExtension a (f.val a) y) =ᶠ[𝓝 q]
      (fun y => (scalarSections f a.component).val (labeledA (placeEquiv F ζ hζ) y)) := by
    have hopen : IsOpen (omega a) := a.domain_open.preimage
      (labeledA_smooth (F := F) (ζ := ζ) (hζ := hζ)).continuous
    filter_upwards [hopen.mem_nhds hq] with y hy
    rw [liftExtension, dite_eq_left hy]
    have hs := congrFun (Classical.choose_spec (scalar_gluing f)).1.2.2 a
    rw [← hs]
    exact sectionFields_apply _ a ⟨y,hy⟩
  have hd : DifferentiableAt ℝ (liftExtension a (f.val a)) q :=
    (((Classical.choose_spec (scalar_gluing f)).1.1 a.component).comp (labeledA_smooth (F := F) (ζ := ζ) (hζ := hζ))).differentiable (by simp) |>.differentiableAt |>.congr_of_eventuallyEq hg
  have hqp : canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) p = q := canonicalLinear_apply p
  rw [← hqp] at hd
  have hc := hd.hasFDerivAt.comp p
    ((canonicalLinear (F := F) (ζ := ζ) (hζ := hζ)).toContinuousLinearEquiv.hasFDerivAt)
  have he : (fun y => liftExtension a (f.val a) (canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) y)) =ᶠ[𝓝 p]
      (fun y => (scalarSections f a.component).val (coordinates F y)) := by
    have hn := hg.comp_tendsto (hqp ▸ (canonicalLinear (F := F) (ζ := ζ) (hζ := hζ)).continuous.tendsto p)
    filter_upwards [hn] with y hy
    change liftExtension a (f.val a) (canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) y) = _ at hy
    rw [hy]
    simp only [Function.comp_apply]
    rw [canonicalLinear_apply, labeledA_roundtrip]
  have hc' := hc.fderiv
  change fderiv ℝ (fun y => liftExtension a (f.val a) (canonicalLinear (F := F) (ζ := ζ) (hζ := hζ) y)) p = _ at hc'
  rw [he.fderiv_eq] at hc'
  change _ = fderiv ℝ (fun y => (scalarSections f a.component).val (coordinates F y)) p (EuclideanSpace.single j 1)
  rw [hc']
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe]
  rw [canonicalLinear_single, hqp]
  unfold cotangentDecode
  change _ = HyperbolicChart.coordinateDerivative (d F) _ _ _ q
  rw [liftExtension, dite_eq_left hq]
  have hdf : coefficient (D_U f).val a ⟨q,hq⟩ = chartDifferential a (f.val a) ⟨q,hq⟩ := rfl
  change _ = _
  rw [hdf]
  change _ = _
  generalize hi : finProdFinEquiv.symm j = ik
  obtain ⟨i,k⟩ := ik
  fin_cases k <;> simp [chartDifferential, CotangentLogCoframe.j_apply,
    HyperbolicChart.differential, q, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add,
    ← Complex.exp_add]

private theorem test_gradient_class
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) :
    KPContActualSectorCotangentL2.ofFamily F ζ hζ U R P H (cotangentSquareFamily (D_U f)) =
      (KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization).closure
        (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f) := by
  let A := KPContActualSectorFriedrichsSynthesis.A_U F ζ hζ U R P H μG hμG hR realization
  have hh := A.le_closure.2 (x := ⟨iota f, LinearMap.mem_range_self iota f⟩)
    (y := KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f) rfl
  refine Eq.trans ?_ hh
  change j (D_U f) = A ⟨iota f, _⟩
  unfold A KPContActualSectorFriedrichsSynthesis.A_U
  exact (KPTestOperator.descend_image (S := S_U F ζ hζ U R P H) (T := T_U F ζ hζ U R P H)
    (iota (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (KPContActualSectorFriedrichsSynthesis.scalarInjective F ζ hζ U R P H μG hμG hR realization)
    (j (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H))
    (D_U (F := F) (ζ := ζ) (hζ := hζ) (U := U) (H := H)) f).symm

private theorem phased_differential (a : ShrunkChart F ζ hζ U R P H)
    (f : S_U F ζ hζ U R P H) (p : Space (KPCuspLogShape.dimension F * 3))
    (hp : coordinates F p ∈ a.domain) (ε : rootsOfUnity 3 F)
    (j : Fin (KPCuspLogShape.dimension F * 3)) :
    (chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p
      (liftExtension a (coefficient (D_U f).val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j =
      coordinateDerivativeList [j] (frameCoefficient F ζ hζ U R P H (scalarCovered f) a.component (phaseClass F ζ hζ U ε)) p := by
  rw [decode_differential a f p hp j]
  have hf : frameCoefficient F ζ hζ U R P H (scalarCovered f) a.component (phaseClass F ζ hζ U ε) =
      (chi F ζ hζ ε : ℂ) • (fun p => (scalarSections f a.component).val (coordinates F p)) := by
    funext p
    rw [frameCoefficient_class, S_scalarCovered]
    rfl
  rw [hf]
  change _ = fderiv ℝ ((chi F ζ hζ ε : ℂ) • _) p (EuclideanSpace.single j 1)
  rw [fderiv_const_smul_field]
  rfl

private theorem phased_decode_pair (p : Space (KPCuspLogShape.dimension F * 3))
    (v w : KPContCotangentActualGenuineTwistIsotropy.E F) (ε : rootsOfUnity 3 F) :
    (∑ j : Fin (KPCuspLogShape.dimension F * 3),
      ((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
      ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p v j) *
      star ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p w j)) = inner ℂ w v := by
  have he : (chi F ζ hζ ε : ℂ) * star (chi F ζ hζ ε : ℂ) = 1 := by
    simpa [Complex.mul_conj] using (chi F ζ hζ ε).normSq_coe
  have hf : ∀ j, ((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
      ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p v j) *
      star ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p w j) =
      ((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
        cotangentDecode (ζ := ζ) (hζ := hζ) p v j * star (cotangentDecode (ζ := ζ) (hζ := hζ) p w j) := by
    intro j
    rw [star_mul]
    calc _ = ((chi F ζ hζ ε : ℂ) * star (chi F ζ hζ ε : ℂ)) *
      (((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
        cotangentDecode (ζ := ζ) (hζ := hζ) p v j * star (cotangentDecode (ζ := ζ) (hζ := hζ) p w j)) := by ring
         _ = _ := by rw [he,one_mul]
  simp_rw [hf]
  exact cotangent_decode_pair p v w

private theorem tensor_test_pairing
    (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ)) (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (a : ShrunkChart F ζ hζ U R P H)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : coordinates F '' KPContLocalCubeEmbedding.closedCarrier A ⊆ a.domain)
    (ε : rootsOfUnity 3 F) (W : SquareFiniteFamily (U := U) (H := H))
    (φ : TestFunction A.toOpens ℂ ⊤) (f : S_U F ζ hζ U R P H)
    [Fintype a.Isotropy]
    (hfc : ∀ p, coordinates F p ∈ a.domain → frameCoefficient F ζ hζ U R P H (scalarCovered f)
      a.component (phaseClass F ζ hζ U ε) p = reynolds a.component a.center φ p)
    (hfs : scalarSupport f.val ⊆ a.baseDomain) :
    star (∫ b, pair W.val (D_U f).val b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) =
      (((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)).toReal : ℂ) *
        ∫ p in A.carrier, (density F p : ℂ) * ∑ j : Fin (KPCuspLogShape.dimension F * 3),
          ((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
          ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p
            (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] (fun q => φ q) p) := by
  have hds : cotangentSupport (D_U f).val ⊆ scalarSupport f.val :=
    (kp_cont_actual_sector_test_differential_descent F ζ hζ μG hμG U R hR P H realization).differential_support f
  rw [cotangent_chart_normalization a W.val (D_U f).val (hds.trans hfs)]
  congr 1
  trans ∫ p in (coordinates F) ⁻¹' a.domain, (density F p : ℂ) *
      ∑ j : Fin (KPCuspLogShape.dimension F * 3),
        ((if (finProdFinEquiv.symm j).2 = 2 then 1 else Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℂ) *
          ((chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p
            (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j) *
          star (coordinateDerivativeList [j] (reynolds a.component a.center φ) p)
  · apply setIntegral_congr_fun (a.domain_open.preimage (coordinates F).continuous).measurableSet
    intro p hp
    dsimp only
    rw [cotangent_pair_coordinates a W.val (D_U f).val p hp]
    simp only [Complex.star_def, inner_conj_symm]
    congr 1
    rw [← phased_decode_pair (ζ := ζ) (hζ := hζ) p _ _ ε]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    have hne : frameCoefficient F ζ hζ U R P H (scalarCovered f) a.component (phaseClass F ζ hζ U ε) =ᶠ[𝓝 p]
        reynolds a.component a.center φ :=
      Filter.eventuallyEq_of_mem ((a.domain_open.preimage (coordinates F).continuous).mem_nhds hp) hfc
    change star (_ * _) = star (fderiv ℝ (reynolds a.component a.center φ) p (EuclideanSpace.single j 1))
    rw [← hne.fderiv_eq]
    exact congrArg star (phased_differential a f p hp ε j)
  · have h := KPContFriedrichsTensorReynolds.tensor_reynolds_integral a A hA ε W φ
    dsimp only at h
    convert h using 1
    · apply setIntegral_congr_fun (a.domain_open.preimage (coordinates F).continuous).measurableSet
      intro p hp
      dsimp only
      simp only [← chi_coe, cotangentDecode, apply_ite, Complex.ofReal_one]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      congr 1
      congr 1
      congr 2
      exact Subsingleton.elim _ _
    · apply setIntegral_congr_fun A.toOpens.isOpen.measurableSet
      intro p hp
      simp only [← chi_coe, cotangentDecode, apply_ite, Complex.ofReal_one]

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem projected_test_pairings (μG : Measure (KPMsFixedHaarDisintegration.Cover F ζ hζ))
    (hμG : μG.IsHaarMeasure) (hR : R.adelicHaar = μG)
    (realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
    (O : OrbifoldChart F ζ hζ U R P H i x) (m : PhaseSheets F ζ hζ U)
    (A : LocalBall (KPCuspLogShape.dimension F * 3))
    (hA : KPContLocalCubeEmbedding.closedCarrier A ⊆ chartDomain F ζ hζ U R P H i x O) :
    let G := MulAction.stabilizer (Component F ζ hζ U R P H i) x
    letI : Finite G := chart_stabilizer_finite F ζ hζ U R P H i x O
    letI := Fintype.ofFinite G
    let c : ℂ := (((H.disintegration U).componentWeight i /
      (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℝ)
    ∀ φ : TestFunction A.toOpens ℂ ⊤,
    ∃ f : KPContActualSectorSmoothTestModules.S_U F ζ hζ U R P H,
      (∀ p ∈ chartDomain F ζ hζ U R P H i x O,
        frameCoefficient F ζ hζ U R P H
          (KPContActualSectorSmoothTestModules.scalarCovered f) i m p =
        (Nat.card G : ℂ)⁻¹ * ∑ σ : G,
          (chi F ζ hζ (((H.atlas U).line i).rho σ.val) : ℂ)⁻¹ *
            (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U).starProjection
              (φ (overlapCoordinate F ζ hζ U R P H i σ.val p))) ∧
      KPContActualSectorSmoothTestModules.scalarSupport f.val ⊆
        baseChartImage F ζ hζ U R P H i x O ∧
      (∀ w : KPContSectorClosedLpSubspace.H F ζ hζ R U,
        star (inner ℂ w (KPContActualSectorTestEmbeddings.iota f)) =
          c * ∫ p in A.carrier, (density F p : ℂ) *
            restriction F ζ hζ U R P H i x O m A hA w p * star (φ p)) ∧
      (∀ v : (KPContActualSectorFriedrichsSynthesis.A_U
          F ζ hζ U R P H μG hμG hR realization).closure.domain,
        ∀ ξ : IntegerSobolev A 1,
        KPContLocalEnergy.value ξ =
          restriction F ζ hζ U R P H i x O m A hA v.val →
        star (closedGradientForm
          (KPContActualSectorFriedrichsSynthesis.A_U
            F ζ hζ U R P H μG hμG hR realization) v
          (KPContActualSectorFriedrichsSynthesis.formTest
            F ζ hζ U R P H μG hμG hR realization f)) =
          c * ∫ p in A.carrier, (density F p : ℂ) *
            ∑ j : Fin (KPCuspLogShape.dimension F * 3),
              (((if (finProdFinEquiv.symm j).2 = 2 then 1 else
                Real.exp (2 * (coordinates F p (finProdFinEquiv.symm j).1).2)) : ℝ) : ℂ) *
                KPContLocalEnergy.gradient ξ j p *
                star (coordinateDerivativeList [j] (fun q => φ q) p)) := by
  letI : Finite (MulAction.stabilizer (Component F ζ hζ U R P H i) x) := chart_stabilizer_finite F ζ hζ U R P H i x O
  letI := Fintype.ofFinite (MulAction.stabilizer (Component F ζ hζ U R P H i) x)
  dsimp only
  intro φ
  obtain ⟨a,hai,hax,haA,haO,f,hfc,hfs⟩ := projected_test_in_shrinking μG hμG hR realization i x O m A hA φ
  have hsbase : scalarSupport f.val ⊆ baseChartImage F ζ hζ U R P H i x O := by
    intro z hz
    obtain ⟨y,hy⟩ := hfs hz
    refine ⟨Quotient.mk _ y.val, ⟨y.val, haO y.property, rfl⟩, ?_⟩
    subst i
    simp only [ShrunkChart.toBase, (H.atlas U).components_formula] at hy ⊢
    exact hy
  refine ⟨f,hfc,hsbase,?_,?_⟩
  · intro w
    exact projected_scalar_pairing μG hμG hR realization i x O m A hA φ f hfc hsbase w
  · intro v ξ hξ
    obtain ⟨ε,hε⟩ := QuotientGroup.mk'_surjective (centralLevel F ζ hζ U) m
    have hl := kp_cont_actual_sector_form_weak_localization F ζ hζ μG hμG U R hR P H realization
    obtain ⟨s,W,hs,hW,hweak⟩ := hl.closed_gradient v
    have hsξ : (fun p => KPContLocalEnergy.value ξ p) =ᵐ[volume.restrict A.carrier]
        (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (s.val a.component).val (coordinates F p)) := by
      let b := (borelS F ζ hζ U R P H).symm s
      have hb : scalarEmbedding F ζ hζ U R P H b = v.val := by
        apply (sectorLineIsometry F ζ hζ U R P H).injective
        change (sectorLineIsometry F ζ hζ U R P H) ((toSector F ζ hζ U R P H) ((borelS F ζ hζ U R P H) b)) = _
        rw [sectorLineIsometry_toSector]
        simpa only [b, LinearEquiv.apply_symm_apply] using hs.symm
      have ht := restriction_representative F ζ hζ U R P H i x O m A hA v.val b hb
      have he : frameCoefficient F ζ hζ U R P H b.val i m =
          (fun p => (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * (s.val a.component).val (coordinates F p)) := by
        rw [← hε]
        funext p
        change frameCoefficient F ζ hζ U R P H b.val i (phaseClass F ζ hζ U ε) p = _
        rw [frameCoefficient_class]
        have hbS : (KPContSectorScalarLineAlgebra.S F ζ hζ U R P H) b.val = s.val := by
          exact congrArg Subtype.val ((borelS F ζ hζ U R P H).apply_symm_apply s)
        rw [hbS,hai]
        rw [← chi_coe]
      rw [he] at ht
      rw [hξ]
      exact ht
    have hdecode := KPContFriedrichsWeakGradientCoordinates.coordinate_weak_gradient_decode s W.val hweak a A haA ε ξ hsξ
    have hgrad := test_gradient_class μG hμG hR realization f
    have hform := (hl.form_integral v (KPContActualSectorFriedrichsSynthesis.formTest F ζ hζ U R P H μG hμG hR realization f)
      W (cotangentSquareFamily (D_U f)) hW hgrad).2
    letI : Finite a.Isotropy := chart_stabilizer_finite F ζ hζ U R P H a.component a.center a.larger
    letI : Fintype a.Isotropy := Fintype.ofFinite a.Isotropy
    have hft : ∀ p, coordinates F p ∈ a.domain →
        frameCoefficient F ζ hζ U R P H (scalarCovered f) a.component (phaseClass F ζ hζ U ε) p =
          reynolds a.component a.center φ p := by
      intro p hp
      have hh := hfc p (haO hp)
      subst i
      subst x
      rw [← hε] at hh
      change frameCoefficient F ζ hζ U R P H (scalarCovered f) a.component (phaseClass F ζ hζ U ε) p = _ at hh
      convert hh using 1
    have hp := tensor_test_pairing μG hμG hR realization a A haA ε W φ f hft hfs
    rw [hform]
    change star (∫ b, pair W.val (D_U f).val b ∂KPContActualSectorCotangentL2.muU F ζ hζ U R P) = _
    rw [hp]
    have hc : (((H.disintegration U).componentWeight a.component / (Nat.card a.Isotropy : ℝ≥0∞)).toReal : ℂ) =
        (((H.disintegration U).componentWeight i / (isotropyOrder F ζ hζ U R P H i x : ℝ≥0∞)).toReal : ℂ) := by
      subst i
      subst x
      rfl
    rw [hc]
    congr 1
    apply integral_congr_ae
    have hdall : ∀ᵐ p ∂volume.restrict A.carrier, ∀ j, KPContLocalEnergy.gradient ξ j p =
        (KPCuspGenuineMonodromy.chi F ζ hζ ε : ℂ) * cotangentDecode (ζ := ζ) (hζ := hζ) p
          (liftExtension a (coefficient W.val a) (labeledAInv (placeEquiv F ζ hζ) (coordinates F p))) j := by
      exact (ae_all_iff).mpr hdecode
    filter_upwards [hdall] with p hp
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [hp j,← chi_coe]
    simp only [apply_ite,Complex.ofReal_one]

end DedekindZetaZeroFree.KPContFriedrichsChartProjectedPairings

end
