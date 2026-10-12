module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Haar.SphericalSectorRealization

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualCompactSectorL2Map

open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)

structure CompactDomain where
  compact : TopologicalSpace.Compacts (CoveredSpherical F ζ hζ U)
  measurable : MeasurableSet (compact : Set (CoveredSpherical F ζ hζ U))
  finite_measure : coveredMeasure F ζ hζ R U compact < ⊤
  central_invariant : ∀ (ε : rootsOfUnity 3 F) (x : CoveredSpherical F ζ hζ U),
    x ∈ compact ↔ z F ζ hζ U ε x ∈ compact

variable (L : CompactDomain F ζ hζ U R)

def E_L : Submodule ℂ C(L.compact, ℂ) where
  carrier := {g | ∀ (ε : rootsOfUnity 3 F) (x : L.compact),
    g ⟨z F ζ hζ U ε x.val, (L.central_invariant ε x.val).mp x.property⟩ =
      (chi F ζ hζ ε : ℂ) * g x}
  zero_mem' := by intro ε x; simp
  add_mem' := by
    intro f g hf hg ε x
    simp only [ContinuousMap.add_apply, hf ε x, hg ε x]
    ring
  smul_mem' := by
    intro c f hf ε x
    simp only [ContinuousMap.smul_apply, smul_eq_mul, hf ε x]
    ring

def zeroExtension (g : E_L F ζ hζ U R L) : CoveredSpherical F ζ hζ U → ℂ :=
  fun x => if hx : x ∈ L.compact then g.val ⟨x, hx⟩ else 0

 theorem extension_measurable (g : E_L F ζ hζ U R L) :
    Measurable (zeroExtension F ζ hζ U R L g) := by
  exact Measurable.dite g.val.continuous.measurable measurable_const L.measurable

private theorem extension_bound (g : E_L F ζ hζ U R L) (x : CoveredSpherical F ζ hζ U) :
    ‖zeroExtension F ζ hζ U R L g x‖ ≤
      ‖(L.compact : Set (CoveredSpherical F ζ hζ U)).indicator (fun _ => (‖g‖ : ℝ)) x‖ := by
  by_cases hx : x ∈ L.compact
  · simp only [zeroExtension, dif_pos hx, Set.indicator_of_mem hx, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg g)]
    exact g.val.norm_coe_le_norm ⟨x, hx⟩
  · simp only [zeroExtension, dif_neg hx, Set.indicator_of_notMem hx, norm_zero, le_refl]

 theorem extension_memLp (g : E_L F ζ hζ U R L) :
    MemLp (zeroExtension F ζ hζ U R L g) 2 (coveredMeasure F ζ hζ R U) := by
  exact (memLp_indicator_const 2 L.measurable.nullMeasurableSet (‖g‖ : ℝ)
    (Or.inr L.finite_measure.ne)).of_le
    (extension_measurable F ζ hζ U R L g).aestronglyMeasurable
    (Filter.Eventually.of_forall (extension_bound F ζ hζ U R L g))

 theorem extension_genuine (g : E_L F ζ hζ U R L)
    (ε : rootsOfUnity 3 F) (x : CoveredSpherical F ζ hζ U) :
    zeroExtension F ζ hζ U R L g (z F ζ hζ U ε x) =
      (chi F ζ hζ ε : ℂ) * zeroExtension F ζ hζ U R L g x := by
  by_cases hx : x ∈ L.compact
  · have hz := (L.central_invariant ε x).mp hx
    simpa only [zeroExtension, dif_pos hx, dif_pos hz] using g.property ε ⟨x, hx⟩
  · have hz : z F ζ hζ U ε x ∉ L.compact :=
      fun h => hx ((L.central_invariant ε x).mpr h)
    simp only [zeroExtension, dif_neg hx, dif_neg hz, mul_zero]

private theorem extension_norm (g : E_L F ζ hζ U R L) :
    ‖(extension_memLp F ζ hζ U R L g).toLp (zeroExtension F ζ hζ U R L g)‖ ≤
      Real.sqrt ((coveredMeasure F ζ hζ R U).real L.compact) * ‖g‖ := by
  let c : Lp ℝ 2 (coveredMeasure F ζ hζ R U) :=
    indicatorConstLp 2 L.measurable L.finite_measure.ne ‖g‖
  have h : ‖(extension_memLp F ζ hζ U R L g).toLp
      (zeroExtension F ζ hζ U R L g)‖ ≤ ‖c‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(extension_memLp F ζ hζ U R L g).coeFn_toLp,
      indicatorConstLp_coeFn (E := ℝ) (p := 2) (hs := L.measurable)
        (hμs := L.finite_measure.ne) (c := ‖g‖)]
      with x hx hc
    rw [hx, hc]
    exact extension_bound F ζ hζ U R L g x
  refine h.trans_eq ?_
  change ‖indicatorConstLp 2 L.measurable L.finite_measure.ne (‖g‖ : ℝ)‖ = _
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg g), ENNReal.toReal_ofNat]
  rw [Real.sqrt_eq_rpow, mul_comm]

 def extensionBorel : E_L F ζ hζ U R L →ₗ[ℂ]
    KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R where
  toFun g := ⟨⟨zeroExtension F ζ hζ U R L g, extension_genuine F ζ hζ U R L g⟩,
    extension_measurable F ζ hζ U R L g, extension_memLp F ζ hζ U R L g⟩
  map_add' f g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ L.compact
    · simp only [zeroExtension, dif_pos hx, Submodule.coe_add, Pi.add_apply,
        ContinuousMap.add_apply]
    · simp only [zeroExtension, dif_neg hx, Submodule.coe_add, Pi.add_apply, add_zero]
  map_smul' c g := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ L.compact
    · simp only [zeroExtension, dif_pos hx, Submodule.coe_smul, Pi.smul_apply,
        ContinuousMap.smul_apply, RingHom.id_apply]
    · simp only [zeroExtension, dif_neg hx, Submodule.coe_smul, Pi.smul_apply, smul_zero]

end DedekindZetaZeroFree.KPContActualCompactSectorL2Map

namespace DedekindZetaZeroFree

open KPContSectorCoveredQuotientVocabulary KPContSectorFixedPushforwardSupport
open KPContSectorScalarLineAlgebra KPContSectorSmoothFramesSupport
open KPContActualCompactSectorL2Map

theorem kp_cont_actual_compact_sector_l2_map
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (U : KPMsFixedHaarDisintegration.Level F ζ hζ)
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)
    (_realization : KPContActualFixedSectorRealization.LevelRealization F ζ hζ U R P H)
    (L : CompactDomain F ζ hζ U R) :
    ∃ J_L : E_L F ζ hζ U R L →L[ℂ] KPContSectorClosedLpSubspace.H F ζ hζ R U,
      ‖J_L‖ ≤ Real.sqrt ((coveredMeasure F ζ hζ R U).real L.compact) ∧
      ∀ g : E_L F ζ hζ U R L,
        Measurable (zeroExtension F ζ hζ U R L g) ∧
        MemLp (zeroExtension F ζ hζ U R L g) 2 (coveredMeasure F ζ hζ R U) ∧
        (((J_L g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) :
          CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U]
            zeroExtension F ζ hζ U R L g) ∧
        ‖J_L g‖ ≤ Real.sqrt ((coveredMeasure F ζ hζ R U).real L.compact) * ‖g‖ ∧
        ∃ f : KPContSectorLineL2Isometry.BorelL2Scalars F ζ hζ U R,
          f.val.val = zeroExtension F ζ hζ U R L g ∧
          (J_L g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
            f.property.2.toLp f.val.val ∧
          KPContSectorLineL2Isometry.sectorLineIsometry F ζ hζ U R P H (J_L g) =
            KPContSectorLineL2Isometry.mk F ζ hζ U R P H
              (KPContSectorLineL2Isometry.borelS F ζ hζ U R P H f) ∧
          KPContSectorFixedLineNormIntegrals.NormIdentities F ζ hζ U R P H f.val ∧
          (∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F),
            (liftFrame F ζ hζ U x
              (liftCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f.val) i x) : ℂ) =
            zeroExtension F ζ hζ U R L g (Quotient.mk (coveredRelation F ζ hζ U)
              (x, (H.atlas U).representative i))) ∧
          (∀ (i : Fin (H.atlas U).componentCount) (x : SymmetricSpace F)
              (O : KPContSectorPhaseComponentCharts.OrbifoldChart F ζ hζ U R P H i x)
              (m : KPContSectorPhaseComponentCharts.PhaseSheets F ζ hζ U)
              (y : O.neighborhood),
            (phaseCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f.val) i m y.val : ℂ) =
            zeroExtension F ζ hζ U R L g
              (KPContSectorPhaseComponentCharts.coveredChart F ζ hζ U R P H i x O
                (Quotient.mk _ (m,y))).val) ∧
          (∀ (i : Fin (H.atlas U).componentCount)
              (j : Fin ((H.atlas U).cuspAtlas i).cuspCount) (p : KPCuspCharts.Coordinates F),
            (cuspCoefficient F ζ hζ U R P H (S F ζ hζ U R P H f.val) i j p : ℂ) =
            zeroExtension F ζ hζ U R L g (Quotient.mk (coveredRelation F ζ hζ U)
              (cuspPoint F ζ hζ U R P H i j p, (H.atlas U).representative i))) := by
  let A : E_L F ζ hζ U R L →ₗ[ℂ] KPContSectorClosedLpSubspace.H F ζ hζ R U :=
    (KPContSectorLineL2Isometry.scalarEmbedding F ζ hζ U R P H).comp
      (extensionBorel F ζ hζ U R L)
  have hA (g : E_L F ζ hζ U R L) :
      (A g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) =
        (extension_memLp F ζ hζ U R L g).toLp (zeroExtension F ζ hζ U R L g) :=
    KPContSectorLineL2Isometry.scalarEmbedding_coe F ζ hζ U R P H _
  have hb (g : E_L F ζ hζ U R L) :
      ‖A g‖ ≤ Real.sqrt ((coveredMeasure F ζ hζ R U).real L.compact) * ‖g‖ := by
    change ‖(A g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U)‖ ≤ _
    rw [hA]
    exact extension_norm F ζ hζ U R L g
  let J := A.mkContinuous (Real.sqrt ((coveredMeasure F ζ hζ R U).real L.compact)) hb
  refine ⟨J, LinearMap.mkContinuous_norm_le A (Real.sqrt_nonneg _) hb, ?_⟩
  intro g
  refine ⟨extension_measurable F ζ hζ U R L g, extension_memLp F ζ hζ U R L g,
    ?_, hb g, extensionBorel F ζ hζ U R L g, rfl, hA g, ?_, ?_, ?_, ?_, ?_⟩
  · change ((A g : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R U) :
      CoveredSpherical F ζ hζ U → ℂ) =ᵐ[coveredMeasure F ζ hζ R U] _
    rw [hA]
    exact (extension_memLp F ζ hζ U R L g).coeFn_toLp
  · exact KPContSectorLineL2Isometry.sectorLineIsometry_representative
      F ζ hζ U R P H (J g) (extensionBorel F ζ hζ U R L g) (hA g).symm
  · exact _realization.norm_integrals _ (extension_measurable F ζ hζ U R L g)
  · intro i x
    change (S F ζ hζ U R P H (extensionBorel F ζ hζ U R L g).val i).val x = _
    exact S_apply F ζ hζ U R P H _ i x
  · intro i x O m y
    exact (_realization.chart_restriction (extensionBorel F ζ hζ U R L g).val i x O m y).symm
  · intro i j p
    change (S F ζ hζ U R P H (extensionBorel F ζ hζ U R L g).val i).val
      (cuspPoint F ζ hζ U R P H i j p) = _
    exact S_apply F ζ hζ U R P H _ i _

end DedekindZetaZeroFree

end
