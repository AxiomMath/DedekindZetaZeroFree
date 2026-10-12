module

public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.LogCoordinates.FirstOrderGreenIdentity
public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.FinitePartitionsOfUnity
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Archimedean.RealCoordinatesAndVolume

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContCotangentActualOverlap
open KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

def placeReindex : KPArch.Space (KPCuspLogShape.dimension F) → KPArch.Space (d F) :=
  fun z k => z ((placeEquiv F ζ hζ) k)

theorem placeReindex_apply (z : KPArch.Space (KPCuspLogShape.dimension F)) (k : Fin (d F)) :
    placeReindex (ζ := ζ) (hζ := hζ) z k = z ((placeEquiv F ζ hζ) k) := rfl

theorem placeReindex_eq :
    placeReindex (F := F) (ζ := ζ) (hζ := hζ)
      = (Equiv.piCongrLeft (fun _ : Fin (KPCuspLogShape.dimension F) => ℂ × ℝ)
          (placeEquiv F ζ hζ)).symm := by
  funext z k
  rw [placeReindex_apply]
  simp [Equiv.piCongrLeft_apply_apply]

private lemma phi_measurePreserving :
    MeasurePreserving (fun p : Fin 3 → ℝ =>
      (Complex.measurableEquivPi.symm (fun j : Fin 2 => p (Fin.castSucc j)), p 2))
      (volume : Measure (Fin 3 → ℝ)) (volume : Measure (ℂ × ℝ)) := by
  have hp := volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) (Fin.last 2)
  have hs := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin 2 → ℝ)))
  have hc := (Complex.volume_preserving_equiv_pi).symm
  have hid : MeasurePreserving (id : ℝ → ℝ) (volume : Measure ℝ) (volume : Measure ℝ) :=
    MeasurePreserving.id _
  have hcp := hc.prod hid
  have hcomp := hcp.comp (hs.comp hp)
  convert hcomp using 1
  · funext p
    simp only [Function.comp_def, MeasurableEquiv.piFinSuccAbove_apply, Prod.map_apply,
      Prod.swap_prod_mk, Prod.fst_swap, Prod.snd_swap, id_eq, Fin.removeNth_apply,
      Fin.succAbove_last, Fin.castSucc_zero, Fin.castSucc_one, Fin.last]
    congr 1 <;> rfl

private lemma curry_measurePreserving (d : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ)
      (volume : Measure (Fin d × Fin 3 → ℝ)) (volume : Measure (Fin d → Fin 3 → ℝ)) := by
  have key : (volume : Measure (Fin d × Fin 3 → ℝ)) =
      Measure.map (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ).symm
        (volume : Measure (Fin d → Fin 3 → ℝ)) := by
    rw [show (volume : Measure (Fin d × Fin 3 → ℝ)) =
        Measure.pi (fun _ : Fin d × Fin 3 => (volume : Measure ℝ)) from rfl,
      show (volume : Measure (Fin d → Fin 3 → ℝ)) =
        Measure.pi (fun _ : Fin d => Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ)))
        from rfl]
    refine Measure.pi_eq (fun s hs => ?_)
    rw [Measure.map_apply (MeasurableEquiv.curry _ _ _).symm.measurable
      (MeasurableSet.pi (Set.to_countable _) fun i _ => hs i)]
    have hpre : (MeasurableEquiv.curry (Fin d) (Fin 3) ℝ).symm ⁻¹' (Set.pi Set.univ s) =
        Set.pi Set.univ (fun i : Fin d => Set.pi Set.univ (fun j : Fin 3 => s (i, j))) := by
      ext g
      simp [MeasurableEquiv.coe_curry_symm, Function.uncurry_apply_pair, Set.mem_univ_pi]
    rw [hpre]
    simp only [Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry _ _ _).measurable, ?_⟩
  rw [key, MeasurableEquiv.map_map_symm]

private lemma A_measurePreserving (d : ℕ) :
    MeasurePreserving (CotangentLogCoframe.A d)
      (volume : Measure (HyperbolicChart.Space d)) (volume : Measure (KPArch.Space d)) := by
  have h1 : MeasurePreserving
      (MeasurableEquiv.toLp 2 ((Fin d × Fin 3) → ℝ)).symm
      (volume : Measure (HyperbolicChart.Space d))
      (volume : Measure (Fin d × Fin 3 → ℝ)) :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d × Fin 3)
  have h2 := curry_measurePreserving d
  have h3 : MeasurePreserving
      (fun (a : Fin d → Fin 3 → ℝ) (i : Fin d) =>
        (Complex.measurableEquivPi.symm (fun j : Fin 2 => a i (Fin.castSucc j)), a i 2))
      (volume : Measure (Fin d → Fin 3 → ℝ)) (volume : Measure (KPArch.Space d)) :=
    volume_preserving_pi (fun _ : Fin d => phi_measurePreserving)
  have hc := h3.comp (h2.comp h1)
  convert hc using 1
  · funext p i
    simp [CotangentLogCoframe.A_apply, Function.comp_def, mul_comm]

private lemma weighted_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {f : A → B} (hf : MeasurePreserving f μ ν)
    (ρ : B → ENNReal) (hρ : Measurable ρ) :
    Measure.map f (μ.withDensity (ρ ∘ f)) = ν.withDensity ρ := by
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  rw [← hf.map_eq]
  rw [← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs,
    lintegral_map (hρ.indicator hs) hf.measurable]
  congr 1

private lemma volumeDensity_A (d : ℕ) (p : HyperbolicChart.Space d) :
    KPArch.volumeDensity d (CotangentLogCoframe.A d p) = HyperbolicChart.density d p := by
  have he (u : ℝ) : (Real.exp u)⁻¹ ^ 2 = Real.exp (-2 * u) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; ring
  simp only [KPArch.volumeDensity, KPArch.height, HyperbolicChart.density,
    CotangentLogCoframe.A_apply, he]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

theorem map_A_volume (d : ℕ) :
    Measure.map (CotangentLogCoframe.A d) (volume : Measure (HyperbolicChart.Space d))
      = (volume : Measure (KPArch.Space d)) :=
  (A_measurePreserving d).map_eq

theorem map_A_hyperbolicVolume (d : ℕ) :
    Measure.map (CotangentLogCoframe.A d) (HyperbolicChart.measure d)
      = KPArch.hyperbolicVolume d := by
  have hmp := A_measurePreserving d
  have hρ : Measurable (fun z : KPArch.Space d => ENNReal.ofReal (KPArch.volumeDensity d z)) := by
    unfold KPArch.volumeDensity KPArch.height; fun_prop
  have hkey := weighted_map hmp
    (fun z : KPArch.Space d => ENNReal.ofReal (KPArch.volumeDensity d z)) hρ
  have hcomp : (fun p : HyperbolicChart.Space d =>
      ENNReal.ofReal (KPArch.volumeDensity d (CotangentLogCoframe.A d p))) =
      (fun p : HyperbolicChart.Space d => ENNReal.ofReal (HyperbolicChart.density d p)) := by
    funext p; rw [volumeDensity_A]
  rw [show ((fun z : KPArch.Space d => ENNReal.ofReal (KPArch.volumeDensity d z)) ∘
      ⇑(CotangentLogCoframe.A d)) =
      (fun p : HyperbolicChart.Space d => ENNReal.ofReal (HyperbolicChart.density d p))
      from hcomp] at hkey
  rw [HyperbolicChart.measure, KPArch.hyperbolicVolume]
  exact hkey

private lemma placeReindex_measurePreserving :
    MeasurePreserving (placeReindex (F := F) (ζ := ζ) (hζ := hζ))
      (volume : Measure (KPArch.Space (KPCuspLogShape.dimension F)))
      (volume : Measure (KPArch.Space (d F))) := by
  have h := volume_measurePreserving_piCongrLeft
    (α := fun _ : Fin (KPCuspLogShape.dimension F) => ℂ × ℝ) (placeEquiv F ζ hζ)
  convert h.symm using 1
  exact (placeReindex_eq (F := F) (ζ := ζ) (hζ := hζ)).symm

private lemma volumeDensity_placeReindex (z : KPArch.Space (KPCuspLogShape.dimension F)) :
    KPArch.volumeDensity (d F) (placeReindex (F := F) (ζ := ζ) (hζ := hζ) z) =
      KPArch.volumeDensity (KPCuspLogShape.dimension F) z := by
  simp only [KPArch.volumeDensity, placeReindex_apply]
  exact Equiv.prod_comp (placeEquiv F ζ hζ)
    (fun k : Fin (KPCuspLogShape.dimension F) => (KPArch.height (z k))⁻¹ ^ 2)

theorem map_placeReindex_hyperbolicVolume :
    Measure.map (placeReindex (F := F) (ζ := ζ) (hζ := hζ))
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))
      = KPArch.hyperbolicVolume (d F) := by
  have hmp := placeReindex_measurePreserving (F := F) (ζ := ζ) (hζ := hζ)
  have hρ : Measurable (fun z : KPArch.Space (d F) =>
      ENNReal.ofReal (KPArch.volumeDensity (d F) z)) := by
    unfold KPArch.volumeDensity KPArch.height; fun_prop
  have hkey := weighted_map hmp
    (fun z : KPArch.Space (d F) => ENNReal.ofReal (KPArch.volumeDensity (d F) z)) hρ
  have hcomp : ((fun z : KPArch.Space (d F) => ENNReal.ofReal (KPArch.volumeDensity (d F) z)) ∘
      placeReindex (F := F) (ζ := ζ) (hζ := hζ)) =
      (fun z : KPArch.Space (KPCuspLogShape.dimension F) =>
        ENNReal.ofReal (KPArch.volumeDensity (KPCuspLogShape.dimension F) z)) := by
    funext z
    simp only [Function.comp_apply]
    rw [volumeDensity_placeReindex]
  rw [hcomp] at hkey
  rw [KPArch.hyperbolicVolume]
  exact hkey

theorem map_labeledAInv_hyperbolicVolume :
    Measure.map (labeledAInv (placeEquiv F ζ hζ))
        (KPArch.hyperbolicVolume (KPCuspLogShape.dimension F))
      = HyperbolicChart.measure (d F) := by
  have hpre : (labeledAInv (placeEquiv F ζ hζ)) =
      (CotangentLogCoframe.A (d F)).symm ∘ (placeReindex (F := F) (ζ := ζ) (hζ := hζ)) := by
    funext z; rfl
  rw [hpre]
  rw [← Measure.map_map (CotangentLogCoframe.A (d F)).symm.continuous.measurable
    (placeReindex_measurePreserving (F := F) (ζ := ζ) (hζ := hζ)).measurable]
  rw [map_placeReindex_hyperbolicVolume]
  rw [← map_A_hyperbolicVolume]
  rw [Measure.map_map (CotangentLogCoframe.A (d F)).symm.continuous.measurable
    (CotangentLogCoframe.A (d F)).continuous.measurable]
  simp

end DedekindZetaZeroFree.KPContActualGlobalGreen

end
