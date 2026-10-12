module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CuspEnergy.CompactTestIdentities
public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree
namespace KPMeanZeroWeightedEnergy

variable (F : Type) [Field F] [NumberField F]
  (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

structure End where
  atlas : KPFiniteCuspAtlas.Atlas F ζ hζ hF U
  component : Fin atlas.componentCount
  cusp : Fin (atlas.cuspAtlas component).cuspCount

namespace End
variable {F ζ hζ hF U} (E : End F ζ hζ hF U)

abbrev componentAtlas := E.atlas.cuspAtlas E.component
abbrev representative := E.atlas.representative E.component
abbrev line := E.atlas.line E.component
abbrev arithmeticGroup := KPCuspGenuineMonodromy.Component F ζ hζ U E.representative
abbrev parabolicGroup := KPCuspArithmetic.conjugatedStabilizer F E.arithmeticGroup
  (E.componentAtlas.cusp E.cusp) (E.componentAtlas.representative E.cusp)
abbrev parabolic := E.componentAtlas.parabolic E.cusp
abbrev geometry := E.componentAtlas.geometry E.cusp
abbrev rho := E.line.rho.comp (KPCuspGenuineMonodromy.cuspInclusion F E.arithmeticGroup
  (E.componentAtlas.cusp E.cusp) (E.componentAtlas.representative E.cusp))
abbrev monodromy := E.componentAtlas.monodromy E.cusp
abbrev KernelTorus := KPCuspGenuineMonodromy.KernelTorus E.parabolicGroup E.parabolic E.rho

def measure : Measure (KPCuspCharts.Coordinates F) :=
  ((volume.prod E.geometry.shapeMeasure).prod
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
      {p | p.1 ∈ E.geometry.fundamentalDomain}

end End

def archCoordinates (d : ℕ) (p : HyperbolicChart.Space d) : KPArch.Space d :=
  fun i => (⟨p (i, 0), p (i, 1)⟩, p (i, 2))

def realCoordinates (d : ℕ) (p : KPArch.Space d) : HyperbolicChart.Space d :=
  WithLp.toLp 2 (fun j => ![(p j.1).1.re, (p j.1).1.im, (p j.1).2] j.2)

variable {F ζ hζ hF U} (E : End F ζ hζ hF U)

structure Section (T : ℝ) where
  val : KPArch.Space (KPCuspLogShape.dimension F) → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) val
    {x | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x}
  fiber : ∀ x, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x →
    val x ∈ KPCuspGenuineMonodromy.scalarFiber F ζ hζ U
  equivariant : ∀ (s : E.parabolicGroup) x,
    T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x →
    val (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (E.rho s) : ℂ) * val x

namespace Section
variable {E} {T : ℝ} (v : Section E T)

def scalar (p : KPCuspCharts.Coordinates F) : ℂ := v.val (KPCuspCharts.toArch F p)

def gradientSq (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (v.val ∘ archCoordinates (KPCuspLogShape.dimension F))
    (realCoordinates (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ k, ‖w i k‖ ^ 2

def laplacian (p : KPCuspCharts.Coordinates F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    (v.val ∘ archCoordinates (KPCuspLogShape.dimension F))
    (realCoordinates (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))

def horizontalSlice (b : KPCuspCharts.Shape F) (t : Set.Ioi T) :
    KPCuspGenuineMonodromy.horizontalSections (ζ := ζ) (hζ := hζ)
      E.parabolicGroup E.parabolic E.rho (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) :=
  ⟨fun y => v.scalar ((y,b),t.val), by
    constructor
    · intro y
      apply v.fiber
      rw [KPCuspCharts.toArch_meanHeight F E.geometry.positive_dimension]
      exact t.property
    · intro x y
      have hh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (KPCuspCharts.toArch F ((y,b),t.val)) := by
        rw [KPCuspCharts.toArch_meanHeight F E.geometry.positive_dimension]
        exact t.property
      simpa only [scalar, E.geometry.unipotent_action] using
        v.equivariant (E.parabolic.inclusion (Multiplicative.ofAdd x))
          (KPCuspCharts.toArch F ((y,b),t.val)) hh⟩

def torusSlice (b : KPCuspCharts.Shape F) (t : Set.Ioi T) : E.KernelTorus → ℂ :=
  (E.monodromy.realization.symm (v.horizontalSlice b t)).val

end Section

def forcingMass {T : ℝ} (g : Section E T) (A R : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
    ENNReal.ofReal (Real.exp (2 * A * p.2) * ‖g.scalar p‖ ^ 2) ∂E.measure

def energy {T : ℝ} (v : Section E T) (A R : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
    ENNReal.ofReal (Real.exp (2 * A * p.2) *
      (‖v.scalar p‖ ^ 2 + v.gradientSq p)) ∂E.measure

def IsCutoff (T : ℝ) (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ Set.Ioi T

def average {T : ℝ} (μ : Measure E.KernelTorus) (v : Section E T)
    (b : KPCuspCharts.Shape F) (t : Set.Ioi T) : ℂ :=
  ∫ y, v.torusSlice b t y ∂μ

def MeanZero {T : ℝ} (μ : Measure E.KernelTorus) (v : Section E T) : Prop :=
  ∀ b t, average E μ v b t = 0

structure AnalyticAdapter where
  fiberMeasure : Measure E.KernelTorus
  fiberHaar : fiberMeasure.IsAddHaarMeasure
  fiberProbability : IsProbabilityMeasure fiberMeasure
  slice_integrable : ∀ {T : ℝ} (v : Section E T) b t,
    Integrable (v.torusSlice b t) fiberMeasure

  compact_integrable : ∀ {T : ℝ} (v : Section E T) (η : ℝ → ℝ), IsCutoff T η →
    Integrable (fun p => η p.2 ^ 2 * v.gradientSq p) E.measure ∧
    Integrable (fun p => deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) E.measure ∧
    Integrable (fun p => Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) E.measure ∧
    Integrable (fun p => η p.2 ^ 2 *
      (star (v.scalar p) * v.laplacian p).re) E.measure

  cutoffEnergy : ∀ {T : ℝ} (v : Section E T) (η : ℝ → ℝ), IsCutoff T η →
    ∃ q : ℝ, 0 ≤ q ∧
      q = (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂E.measure) +
        (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) ∧
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂E.measure) ≤
        2 * q + 2 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure)
  potential : ℝ
  positive_potential : 0 < potential

  meanZero_coercivity : ∀ {T : ℝ} (v : Section E T),
    MeanZero E fiberMeasure v → ∀ (η : ℝ → ℝ), IsCutoff T η →
    potential * (∫ p, Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) ≤
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂E.measure)

theorem IsCutoff.exp_mul {T : ℝ} {η : ℝ → ℝ} (hη : IsCutoff T η)
    (b : ℝ) : IsCutoff T (fun t => Real.exp (b * t) * η t) := by
  refine ⟨((contDiff_const.mul contDiff_id).exp).mul hη.1, ?_, ?_⟩
  · exact hη.2.1.mul_left
  · exact (tsupport_mul_subset_right).trans hη.2.2

theorem cutoff_mass_integrable (D : AnalyticAdapter E) {T : ℝ}
    (v : Section E T) (η : ℝ → ℝ) (hη : IsCutoff T η) :
    Integrable (fun p => η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) E.measure := by
  have hi := (D.compact_integrable v _ (hη.exp_mul (-1))).2.2.1
  convert hi using 1
  funext p
  rw [mul_pow]
  have hexp : Real.exp (2 * p.2) * Real.exp (-1 * p.2) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  calc
    η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 = 1 * (η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) := by ring
    _ = Real.exp (2 * p.2) * (Real.exp (-1 * p.2) ^ 2 * η p.2 ^ 2) *
        ‖v.scalar p‖ ^ 2 := by
      calc
        _ = (Real.exp (2 * p.2) * Real.exp (-1 * p.2) ^ 2) *
            (η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) := by rw [hexp]
        _ = _ := by ring

theorem laplacian_pairing_bound {T : ℝ} (v g : Section E T)
    (z : ℂ) {Z : ℝ} (hz : ‖z‖ ≤ Z) (p : KPCuspCharts.Coordinates F)
    (heq : v.laplacian p - z * v.scalar p = g.scalar p) :
    (star (v.scalar p) * v.laplacian p).re ≤
      (1 / 2 : ℝ) * ‖g.scalar p‖ ^ 2 + (Z + 1 / 2) * ‖v.scalar p‖ ^ 2 := by
  have he : v.laplacian p = g.scalar p + z * v.scalar p := by
    linear_combination heq
  rw [he, mul_add, Complex.add_re]
  have hvg : (star (v.scalar p) * g.scalar p).re ≤
      ‖v.scalar p‖ * ‖g.scalar p‖ := by
    simpa only [norm_mul, norm_star] using
      Complex.re_le_norm (star (v.scalar p) * g.scalar p)
  have hvz : (star (v.scalar p) * (z * v.scalar p)).re ≤ Z * ‖v.scalar p‖ ^ 2 := by
    calc
      _ ≤ ‖star (v.scalar p) * (z * v.scalar p)‖ := Complex.re_le_norm _
      _ = ‖z‖ * ‖v.scalar p‖ ^ 2 := by rw [norm_mul, norm_mul, norm_star]; ring
      _ ≤ Z * ‖v.scalar p‖ ^ 2 := mul_le_mul_of_nonneg_right hz (sq_nonneg _)
  nlinarith [sq_nonneg (‖v.scalar p‖ - ‖g.scalar p‖)]

theorem cutoff_pairing_bound {T : ℝ} (v g : Section E T)
    (z : ℂ) {Z : ℝ} (hz : ‖z‖ ≤ Z)
    (heq : ∀ p : KPCuspCharts.Coordinates F, T < p.2 →
      v.laplacian p - z * v.scalar p = g.scalar p)
    (η : ℝ → ℝ) (hη : IsCutoff T η) (p : KPCuspCharts.Coordinates F) :
    η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ≤
      η p.2 ^ 2 * ((1 / 2 : ℝ) * ‖g.scalar p‖ ^ 2 +
        (Z + 1 / 2) * ‖v.scalar p‖ ^ 2) := by
  by_cases hp : η p.2 = 0
  · simp [hp]
  · have ht : T < p.2 := hη.2.2 (subset_tsupport η (Function.mem_support.mpr hp))
    exact mul_le_mul_of_nonneg_left (laplacian_pairing_bound E v g z hz p (heq p ht))
      (sq_nonneg _)

theorem cutoff_gradient_bound (D : AnalyticAdapter E) {T : ℝ}
    (v : Section E T) (η : ℝ → ℝ) (hη : IsCutoff T η) :
    (∫ p, η p.2 ^ 2 * v.gradientSq p ∂E.measure) ≤
      2 * (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂E.measure) +
      4 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
        (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) := by
  obtain ⟨q, _, hq, hgrad⟩ := D.cutoffEnergy v η hη
  rw [hq] at hgrad
  nlinarith

theorem cutoff_equation_energy (D : AnalyticAdapter E) {T : ℝ}
    (v g : Section E T) (z : ℂ) {Z : ℝ} (hz : ‖z‖ ≤ Z)
    (heq : ∀ p : KPCuspCharts.Coordinates F, T < p.2 →
      v.laplacian p - z * v.scalar p = g.scalar p)
    (η : ℝ → ℝ) (hη : IsCutoff T η) :
    (∫ p, η p.2 ^ 2 * v.gradientSq p ∂E.measure) ≤
      (∫ p, η p.2 ^ 2 * ‖g.scalar p‖ ^ 2 ∂E.measure) +
      (2 * Z + 1) * (∫ p, η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) +
      4 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
        (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) := by
  have hg := cutoff_mass_integrable E D g η hη
  have hv := cutoff_mass_integrable E D v η hη
  have hi := (D.compact_integrable v η hη).2.2.2
  have hsum := (hg.const_mul (1 / 2 : ℝ)).add (hv.const_mul (Z + 1 / 2))
  have hb : (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂E.measure) ≤
      (1 / 2 : ℝ) * (∫ p, η p.2 ^ 2 * ‖g.scalar p‖ ^ 2 ∂E.measure) +
      (Z + 1 / 2) * (∫ p, η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂E.measure) := by
    calc
      _ ≤ ∫ p, (1 / 2 : ℝ) * (η p.2 ^ 2 * ‖g.scalar p‖ ^ 2) +
          (Z + 1 / 2) * (η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) ∂E.measure := by
        apply integral_mono hi hsum
        intro p
        convert cutoff_pairing_bound E v g z hz heq η hη p using 1 <;>
          dsimp only [Pi.add_apply] <;> ring
      _ = _ := by rw [integral_add (hg.const_mul _) (hv.const_mul _),
          integral_const_mul, integral_const_mul]
  have hgrad := cutoff_gradient_bound E D v η hη
  nlinarith

theorem Section.gradientSq_nonneg {T : ℝ} (v : Section E T)
    (p : KPCuspCharts.Coordinates F) : 0 ≤ v.gradientSq p := by
  unfold Section.gradientSq
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_mono_radius {T : ℝ} (v : Section E T) (A : ℝ)
    {R S : ℝ} (hRS : R ≤ S) : energy E v A S ≤ energy E v A R := by
  unfold energy
  apply lintegral_mono'
  · exact Measure.restrict_mono (fun p hp => lt_of_le_of_lt hRS hp) le_rfl
  · exact le_rfl

theorem energy_tail_of_weighted_bound {T : ℝ} (v : Section E T)
    {A T1 B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : energy E v A T1 ≤ ENNReal.ofReal B)
    {R : ℝ} (hR : T1 ≤ R) :
    energy E v 0 R ≤ ENNReal.ofReal (B * Real.exp (-2 * A * R)) := by
  have hpoint (p : KPCuspCharts.Coordinates F) (hp : R < p.2) :
      ENNReal.ofReal (Real.exp (2 * 0 * p.2) *
        (‖v.scalar p‖ ^ 2 + v.gradientSq p)) ≤
      ENNReal.ofReal (Real.exp (-2 * A * R)) *
        ENNReal.ofReal (Real.exp (2 * A * p.2) *
          (‖v.scalar p‖ ^ 2 + v.gradientSq p)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← mul_assoc,
      ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    have hn : 0 ≤ ‖v.scalar p‖ ^ 2 + v.gradientSq p :=
      add_nonneg (sq_nonneg _) (v.gradientSq_nonneg E p)
    apply mul_le_mul_of_nonneg_right _ hn
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hA (sub_nonneg.mpr (le_of_lt hp))]
  have hcompare : energy E v 0 R ≤
      ENNReal.ofReal (Real.exp (-2 * A * R)) * energy E v A R := by
    unfold energy
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono_ae (ae_restrict_mem (measurableSet_lt measurable_const
      measurable_snd) |>.mono hpoint)
  calc
    energy E v 0 R ≤ ENNReal.ofReal (Real.exp (-2 * A * R)) * energy E v A R := hcompare
    _ ≤ ENNReal.ofReal (Real.exp (-2 * A * R)) * ENNReal.ofReal B :=
      mul_le_mul_right ((energy_mono_radius E v A hR).trans hbound) _
    _ = ENNReal.ofReal (B * Real.exp (-2 * A * R)) := by
      rw [mul_comm, ← ENNReal.ofReal_mul hB]

set_option maxHeartbeats 800000 in

theorem energy_le_of_compact_cutoffs (D : AnalyticAdapter E) {T : ℝ}
    (v : Section E T) (A R B : ℝ) (η : ℕ → ℝ → ℝ)
    (hη : ∀ n, IsCutoff T (η n))
    (hlimit : ∀ t : ℝ, R < t →
      Filter.Tendsto (fun n => η n t) Filter.atTop (nhds 1))
    (hbound : ∀ n,
      (∫ p, Real.exp (2 * A * p.2) * η n p.2 ^ 2 *
        (‖v.scalar p‖ ^ 2 + v.gradientSq p) ∂E.measure) ≤ B) :
    energy E v A R ≤ ENNReal.ofReal B := by
  let f : ℕ → KPCuspCharts.Coordinates F → ℝ := fun n p =>
    Real.exp (2 * A * p.2) * η n p.2 ^ 2 *
      (‖v.scalar p‖ ^ 2 + v.gradientSq p)
  have hf : ∀ n, Integrable (f n) E.measure := by
    intro n
    have hc := hη n |>.exp_mul A
    have hm := cutoff_mass_integrable E D v _ hc
    have hg := (D.compact_integrable v _ hc).1
    convert hm.add hg using 1
    funext p
    dsimp [f]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 * A * p.2) = (2 * (A * p.2)) by ring]
    ring
  have hn : ∀ n p, 0 ≤ f n p := by
    intro n p
    dsimp [f]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      (add_nonneg (sq_nonneg _) (v.gradientSq_nonneg E p))
  have hfinite : ∀ n, (∫⁻ p, ENNReal.ofReal (f n p) ∂E.measure) ≤
      ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Filter.Eventually.of_forall (hn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hmeas : MeasurableSet {p : KPCuspCharts.Coordinates F | R < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hlim : ∀ᵐ p ∂E.measure.restrict {p : KPCuspCharts.Coordinates F | R < p.2},
      Filter.liminf (fun n => ENNReal.ofReal (f n p)) Filter.atTop =
        ENNReal.ofReal (Real.exp (2 * A * p.2) *
          (‖v.scalar p‖ ^ 2 + v.gradientSq p)) := by
    filter_upwards [ae_restrict_mem hmeas] with p hp
    have ht := hlimit p.2 hp
    have hl := ((tendsto_const_nhds (x := Real.exp (2 * A * p.2))).mul (ht.pow 2)).mul
      (tendsto_const_nhds (x := ‖v.scalar p‖ ^ 2 + v.gradientSq p))
    have hl' : Filter.Tendsto (fun n => f n p) Filter.atTop
        (nhds (Real.exp (2 * A * p.2) * (‖v.scalar p‖ ^ 2 + v.gradientSq p))) := by
      simpa [f] using hl
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hl').liminf_eq
  calc
    energy E v A R = ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
        Filter.liminf (fun n => ENNReal.ofReal (f n p)) Filter.atTop ∂E.measure := by
      exact lintegral_congr_ae (hlim.mono fun _ hp => hp.symm)
    _ ≤ Filter.liminf (fun n => ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
        ENNReal.ofReal (f n p) ∂E.measure) Filter.atTop := by
      exact lintegral_liminf_le' (μ := E.measure.restrict {p : KPCuspCharts.Coordinates F | R < p.2}) (u := Filter.atTop) fun n =>
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((hf n).aestronglyMeasurable.restrict.aemeasurable)
    _ ≤ ENNReal.ofReal B := by
      apply Filter.liminf_le_of_frequently_le'
      exact (Filter.Eventually.of_forall fun n =>
        (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hfinite n)).frequently

set_option maxHeartbeats 800000 in

theorem mass_le_of_compact_cutoffs (D : AnalyticAdapter E) {T : ℝ}
    (v : Section E T) (A R B : ℝ) (η : ℕ → ℝ → ℝ)
    (hη : ∀ n, IsCutoff T (η n))
    (hlimit : ∀ t : ℝ, R < t →
      Filter.Tendsto (fun n => η n t) Filter.atTop (nhds 1))
    (hbound : ∀ n,
      (∫ p, Real.exp (2 * A * p.2) * η n p.2 ^ 2 *
        (‖v.scalar p‖ ^ 2) ∂E.measure) ≤ B) :
    forcingMass E v A R ≤ ENNReal.ofReal B := by
  let f : ℕ → KPCuspCharts.Coordinates F → ℝ := fun n p =>
    Real.exp (2 * A * p.2) * η n p.2 ^ 2 *
      (‖v.scalar p‖ ^ 2)
  have hf : ∀ n, Integrable (f n) E.measure := by
    intro n
    have hm := cutoff_mass_integrable E D v _ ((hη n).exp_mul A)
    convert hm using 1
    funext p
    dsimp [f]
    rw [mul_pow, ← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 * A * p.2) = (2 * (A * p.2)) by ring]
  have hn : ∀ n p, 0 ≤ f n p := by
    intro n p
    dsimp [f]
    exact mul_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
      (sq_nonneg _)
  have hfinite : ∀ n, (∫⁻ p, ENNReal.ofReal (f n p) ∂E.measure) ≤
      ENNReal.ofReal B := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hf n) (Filter.Eventually.of_forall (hn n))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  have hmeas : MeasurableSet {p : KPCuspCharts.Coordinates F | R < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have hlim : ∀ᵐ p ∂E.measure.restrict {p : KPCuspCharts.Coordinates F | R < p.2},
      Filter.liminf (fun n => ENNReal.ofReal (f n p)) Filter.atTop =
        ENNReal.ofReal (Real.exp (2 * A * p.2) *
          (‖v.scalar p‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem hmeas] with p hp
    have ht := hlimit p.2 hp
    have hl := ((tendsto_const_nhds (x := Real.exp (2 * A * p.2))).mul (ht.pow 2)).mul
      (tendsto_const_nhds (x := ‖v.scalar p‖ ^ 2))
    have hl' : Filter.Tendsto (fun n => f n p) Filter.atTop
        (nhds (Real.exp (2 * A * p.2) * (‖v.scalar p‖ ^ 2))) := by
      simpa [f] using hl
    exact (ENNReal.continuous_ofReal.tendsto _ |>.comp hl').liminf_eq
  calc
    forcingMass E v A R = ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
        Filter.liminf (fun n => ENNReal.ofReal (f n p)) Filter.atTop ∂E.measure := by
      exact lintegral_congr_ae (hlim.mono fun _ hp => hp.symm)
    _ ≤ Filter.liminf (fun n => ∫⁻ p in {p : KPCuspCharts.Coordinates F | R < p.2},
        ENNReal.ofReal (f n p) ∂E.measure) Filter.atTop := by
      exact lintegral_liminf_le' (μ := E.measure.restrict {p : KPCuspCharts.Coordinates F | R < p.2}) (u := Filter.atTop) fun n =>
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          ((hf n).aestronglyMeasurable.restrict.aemeasurable)
    _ ≤ ENNReal.ofReal B := by
      apply Filter.liminf_le_of_frequently_le'
      exact (Filter.Eventually.of_forall fun n =>
        (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hfinite n)).frequently

private lemma compact_integral_le_mass {T : ℝ} (v : Section E T)
    (b S B K : ℝ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (w : KPCuspCharts.Coordinates F → ℝ)
    (hw : Integrable w E.measure) (hw0 : ∀ p, 0 ≤ w p)
    (hpoint : ∀ p, w p ≤
      Set.indicator {p : KPCuspCharts.Coordinates F | S < p.2}
        (fun p => K * (Real.exp (2 * b * p.2) * ‖v.scalar p‖ ^ 2)) p)
    (hbound : forcingMass E v b S ≤ ENNReal.ofReal B) :
    (∫ p, w p ∂E.measure) ≤ K * B := by
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hB)).mp
  calc
    ENNReal.ofReal (∫ p, w p ∂E.measure)
        = ∫⁻ p, ENNReal.ofReal (w p) ∂E.measure :=
      ofReal_integral_eq_lintegral_ofReal hw (Filter.Eventually.of_forall hw0)
    _ ≤ ∫⁻ p, Set.indicator {p : KPCuspCharts.Coordinates F | S < p.2}
        (fun p => ENNReal.ofReal K *
          ENNReal.ofReal (Real.exp (2 * b * p.2) * ‖v.scalar p‖ ^ 2)) p ∂E.measure := by
      apply lintegral_mono
      intro p
      have hpt := hpoint p
      by_cases hp : p ∈ {p : KPCuspCharts.Coordinates F | S < p.2}
      · simp only [Set.indicator_of_mem hp] at hpt ⊢
        rw [← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal hpt
      · simp only [Set.indicator_of_notMem hp] at hpt ⊢
        exact ENNReal.ofReal_eq_zero.mpr hpt |>.le
    _ = ENNReal.ofReal K * forcingMass E v b S := by
      rw [lintegral_indicator (measurableSet_lt measurable_const measurable_snd),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rfl
    _ ≤ ENNReal.ofReal K * ENNReal.ofReal B := mul_le_mul_right hbound _
    _ = ENNReal.ofReal (K * B) := (ENNReal.ofReal_mul hK).symm

private theorem transition_deriv_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ t, ‖deriv Real.smoothTransition t‖ ≤ D := by
  have hc := Real.smoothTransition.contDiff.continuous_deriv (n := (⊤ : ℕ∞)) (by simp)
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · exact (hD t ht).trans (le_max_left _ _)
  · have hz : deriv Real.smoothTransition t = 0 := by
      rcases not_and_or.mp ht with ht | ht
      · have ht : t < 0 := lt_of_not_ge ht
        apply HasDerivAt.deriv
        apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
        filter_upwards [eventually_lt_nhds ht] with x hx
        exact Real.smoothTransition.zero_of_nonpos hx.le
      · have ht : 1 < t := lt_of_not_ge ht
        apply HasDerivAt.deriv
        apply (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
        filter_upwards [eventually_gt_nhds ht] with x hx
        exact Real.smoothTransition.one_of_one_le hx.le
    simp only [hz, norm_zero]
    exact le_max_right _ _

theorem exists_weighted_cutoff_family (S R b : ℝ) (hSR : S < R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ η : ℕ → ℝ → ℝ,
      (∀ n, IsCutoff S (η n)) ∧
      (∀ n t, η n t ^ 2 ≤ 1) ∧
      (∀ n t, deriv (fun t => Real.exp (b * t) * η n t) t ^ 2 ≤
        Set.indicator (Set.Ioi S) (fun t => K * Real.exp (2 * b * t)) t) ∧
      (∀ t : ℝ, R < t → Filter.Tendsto (fun n => η n t) Filter.atTop (nhds 1)) := by
  let a := (S + R) / 2
  let δ := R - a
  have ha : S < a := by dsimp [a]; linarith
  have hδ : 0 < δ := by dsimp [δ, a]; linarith
  let l : ℝ → ℝ := fun t => Real.smoothTransition ((t - a) / δ)
  let u : ℕ → ℝ → ℝ := fun n t => Real.smoothTransition ((n : ℝ) - t)
  let η : ℕ → ℝ → ℝ := fun n t => l t * u n t
  have hl : ContDiff ℝ (⊤ : ℕ∞) l :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const δ)
  have hu : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (u n) := fun n =>
    Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)
  have hη : ∀ n, IsCutoff S (η n) := by
    intro n
    have hs : Function.support (η n) ⊆ Set.Icc a (n : ℝ) := by
      intro t ht
      have ht : l t * u n t ≠ 0 := ht
      constructor
      · by_contra hh
        have hh : (t - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
        exact ht (by simp [l, Real.smoothTransition.zero_of_nonpos hh])
      · by_contra hh
        exact ht (by simp [u, Real.smoothTransition.zero_of_nonpos (show (n : ℝ) - t ≤ 0 by linarith)])
    refine ⟨hl.mul (hu n), HasCompactSupport.of_support_subset_isCompact isCompact_Icc hs, ?_⟩
    exact (closure_minimal hs isClosed_Icc).trans fun t ht => lt_of_lt_of_le ha ht.1
  have hsize : ∀ n t, η n t ^ 2 ≤ 1 := by
    intro n t
    have h0 : 0 ≤ η n t := mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
    have h1 : η n t ≤ 1 := by
      exact (mul_le_mul (Real.smoothTransition.le_one _) (Real.smoothTransition.le_one _)
        (Real.smoothTransition.nonneg _) zero_le_one).trans (by norm_num)
    nlinarith
  have hlim : ∀ t : ℝ, R < t → Filter.Tendsto (fun n => η n t) Filter.atTop (nhds 1) := by
    intro t ht
    have ht1 : l t = 1 := Real.smoothTransition.one_of_one_le (by
      apply (le_div_iff₀ hδ).mpr
      dsimp [δ]
      linarith)
    apply tendsto_const_nhds.congr'
    have hev : ∀ᶠ n : ℕ in Filter.atTop, t + 1 ≤ (n : ℝ) :=
      (tendsto_natCast_atTop_atTop.eventually_ge_atTop (t + 1))
    filter_upwards [hev] with n hn
    simp only [η, ht1, one_mul]
    symm
    exact Real.smoothTransition.one_of_one_le (x := (n : ℝ)-t) (by linarith)
  obtain ⟨D, hD0, hD⟩ := transition_deriv_bound
  let H := |b| + D / δ + D
  refine ⟨H ^ 2, sq_nonneg _, η, hη, hsize, ?_, hlim⟩
  intro n t
  have hdL : HasDerivAt l (deriv Real.smoothTransition ((t-a)/δ) / δ) t := by
    convert ((Real.smoothTransition.contDiff.differentiable (n := (⊤ : ℕ∞)) (by simp)).differentiableAt.hasDerivAt).comp t
      (((hasDerivAt_id t).sub_const a).div_const δ) using 1 <;> simp [l, Function.comp_def, div_eq_mul_inv]
  have hdU : HasDerivAt (u n) (-deriv Real.smoothTransition ((n : ℝ)-t)) t := by
    convert ((Real.smoothTransition.contDiff.differentiable (n := (⊤ : ℕ∞)) (by simp)).differentiableAt.hasDerivAt).comp t
      ((hasDerivAt_const t (n : ℝ)).sub (hasDerivAt_id t)) using 1 <;> simp [u, Function.comp_def]
  have hdE := ((hasDerivAt_id t).const_mul b).exp
  have hdη := hdL.mul hdU
  have hexp : Real.exp (b*t)^2 = Real.exp (2*b*t) := by
    rw [← Real.exp_nat_mul]; congr 1; norm_num; ring
  by_cases ht : S < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi S from ht)]
    change deriv (fun t => Real.exp (b*t) * (l t * u n t)) t ^ 2 ≤ _
    have hd := (hdE.mul hdη).deriv
    simp only [id_eq, mul_one, Pi.mul_apply] at hd
    change deriv ((fun x => Real.exp (b*x)) * (l * u n)) t ^ 2 ≤ _
    rw [hd]
    have hnL : ‖l t‖ ≤ 1 := by
      simpa only [l, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one ((t-a)/δ)
    have hnU : ‖u n t‖ ≤ 1 := by
      simpa only [u, Real.norm_eq_abs, abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one ((n : ℝ)-t)
    have hnD : ‖deriv Real.smoothTransition ((t-a)/δ) / δ * u n t + l t * -deriv Real.smoothTransition ((n : ℝ)-t)‖ ≤ D/δ + D := by
      calc
        _ ≤ ‖deriv Real.smoothTransition ((t-a)/δ) / δ‖ * ‖u n t‖ + ‖l t‖ * ‖deriv Real.smoothTransition ((n : ℝ)-t)‖ := by simpa only [norm_mul, norm_neg] using norm_add_le (deriv Real.smoothTransition ((t-a)/δ) / δ * u n t) (l t * -deriv Real.smoothTransition ((n : ℝ)-t))
        _ ≤ (D / δ) * 1 + 1 * D := by
          apply add_le_add
          · apply mul_le_mul _ hnU (norm_nonneg _) (by positivity)
            simpa only [norm_div, Real.norm_eq_abs, abs_of_pos hδ] using div_le_div_of_nonneg_right (hD ((t-a)/δ)) hδ.le
          · exact mul_le_mul hnL (hD _) (norm_nonneg _) zero_le_one
        _ = _ := by ring
    have hn : ‖Real.exp (b * t) * b * (l t * u n t) + Real.exp (b * t) * (deriv Real.smoothTransition ((t - a) / δ) / δ * u n t + l t * -deriv Real.smoothTransition ((n : ℝ)-t))‖ ≤ Real.exp (b*t) * H := by
      calc
        _ ≤ ‖Real.exp (b*t)‖ * ‖b‖ * (‖l t‖ * ‖u n t‖) + ‖Real.exp (b*t)‖ * ‖deriv Real.smoothTransition ((t - a) / δ) / δ * u n t + l t * -deriv Real.smoothTransition ((n : ℝ)-t)‖ := by simpa only [norm_mul] using norm_add_le (Real.exp (b*t) * b * (l t * u n t)) (Real.exp (b*t) * (deriv Real.smoothTransition ((t-a)/δ) / δ * u n t + l t * -deriv Real.smoothTransition ((n : ℝ)-t)))
        _ ≤ Real.exp (b*t) * |b| * (1*1) + Real.exp (b*t) * (D/δ+D) := by
          simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul hnL hnU (abs_nonneg _) zero_le_one) (by positivity)) (mul_le_mul_of_nonneg_left hnD (Real.exp_nonneg _))
        _ = _ := by dsimp [H]; ring
    have hn0 : 0 ≤ Real.exp (b*t) * H := by dsimp [H]; positivity
    have hnSq := sq_le_sq₀ (norm_nonneg _) hn0 |>.mpr hn
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow, hexp, mul_comm] using hnSq
  · have ha' : t < a := lt_of_le_of_lt (le_of_not_gt ht) ha
    have hz : (fun t => Real.exp (b * t) * η n t) =ᶠ[nhds t] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ha'] with x hx
      have hx : (x-a)/δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
      simp [η, l, Real.smoothTransition.zero_of_nonpos hx]
    rw [hz.deriv_eq, deriv_const]
    simp [Set.indicator_of_notMem (show t ∉ Set.Ioi S from ht)]

set_option maxHeartbeats 1000000 in

theorem weighted_step_from_cutoffs (D : AnalyticAdapter E) {T : ℝ}
    (v g : Section E T) (z : ℂ) (Z b S R V G K : ℝ)
    (hZ : 0 ≤ Z) (hz : ‖z‖ ≤ Z) (hTS : T ≤ S)
    (hV : 0 ≤ V) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hv0 : MeanZero E D.fiberMeasure v)
    (heq : ∀ p : KPCuspCharts.Coordinates F, T < p.2 →
      v.laplacian p - z * v.scalar p = g.scalar p)
    (hmass : forcingMass E v b S ≤ ENNReal.ofReal V)
    (hforcing : forcingMass E g b S ≤ ENNReal.ofReal G)
    (η : ℕ → ℝ → ℝ) (hη : ∀ n, IsCutoff S (η n))
    (hsize : ∀ n t, η n t ^ 2 ≤ 1)
    (hderiv : ∀ n t, deriv (fun t => Real.exp (b * t) * η n t) t ^ 2 ≤
      Set.indicator (Set.Ioi S) (fun t => K * Real.exp (2 * b * t)) t)
    (hlimit : ∀ t : ℝ, R < t →
      Filter.Tendsto (fun n => η n t) Filter.atTop (nhds 1)) :
    let Q := G + (2 * Z + 1) * V +
      4 * (KPCuspLogShape.dimension F : ℝ)⁻¹ * (K * V)
    forcingMass E v (b + 1) R ≤ ENNReal.ofReal (Q / D.potential) ∧
      energy E v b R ≤ ENNReal.ofReal (V + Q) := by
  dsimp only
  let Q := G + (2 * Z + 1) * V +
    4 * (KPCuspLogShape.dimension F : ℝ)⁻¹ * (K * V)
  have ht : ∀ n, IsCutoff T (η n) := by
    intro n
    exact ⟨(hη n).1, (hη n).2.1, fun t ht => lt_of_le_of_lt hTS ((hη n).2.2 ht)⟩
  have hexp (t : ℝ) : Real.exp (b * t) ^ 2 = Real.exp (2 * b * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hm (n : ℕ) (w : Section E T) (B : ℝ) (hB : 0 ≤ B)
      (hb : forcingMass E w b S ≤ ENNReal.ofReal B) :
      (∫ p, (Real.exp (b * p.2) * η n p.2) ^ 2 * ‖w.scalar p‖ ^ 2 ∂E.measure) ≤ B := by
    have hi := cutoff_mass_integrable E D w _ ((ht n).exp_mul b)
    simpa only [one_mul] using compact_integral_le_mass E w b S B 1 hB zero_le_one _ hi
      (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by
        intro p
        by_cases hp : S < p.2
        · rw [Set.indicator_of_mem (show p ∈ {p | S < p.2} from hp), one_mul,
            mul_pow, hexp]
          nlinarith [Real.exp_nonneg (2 * b * p.2), sq_nonneg ‖w.scalar p‖,
            mul_nonneg (Real.exp_nonneg (2 * b * p.2)) (sq_nonneg ‖w.scalar p‖), hsize n p.2]
        · have hz : η n p.2 = 0 := by
            by_contra hz
            exact hp ((hη n).2.2 (subset_tsupport _ (Function.mem_support.mpr hz)))
          simp [hz, Set.indicator_of_notMem (show p ∉ {p | S < p.2} from hp)]) hb
  have hd (n : ℕ) :
      (∫ p, deriv (fun t => Real.exp (b * t) * η n t) p.2 ^ 2 * ‖v.scalar p‖ ^ 2
        ∂E.measure) ≤ K * V := by
    apply compact_integral_le_mass E v b S V K hV hK _
      ((D.compact_integrable v _ ((ht n).exp_mul b)).2.1)
      (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)) _ hmass
    intro p
    have hh := mul_le_mul_of_nonneg_right (hderiv n p.2) (sq_nonneg ‖v.scalar p‖)
    by_cases hp : S < p.2
    · simpa only [Set.indicator_of_mem (show p.2 ∈ Set.Ioi S from hp),
        Set.indicator_of_mem (show p ∈ {p | S < p.2} from hp), mul_assoc] using hh
    · simpa only [Set.indicator_of_notMem (show p.2 ∉ Set.Ioi S from hp),
        Set.indicator_of_notMem (show p ∉ {p | S < p.2} from hp), zero_mul] using hh
  have hgrad (n : ℕ) :
      (∫ p, (Real.exp (b * p.2) * η n p.2) ^ 2 * v.gradientSq p ∂E.measure) ≤ Q := by
    have h := cutoff_equation_energy E D v g z hz heq _ ((ht n).exp_mul b)
    exact h.trans (add_le_add (add_le_add (hm n g G hG hforcing)
      (mul_le_mul_of_nonneg_left (hm n v V hV hmass) (by linarith)))
      (mul_le_mul_of_nonneg_left (hd n) (by positivity)))
  have hpot (n : ℕ) :
      (∫ p, Real.exp (2 * (b + 1) * p.2) * η n p.2 ^ 2 * ‖v.scalar p‖ ^ 2
        ∂E.measure) ≤ Q / D.potential := by
    apply (le_div_iff₀ D.positive_potential).mpr
    have h := (D.meanZero_coercivity v hv0 _ ((ht n).exp_mul b)).trans (hgrad n)
    have hx (p : KPCuspCharts.Coordinates F) :
        Real.exp (2 * p.2) * (Real.exp (b * p.2) * η n p.2) ^ 2 * ‖v.scalar p‖ ^ 2 =
        Real.exp (2 * (b + 1) * p.2) * η n p.2 ^ 2 * ‖v.scalar p‖ ^ 2 := by
      rw [mul_pow, hexp, ← mul_assoc, ← Real.exp_add]
      congr 2
      congr 1
      ring
    simpa only [hx, mul_comm D.potential] using h
  constructor
  · exact mass_le_of_compact_cutoffs E D v (b + 1) R (Q / D.potential) η ht hlimit hpot
  · apply energy_le_of_compact_cutoffs E D v b R (V + Q) η ht hlimit
    intro n
    have hmi := cutoff_mass_integrable E D v _ ((ht n).exp_mul b)
    have hgi := (D.compact_integrable v _ ((ht n).exp_mul b)).1
    have hh := add_le_add (hm n v V hV hmass) (hgrad n)
    rw [← integral_add hmi hgi] at hh
    convert hh using 1
    congr 1
    funext p
    rw [mul_pow, hexp]
    ring

theorem energy_compare_weights {T : ℝ} (v : Section E T)
    {a b R : ℝ} (hab : a ≤ b) :
    energy E v a R ≤ ENNReal.ofReal (Real.exp (2 * (a - b) * R)) * energy E v b R := by
  unfold energy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_snd)] with p hp
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← mul_assoc, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _
    (add_nonneg (sq_nonneg _) (v.gradientSq_nonneg E p))
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (le_of_lt hp))
  nlinarith

theorem mass_compare_weights {T : ℝ} (v : Section E T)
    {a b R : ℝ} (hab : a ≤ b) :
    forcingMass E v a R ≤
      ENNReal.ofReal (Real.exp (2 * (a - b) * R)) * forcingMass E v b R := by
  unfold forcingMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const measurable_snd)] with p hp
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← mul_assoc, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Real.exp_le_exp.mpr
  have h := mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr (le_of_lt hp))
  nlinarith

theorem forcing_bounds_all_real {T : ℝ} {I : Type*} (g : I → Section E T)
    (hforcing : ∀ a : ℝ, 0 ≤ a → ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
      forcingMass E (g i) a T ≤ ENNReal.ofReal B) :
    ∀ a : ℝ, ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
      forcingMass E (g i) a T ≤ ENNReal.ofReal B := by
  intro a
  by_cases ha : 0 ≤ a
  · exact hforcing a ha
  · obtain ⟨B, hB, hb⟩ := hforcing 0 le_rfl
    refine ⟨Real.exp (2 * a * T) * B, mul_nonneg (Real.exp_nonneg _) hB, ?_⟩
    intro i
    calc
      forcingMass E (g i) a T ≤
          ENNReal.ofReal (Real.exp (2 * (a - 0) * T)) * forcingMass E (g i) 0 T :=
        mass_compare_weights E (g i) (le_of_not_ge ha)
      _ ≤ ENNReal.ofReal (Real.exp (2 * (a - 0) * T)) * ENNReal.ofReal B :=
        mul_le_mul_right (hb i) _
      _ = _ := by rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]; simp

theorem bootstrap_from_uniform_mass_step {T : ℝ} {I : Type*}
    (v : I → Section E T) (b₀ : ℝ)
    (hseed : ∀ R : ℝ, T < R → ∃ V : ℝ, 0 ≤ V ∧ ∀ i,
      forcingMass E (v i) b₀ R ≤ ENNReal.ofReal V)
    (hstep : ∀ b S R : ℝ, T < S → S < R →
      (∃ V : ℝ, 0 ≤ V ∧ ∀ i, forcingMass E (v i) b S ≤ ENNReal.ofReal V) →
      (∃ V : ℝ, 0 ≤ V ∧ ∀ i, forcingMass E (v i) (b + 1) R ≤ ENNReal.ofReal V) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ i, energy E (v i) b R ≤ ENNReal.ofReal B)) :
    ∀ a R : ℝ, T < R → ∃ B : ℝ, 0 ≤ B ∧ ∀ i,
      energy E (v i) a R ≤ ENNReal.ofReal B := by
  have hm : ∀ n : ℕ, ∀ R : ℝ, T < R → ∃ V : ℝ, 0 ≤ V ∧ ∀ i,
      forcingMass E (v i) (b₀ + n) R ≤ ENNReal.ofReal V := by
    intro n
    induction n with
    | zero => simpa only [Nat.cast_zero, add_zero] using hseed
    | succ n ih =>
      intro R hR
      obtain ⟨S, hTS, hSR⟩ := exists_between hR
      have hh := (hstep (b₀ + n) S R hTS hSR (ih S hTS)).1
      simpa only [Nat.cast_add, Nat.cast_one, ← add_assoc] using hh
  intro a R hR
  obtain ⟨n, hn⟩ := exists_nat_gt (a - b₀)
  obtain ⟨S, hTS, hSR⟩ := exists_between hR
  obtain ⟨B, hB, hb⟩ := (hstep (b₀ + n) S R hTS hSR (hm n S hTS)).2
  refine ⟨Real.exp (2 * (a - (b₀ + n)) * R) * B,
    mul_nonneg (Real.exp_nonneg _) hB, ?_⟩
  intro i
  calc
    energy E (v i) a R ≤ ENNReal.ofReal (Real.exp (2 * (a - (b₀ + n)) * R)) *
        energy E (v i) (b₀ + n) R := energy_compare_weights E (v i) (by linarith)
    _ ≤ ENNReal.ofReal (Real.exp (2 * (a - (b₀ + n)) * R)) * ENNReal.ofReal B :=
      mul_le_mul_right (hb i) _
    _ = _ := (ENNReal.ofReal_mul (Real.exp_nonneg _)).symm

theorem uniform_weighted_step (D : AnalyticAdapter E) {T : ℝ} {I : Type*}
    (v g : I → Section E T) (z : I → ℂ) (Z b S R V G : ℝ)
    (hZ : 0 ≤ Z) (hz : ∀ i, ‖z i‖ ≤ Z) (hTS : T ≤ S) (hSR : S < R)
    (hV : 0 ≤ V) (hG : 0 ≤ G)
    (hv0 : ∀ i, MeanZero E D.fiberMeasure (v i))
    (heq : ∀ i p, T < p.2 → (v i).laplacian p - z i * (v i).scalar p = (g i).scalar p)
    (hmass : ∀ i, forcingMass E (v i) b S ≤ ENNReal.ofReal V)
    (hforcing : ∀ i, forcingMass E (g i) b S ≤ ENNReal.ofReal G) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ i, forcingMass E (v i) (b + 1) R ≤ ENNReal.ofReal B) ∧
      (∀ i, energy E (v i) b R ≤ ENNReal.ofReal B) := by
  obtain ⟨K, hK, η, hη, hs, hd, hl⟩ := exists_weighted_cutoff_family S R b hSR
  let Q := G + (2 * Z + 1) * V +
    4 * (KPCuspLogShape.dimension F : ℝ)⁻¹ * (K * V)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨max (Q / D.potential) (V + Q), ?_, ?_, ?_⟩
  · exact (add_nonneg hV hQ).trans (le_max_right _ _)
  · intro i
    exact (weighted_step_from_cutoffs E D (v i) (g i) (z i) Z b S R V G K
      hZ (hz i) hTS hV hG hK (hv0 i) (heq i) (hmass i) (hforcing i)
      η hη hs hd hl).1.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · intro i
    exact (weighted_step_from_cutoffs E D (v i) (g i) (z i) Z b S R V G K
      hZ (hz i) hTS hV hG hK (hv0 i) (heq i) (hmass i) (hforcing i)
      η hη hs hd hl).2.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))

theorem weighted_energy_from_mass_seed (D : AnalyticAdapter E) {T : ℝ} {I : Type*}
    (v g : I → Section E T) (z : I → ℂ) (Z b₀ : ℝ)
    (hZ : 0 ≤ Z) (hz : ∀ i, ‖z i‖ ≤ Z)
    (hv0 : ∀ i, MeanZero E D.fiberMeasure (v i))
    (heq : ∀ i p, T < p.2 → (v i).laplacian p - z i * (v i).scalar p = (g i).scalar p)
    (hseed : ∀ R : ℝ, T < R → ∃ V : ℝ, 0 ≤ V ∧ ∀ i,
      forcingMass E (v i) b₀ R ≤ ENNReal.ofReal V)
    (hforcing : ∀ a : ℝ, 0 ≤ a → ∃ G : ℝ, 0 ≤ G ∧ ∀ i,
      forcingMass E (g i) a T ≤ ENNReal.ofReal G) :
    ∀ a : ℝ, 0 ≤ a → ∀ R : ℝ, T < R → ∃ B : ℝ, 0 ≤ B ∧
      (∀ i, energy E (v i) a R ≤ ENNReal.ofReal B) ∧
      (∀ S : ℝ, R ≤ S → ∀ i,
        energy E (v i) 0 S ≤ ENNReal.ofReal (B * Real.exp (-2 * a * S))) := by
  have hg := forcing_bounds_all_real E g hforcing
  have hs : ∀ b S R : ℝ, T < S → S < R →
      (∃ V : ℝ, 0 ≤ V ∧ ∀ i, forcingMass E (v i) b S ≤ ENNReal.ofReal V) →
      (∃ V : ℝ, 0 ≤ V ∧ ∀ i, forcingMass E (v i) (b + 1) R ≤ ENNReal.ofReal V) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ i, energy E (v i) b R ≤ ENNReal.ofReal B) := by
    intro b S R hTS hSR hmass
    obtain ⟨V, hV, hv⟩ := hmass
    obtain ⟨G, hG, hb⟩ := hg b
    have hgs : ∀ i, forcingMass E (g i) b S ≤ ENNReal.ofReal G := by
      intro i
      refine le_trans ?_ (hb i)
      unfold forcingMass
      exact lintegral_mono_set (fun p hp => lt_trans hTS hp)
    obtain ⟨B, hB, hmv, hev⟩ :=
      uniform_weighted_step E D v g z Z b S R V G hZ hz hTS.le hSR hV hG hv0 heq hv hgs
    exact ⟨⟨B, hB, hmv⟩, ⟨B, hB, hev⟩⟩
  intro a ha R hR
  obtain ⟨B, hB, hb⟩ := bootstrap_from_uniform_mass_step E v b₀ hseed hs a R hR
  exact ⟨B, hB, hb, fun S hS i => energy_tail_of_weighted_bound E (v i) ha hB (hb i) hS⟩

def Section.rawRepresentative {T : ℝ} (v : Section E T) :
    KPMeanZeroWeightedEnergy.Representative ζ hζ E.parabolicGroup E.rho
      (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U) T :=
  ⟨v.val, v.smooth, v.fiber, v.equivariant⟩

def AnalyticAdapter.ofStructuralInputs
    (B : KPMeanZeroWeightedEnergy.StructuralInputs ζ hζ E.parabolicGroup
      E.parabolic E.rho (KPCuspGenuineMonodromy.scalarFiber F ζ hζ U)
      E.geometry E.monodromy) : AnalyticAdapter E where
  fiberMeasure := B.fiberMeasure
  fiberHaar := B.fiberHaar
  fiberProbability := B.fiberProbability
  slice_integrable := fun v b t => B.slice_integrable (v.rawRepresentative E) b t
  compact_integrable := fun v η hη => B.compact_integrable (v.rawRepresentative E) η hη
  cutoffEnergy := fun v η hη => B.cutoffEnergy (v.rawRepresentative E) η hη
  potential := B.potential
  positive_potential := B.positive_potential
  meanZero_coercivity := fun v hv η hη =>
    B.meanZero_coercivity (v.rawRepresentative E) hv η hη

end KPMeanZeroWeightedEnergy

theorem kp_cont_mean_zero_weighted_energy_adapter
    {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ)}
    (E : KPMeanZeroWeightedEnergy.End F ζ hζ hF U) :
    Nonempty (KPMeanZeroWeightedEnergy.AnalyticAdapter E) := by
  obtain ⟨B⟩ := KPMeanZeroWeightedEnergy.actual_structural_inputs E.componentAtlas E.cusp
  exact ⟨KPMeanZeroWeightedEnergy.AnalyticAdapter.ofStructuralInputs E B⟩

end DedekindZetaZeroFree

end
