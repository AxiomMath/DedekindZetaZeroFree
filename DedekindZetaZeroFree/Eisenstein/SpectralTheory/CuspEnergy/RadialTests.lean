module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas
public import DedekindZetaZeroFree.Geometry.Hyperbolic.Laplacian.ChartGreenIdentities

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical ENNReal

namespace DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
    {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
    {S : Subgroup (KPCuspArithmetic.PGL2 F)} {D : KPCuspCharts.ParabolicData F S}
    {ρ : S →* rootsOfUnity 3 F} {V : Submodule ℂ ℂ}

structure Representative (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (ρ : S →* rootsOfUnity 3 F)
    (V : Submodule ℂ ℂ) (T : ℝ) where
  val : KPArch.Space (KPCuspLogShape.dimension F) → ℂ
  smooth : ContDiffOn ℝ (⊤ : ℕ∞) val
    {x | T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x}
  fiber : ∀ x, T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x → val x ∈ V
  equivariant : ∀ (s : S) x,
    T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x →
    val (KPCuspSiegel.action F (s : KPCuspArithmetic.PGL2 F) x) =
      (KPCuspGenuineMonodromy.chi F ζ hζ (ρ s) : ℂ) * val x

def arch (d : ℕ) (p : HyperbolicChart.Space d) : KPArch.Space d :=
  fun i => (⟨p (i, 0), p (i, 1)⟩, p (i, 2))

def real (d : ℕ) (p : KPArch.Space d) : HyperbolicChart.Space d :=
  WithLp.toLp 2 (fun j => ![(p j.1).1.re, (p j.1).1.im, (p j.1).2] j.2)

namespace Representative
variable {T : ℝ} (v : Representative ζ hζ S ρ V T)

def scalar (p : KPCuspCharts.Coordinates F) : ℂ := v.val (KPCuspCharts.toArch F p)

def gradientSq (p : KPCuspCharts.Coordinates F) : ℝ :=
  let w := HyperbolicChart.differential (KPCuspLogShape.dimension F)
    (v.val ∘ arch (KPCuspLogShape.dimension F))
    (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))
  ∑ i, ∑ k, ‖w i k‖ ^ 2

def laplacian (p : KPCuspCharts.Coordinates F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    (v.val ∘ arch (KPCuspLogShape.dimension F))
    (real (KPCuspLogShape.dimension F) (KPCuspCharts.toArch F p))

def horizontalSlice (G : KPCuspCharts.ChartOutput F hF S D)
    (b : KPCuspCharts.Shape F) (t : Set.Ioi T) :
    KPCuspGenuineMonodromy.horizontalSections (ζ := ζ) (hζ := hζ) S D ρ V :=
  ⟨fun y => v.scalar ((y,b),t.val), by
    constructor
    · intro y
      apply v.fiber
      rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
      exact t.property
    · intro x y
      have hh : T < KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F)
          (KPCuspCharts.toArch F ((y,b),t.val)) := by
        rw [KPCuspCharts.toArch_meanHeight F G.positive_dimension]
        exact t.property
      simpa only [scalar, G.unipotent_action] using
        v.equivariant (D.inclusion (Multiplicative.ofAdd x))
          (KPCuspCharts.toArch F ((y,b),t.val)) hh⟩

def torusSlice (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V)
    (b : KPCuspCharts.Shape F) (t : Set.Ioi T) :
    KPCuspGenuineMonodromy.KernelTorus S D ρ → ℂ :=
  (H.realization.symm (v.horizontalSlice G b t)).val
end Representative

def chartMeasure (G : KPCuspCharts.ChartOutput F hF S D) :
    Measure (KPCuspCharts.Coordinates F) :=
  ((volume.prod G.shapeMeasure).prod
    (KPCuspCharts.radialMeasure (KPCuspLogShape.dimension F))).restrict
      {p | p.1 ∈ G.fundamentalDomain}

def CompactRadialTest (T : ℝ) (η : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ tsupport η ⊆ Set.Ioi T

structure StructuralInputs (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (D : KPCuspCharts.ParabolicData F S)
    (ρ : S →* rootsOfUnity 3 F) (V : Submodule ℂ ℂ)
    (G : KPCuspCharts.ChartOutput F hF S D)
    (H : KPCuspGenuineMonodromy.CuspOutput (ζ := ζ) (hζ := hζ) S D ρ V) where
  fiberMeasure : Measure (KPCuspGenuineMonodromy.KernelTorus S D ρ)
  fiberHaar : fiberMeasure.IsAddHaarMeasure
  fiberProbability : IsProbabilityMeasure fiberMeasure
  slice_integrable : ∀ {T : ℝ} (v : Representative ζ hζ S ρ V T) b t,
    Integrable (v.torusSlice G H b t) fiberMeasure
  compact_integrable : ∀ {T : ℝ} (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ), CompactRadialTest T η →
    Integrable (fun p => η p.2 ^ 2 * v.gradientSq p) (chartMeasure G) ∧
      Integrable (fun p => deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2) (chartMeasure G) ∧
      Integrable (fun p => Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2)
        (chartMeasure G) ∧
      Integrable (fun p => η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re)
        (chartMeasure G)
  cutoffEnergy : ∀ {T : ℝ} (v : Representative ζ hζ S ρ V T)
    (η : ℝ → ℝ), CompactRadialTest T η →
    ∃ q : ℝ, 0 ≤ q ∧
      q = (∫ p, η p.2 ^ 2 * (star (v.scalar p) * v.laplacian p).re ∂chartMeasure G) +
        (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂chartMeasure G) ∧
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂chartMeasure G) ≤
        2 * q + 2 * (KPCuspLogShape.dimension F : ℝ)⁻¹ *
          (∫ p, deriv η p.2 ^ 2 * ‖v.scalar p‖ ^ 2 ∂chartMeasure G)
  potential : ℝ
  positive_potential : 0 < potential
  meanZero_coercivity : ∀ {T : ℝ} (v : Representative ζ hζ S ρ V T),
    (∀ b t, (∫ y, v.torusSlice G H b t y ∂fiberMeasure) = 0) →
    ∀ (η : ℝ → ℝ), CompactRadialTest T η →
      potential * (∫ p, Real.exp (2 * p.2) * η p.2 ^ 2 * ‖v.scalar p‖ ^ 2
        ∂chartMeasure G) ≤
      (∫ p, η p.2 ^ 2 * v.gradientSq p ∂chartMeasure G)

end DedekindZetaZeroFree.KPMeanZeroWeightedEnergy

end
