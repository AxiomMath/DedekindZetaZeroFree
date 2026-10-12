module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteCuspAtlas
public import DedekindZetaZeroFree.Analysis.QuadraticForms.TestDifferentialFriedrichsLaplacian

@[expose] public section

set_option maxHeartbeats 400000
noncomputable section
open scoped Classical NumberField
open MeasureTheory Filter
namespace DedekindZetaZeroFree.KPCuspCutoffGraphApproximation
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
  (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
  (U : CompactOpenLevel (KPFiniteCuspAtlas.FiniteCover F ζ hζ))

abbrev Fiber := KPCuspGenuineMonodromy.scalarFiber F ζ hζ U
abbrev Coordinates := HyperbolicChart.Space (KPCuspLogShape.dimension F)
abbrev Arch := KPFiniteCuspAtlas.SymmetricSpace F

def toArch (p : Coordinates F) : Arch F :=
  fun i => (⟨p (i,0), p (i,1)⟩, p (i,2))

def fromArch (x : Arch F) : Coordinates F :=
  WithLp.toLp 2 (fun ik => ![(x ik.1).1.re, (x ik.1).1.im, (x ik.1).2] ik.2)

abbrev Cotangent := PiLp 2 (fun _ : Fin (KPCuspLogShape.dimension F) × Fin 3 =>
  Fiber F ζ hζ U)

variable (a : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Sections := ∀ i : Fin a.componentCount,
  KPCuspGenuineMonodromy.sections F ζ hζ U (a.representative i) (a.line i).rho

def basePoint (i : Fin a.componentCount) (x : Arch F) : KPFiniteCuspAtlas.rawXU F ζ hζ U :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i)
    (KPCuspSiegel.projection F _ x)

def IsCompactlySupported (s : Sections F ζ hζ hF U a) : Prop :=
  ∃ K : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U), IsCompact K ∧
    ∀ i x, basePoint F ζ hζ hF U a i x ∉ K → (s i).val x = 0

def IsSmooth (s : Sections F ζ hζ hF U a) : Prop :=
  ∀ i, ContDiff ℝ (⊤ : ℕ∞) (s i).val

def scalarTests : Submodule ℂ (Sections F ζ hζ hF U a) where
  carrier := {s | IsSmooth F ζ hζ hF U a s ∧ IsCompactlySupported F ζ hζ hF U a s}
  zero_mem' := by
    refine ⟨fun i => contDiff_const, ∅, isCompact_empty, ?_⟩
    intro i x hx
    rfl
  add_mem' := by
    rintro s t ⟨hs, K, hK, hsK⟩ ⟨ht, L, hL, htL⟩
    refine ⟨fun i => (hs i).add (ht i), K ∪ L, hK.union hL, ?_⟩
    intro i x hx
    simp only [Set.mem_union, not_or] at hx
    change (s i).val x + (t i).val x = 0
    rw [hsK i x hx.1, htL i x hx.2, add_zero]
  smul_mem' := by
    rintro c s ⟨hs, K, hK, hsK⟩
    refine ⟨fun i => (hs i).const_smul c, K, hK, ?_⟩
    intro i x hx
    change c • (s i).val x = 0
    rw [hsK i x hx, smul_zero]

def smoothSections : Submodule ℂ (Sections F ζ hζ hF U a) where
  carrier := {s | IsSmooth F ζ hζ hF U a s}
  zero_mem' := by exact fun i => contDiff_const
  add_mem' := by intro s t hs ht; exact fun i => (hs i).add (ht i)
  smul_mem' := by intro c s hs; exact fun i => (hs i).const_smul c

def highEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      KPFiniteCuspAtlas.endSet F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i))
        ((a.cuspAtlas i).representative c) T

def closedHighEnds (T : ℝ) : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  ⋃ i : Fin a.componentCount, ⋃ c : Fin (a.cuspAtlas i).cuspCount,
    KPFiniteCuspAtlas.componentMap F ζ hζ U (a.representative i) ''
      (KPCuspSiegel.projection F
        (KPCuspGenuineMonodromy.Component F ζ hζ U (a.representative i)) ''
        (KPCuspSiegel.action F ((a.cuspAtlas i).representative c) ''
          {x | T ≤ KPCuspLogShape.meanHeight (KPCuspLogShape.dimension F) x}))

def core : Set (KPFiniteCuspAtlas.rawXU F ζ hζ U) :=
  Set.univ \ highEnds F ζ hζ hF U a a.threshold

def scalarLift (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ) (i : Fin a.componentCount) :
    Coordinates F → ℂ :=
  fun p => (r (basePoint F ζ hζ hF U a i (toArch F p)) : ℂ)

def scalarGradientNorm (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℝ :=
  Real.sqrt (∑ j : Fin (KPCuspLogShape.dimension F), ∑ k : Fin 3,
    ‖HyperbolicChart.differential (KPCuspLogShape.dimension F)
      (scalarLift F ζ hζ hF U a r i) (fromArch F x) j k‖ ^ 2)

def scalarLaplacian (r : KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ)
    (i : Fin a.componentCount) (x : Arch F) : ℂ :=
  HyperbolicChart.laplacian (KPCuspLogShape.dimension F)
    (scalarLift F ζ hζ hF U a r i) (fromArch F x)

structure Cutoffs where
  rho : ℕ → KPFiniteCuspAtlas.rawXU F ζ hζ U → ℝ
  smooth : ∀ n i, ContDiff ℝ (⊤ : ℕ∞)
    (fun x : Arch F => rho n (basePoint F ζ hζ hF U a i x))
  compact_support : ∀ n, HasCompactSupport (rho n)
  nonnegative : ∀ n x, 0 ≤ rho n x
  le_one : ∀ n x, rho n x ≤ 1

  height_bound : ℕ
  above_atlas_threshold : a.threshold < (height_bound : ℝ)
  on_core : ∀ n, height_bound ≤ n → ∀ x ∈ core F ζ hζ hF U a, rho n x = 1
  on_sublevel : ∀ n, height_bound ≤ n →
    ∀ x ∉ highEnds F ζ hζ hF U a n, rho n x = 1
  above_next : ∀ n, height_bound ≤ n →
    ∀ x ∈ closedHighEnds F ζ hζ hF U a (n+1), rho n x = 0
  bound : ℝ
  bound_nonnegative : 0 ≤ bound
  derivative_bound : ∀ n i x,
    scalarGradientNorm F ζ hζ hF U a (rho n) i x +
      ‖scalarLaplacian F ζ hζ hF U a (rho n) i x‖ ≤ bound

end DedekindZetaZeroFree.KPCuspCutoffGraphApproximation

end
