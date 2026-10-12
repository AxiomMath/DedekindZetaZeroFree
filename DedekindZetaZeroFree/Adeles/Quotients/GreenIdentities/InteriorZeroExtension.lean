module

public import DedekindZetaZeroFree.Metaplectic.Cubic.OrbifoldCharts.FinitePartitionsOfUnity
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.DifferentialAndCodifferential
public import DedekindZetaZeroFree.Metaplectic.Cubic.GenuineSector.TestL2Embeddings

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualGlobalGreen

open KPContActualCotangentCountableShrinking
open KPContActualSectorTestDifferentialDescent
open KPContActualSectorSmoothTestModules
open KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem continuous_labeledA_actual :
    Continuous (labeledA (placeEquiv F ζ hζ) : M F → KPCuspGenuineMonodromy.SymmetricSpace F) := by
  apply continuous_pi
  intro k
  have h : (fun x : M F => labeledA (placeEquiv F ζ hζ) x k)
      = fun x => ((((x ((placeEquiv F ζ hζ).symm k, 0)) : ℂ) + Complex.I *
          ((x ((placeEquiv F ζ hζ).symm k, 1)) : ℂ), x ((placeEquiv F ζ hζ).symm k, 2)) :
            ℂ × ℝ) := by
    funext x
    simp only [labeledA, CotangentLogCoframe.A_apply]
  rw [h]
  fun_prop

theorem isOpen_omega_actual (a : ShrunkChart F ζ hζ U R P H) : IsOpen (omega a) :=
  a.domain_open.preimage continuous_labeledA_actual

theorem interior_liftExtension_contDiff {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (a : ShrunkChart F ζ hζ U R P H) (f : omega a → W)
    (hf : SmoothOnLift a f) (hs : tsupport (liftExtension a f) ⊆ omega a) :
    ContDiff ℝ ∞ (liftExtension a f) := by
  obtain ⟨g, hg, hge⟩ := hf
  have hfun : liftExtension a f = fun x => if x ∈ omega a then g x else 0 := by
    funext x
    by_cases hx : x ∈ omega a
    · have h1 : f ⟨x, hx⟩ = g x := (hge ⟨x, hx⟩).symm
      simp [liftExtension, hx, h1]
    · simp [liftExtension, hx]
  rw [hfun]
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ omega a
  · have h1 : ContDiffAt ℝ ∞ g x := hg.contDiffAt ((isOpen_omega_actual a).mem_nhds hx)
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_omega_actual a).mem_nhds hx] with y hy
    simp only [hy, if_true]
  · have hx' : x ∉ tsupport (liftExtension a f) := fun h => hx (hs h)
    have hzero : ∀ y ∈ (tsupport (liftExtension a f))ᶜ, liftExtension a f y = 0 := by
      intro y hy
      by_contra h
      exact hy (subset_tsupport _ h)
    apply (contDiffAt_const (c := (0 : W))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hx'] with y hy
    simp only [Set.mem_compl_iff] at hy
    change (fun x => if x ∈ omega a then g x else 0) y = 0
    rw [← hfun]
    exact hzero y hy

end DedekindZetaZeroFree.KPContActualGlobalGreen

end
