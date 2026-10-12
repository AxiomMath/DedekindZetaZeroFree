module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.WeakSections.ZeroExtensionFirstJetBound

@[expose] public section

noncomputable section
open scoped Classical NumberField ContDiff
open MeasureTheory Topology

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualSectorChartEquivariantInputs KPContCotangentOverlapRationalBranches
open KPContCotangentActualOverlap KPContCotangentActualGenuineTwistIsotropy KPCompactInteriorH1

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

theorem smoothChartTest_of_flat
    (a : ActualChart (U := U) (H := H))
    (h : KPCompactInteriorH1.E (3 * d F) → V 1) (hsm : ContDiff ℝ ∞ h)
    (hcompact : HasCompactSupport h) (hs : tsupport h ⊆ chart a)
    (he : ∀ γ x, x ∈ chart a → h (action a γ x) = scalarCocycle a γ x (h x)) :
    ∃ τ : localScalarTests a,
      (∀ x : omega a, τ.val x = (h (baseReindex x.val)) 0) ∧
      (∀ x : KPCompactInteriorH1.E (3 * d F),
        liftExtension a τ.val ((baseReindex (F := F)).symm x) = (h x) 0) ∧
      HasCompactSupport (liftExtension a τ.val) ∧
      tsupport (liftExtension a τ.val) ⊆ omega a := by
  let g : M F → ℂ := fun x => (h (baseReindex x)) 0
  let f : omega a → ℂ := fun x => g x.val
  have hg : ContDiff ℝ ∞ g := by
    exact (((EuclideanSpace.proj (𝕜 := ℂ) (0 : Fin 1)).restrictScalars ℝ).contDiff).comp
      (hsm.comp (baseReindex (F := F)).contDiff)
  have hts : tsupport g ⊆ (baseReindex (F := F)) ⁻¹' tsupport h := by
    apply closure_minimal _ ((isClosed_tsupport h).preimage (baseReindex (F := F)).continuous)
    intro x hx
    apply subset_tsupport
    intro hz
    exact hx (by simp [g, hz])
  have hgc : HasCompactSupport g := by
    apply (hcompact.image (baseReindex (F := F)).symm.continuous).of_isClosed_subset
      (isClosed_tsupport g)
    intro x hx
    exact ⟨baseReindex x, hts hx, (baseReindex (F := F)).symm_apply_apply x⟩
  have hgs : tsupport g ⊆ omega a := by
    intro x hx
    have hh := hs (hts hx)
    change (baseReindex (F := F)).symm (baseReindex x) ∈ omega a at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh
  have hgf : liftExtension a f = g := by
    funext x
    by_cases hx : x ∈ omega a
    · simp [liftExtension, hx, f]
    · have hz : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hh => hx (hgs hh))
      simp [liftExtension, hx, hz]
  have hq : Continuous (q a) := by
    exact continuous_quot_mk.comp
      (KPContActualGlobalGreen.continuous_labeledA_actual.prodMk continuous_const)
  have hqK := hgc.image hq
  have hlocal : localSupport a f ⊆ q a '' tsupport g := by
    apply closure_minimal _ hqK.isClosed
    rintro y ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨x, subset_tsupport g hn, rfl⟩
  have hlocal_chart : localSupport a f ⊆ a.baseDomain := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hlocal hy
    refine ⟨⟨labeledA (placeEquiv F ζ hζ) x, hgs hx⟩, ?_⟩
    rfl
  have hfe : ScalarEquivariant a f := by
    intro γ x hx
    have hx' : baseReindex x ∈ chart a := by
      change (baseReindex (F := F)).symm (baseReindex x) ∈ omega a
      simpa using hx
    have hh := congrArg (fun v : V 1 => v 0) (he γ (baseReindex x) hx')
    have hphase : (isotropyArrow a γ).phase x =
        (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) := by
      simp [Arrow.phase, isotropyArrow, isotropyChart]
    dsimp only [f, g]
    rw [hphase]
    change (h (baseReindex ((isotropyArrow a γ).psi
      ((baseReindex (F := F)).symm (baseReindex x))))) 0 =
      (KPCuspGenuineMonodromy.chi F ζ hζ γ.val.2 : ℂ) * (h (baseReindex x)) 0 at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh
  refine ⟨⟨f, ⟨⟨g, hg.contDiffOn, fun _ => rfl⟩, hfe,
    hqK.of_isClosed_subset isClosed_closure hlocal, hlocal_chart⟩⟩,
    fun _ => rfl, ?_, ?_, ?_⟩
  · intro x
    rw [hgf]
    simp [g]
  · rwa [hgf]
  · rwa [hgf]

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

namespace DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

open KPContActualSectorSmoothTestModules KPContActualSectorTestDifferentialDescent
open KPContActualSectorChartEquivariantInputs KPContCotangentActualOverlap
open KPContActualSectorTestEmbeddings KPContLocalNorm KPContCotangentOverlapRationalBranches

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}

end DedekindZetaZeroFree.KPContActualSectorCompactWeakFormConverse

end
