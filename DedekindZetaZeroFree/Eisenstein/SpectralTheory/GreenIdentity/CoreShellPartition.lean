module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.GreenIdentity.PairingsAndFluxDefinitions

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory
namespace DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabCoreShell
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

theorem isClosed_quotientCore
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ) (Y : ℝ) :
    IsClosed (quotientCore A P Y) := by
  have ho (j : Cusps A) : IsOpen (endSet A j Y) := by
    have hc : IsOpenMap
        (KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1)) := by
      have he := A.components.isOpenMap.comp (isOpenMap_sigmaMk (i := j.1))
      simpa only [Function.comp_def, A.components_formula] using he
    apply hc
    exact KPCuspSiegel.isOpenMap_projection F _ _
      (KPCuspSiegel.isOpen_highCusp F _ _)
  have heq : quotientCore A P Y =
      ⋂ j : Cusps A, (P.projection U) ⁻¹' (endSet A j Y)ᶜ := by
    ext x
    simp only [quotientCore, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_compl_iff]
  rw [heq]
  exact isClosed_iInter fun j =>
    (ho j).isClosed_compl.preimage (P.continuous U)

theorem endSet_antitone (j : Cusps A) {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) :
    endSet A j T ⊆ endSet A j Y := by
  apply Set.image_mono
  apply Set.image_mono
  apply Set.image_mono
  intro x hx
  exact lt_of_le_of_lt
    (div_le_div_of_nonneg_right (Real.log_le_log hY hYT) (by positivity)) hx

theorem quotientCore_mono
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    {Y T : ℝ} (hY : 0 < Y) (hYT : Y ≤ T) :
    quotientCore A P Y ⊆ quotientCore A P T := by
  intro x hx j hj
  exact hx j (endSet_antitone A j hY hYT hj)

end DedekindZetaZeroFree.KPMsGreenFlux.FiniteSlabCoreShell

end
