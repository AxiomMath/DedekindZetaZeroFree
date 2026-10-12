module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.CompactDerivatives.SecondDerivativeL2

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy
open _root_.DedekindZetaZeroFree.FourierContinuation.ResidualCompactSecondL2 renaming compactAction → compactAction
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem original_compact_orbit_finite
    (f : KPSmoothActualFlowData.X F ζ hζ → ℂ)
    (hk : KPMsGreenFlux.KFinite F ζ hζ
      (fun g => f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g))) :
    FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range (fun k : KPMsGreenFlux.K F => f ∘ compactAction k))) := by
  let V := Submodule.span ℂ
    (Set.range (fun k : KPMsGreenFlux.K F => f ∘ compactAction k))
  let W := Submodule.span ℂ
    (Set.range (fun k : KPMsGreenFlux.K F => fun g =>
      f (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ
        (g * KPMsGreenFlux.compactInsertion F ζ hζ k))))
  letI : FiniteDimensional ℂ W := hk
  let pull : (KPSmoothActualFlowData.X F ζ hζ → ℂ) →ₗ[ℂ]
      (KPSmoothActualFlowData.G F ζ hζ → ℂ) :=
    { toFun := fun u g => u (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem (u : KPSmoothActualFlowData.X F ζ hζ → ℂ) (hu : u ∈ V) : pull u ∈ W := by
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k,rfl⟩ := hx
      exact Submodule.subset_span (Set.mem_range_self k)
    | zero => exact W.zero_mem
    | add x y hx hy ihx ihy => exact W.add_mem ihx ihy
    | smul a x hx ih => exact W.smul_mem a ih
  let L : V →ₗ[ℂ] W := (pull.domRestrict V).codRestrict W (fun u => hmem u.val u.property)
  apply FiniteDimensional.of_injective L
  intro u v huv
  apply Subtype.ext
  funext x
  obtain ⟨g,rfl⟩ := Quotient.mk_surjective x
  exact congrFun (congrArg Subtype.val huv) g

end DedekindZetaZeroFree.FourierContinuation.ResidualWeakEnergy

end
