module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenbergInducingData

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneForwardTestVector.ActualSource
open scoped NumberField Valued Topology
open Classical NumberField IsDedekindDomain ValuativeRel
open KPLocalExceptionalConstruction KPLocalStoneVonNeumann KPLocalPrincipalSeries

set_option autoImplicit false

theorem integer_open_cell_section
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (q : HeightOneSpectrum (𝓞 F))
    (S : CanonicalFiniteInducingData F ζ hζ q) (P : Polarization S.heisenberg)
    (v : InducedModule P) :
    ∃ f : sectionSpace S.borel P .plus 0,
      KPRankOneOpenCellKernel.IsOpenCellSection F ζ hζ q S.borel P .plus 0 f ∧
      (∀ x : LocalField F q,
        f.val (S.borel.liftedW⁻¹ *
          (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q)) =
          if x ∈ (valuation (LocalField F q)).integer then v else 0) := by
  let U : AddSubgroup (LocalField F q) := (valuation (LocalField F q)).integer.toAddSubgroup
  have ho : IsClopen (U : Set (LocalField F q)) :=
    (valuation (LocalField F q)).isClopen_integer
  have hc : IsCompact (U : Set (LocalField F q)) :=
    IsNonarchimedeanLocalField.isCompact_closedBall (LocalField F q) 1
  let φ : LocalField F q → InducedModule P := (U : Set (LocalField F q)).indicator (fun _ => v)
  have hl : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [ho.isOpen.mem_nhds hx] with y hy
      simp [φ, hx, hy]
    · filter_upwards [ho.isClosed.isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ U := hy
      simp [φ, hx, hy']
  have hs : HasCompactSupport φ :=
    HasCompactSupport.intro hc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨f, hf, _⟩ := (KPRankOneOpenCellKernel.open_cell_correspondence
    F ζ hζ q S.borel P (S.openCell P) .plus 0).2 φ hl hs
  refine ⟨f, hf.1, ?_⟩
  intro x
  have he : S.borel.liftedW⁻¹ *
      (S.borel.upperRoot (Multiplicative.ofAdd x) : ActualCover F ζ hζ q) =
      KPRankOneOpenCellKernel.openCoordinate F ζ hζ q x := by
    simp only [KPRankOneOpenCellKernel.openCoordinate,
      (S.openCell P).weyl_eq, (S.openCell P).upper_eq]
  rw [he, hf.2 x]
  change (U : Set (LocalField F q)).indicator (fun _ => v) x = if x ∈ U then v else 0
  exact Set.indicator_apply _ _ _

end DedekindZetaZeroFree.KPRankOneForwardTestVector.ActualSource

end
