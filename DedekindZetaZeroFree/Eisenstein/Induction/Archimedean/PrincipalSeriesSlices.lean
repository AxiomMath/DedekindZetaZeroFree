module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.HarishChandraHeckeCore.FiniteDimensionalCompactOrbits
public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.BorelCharacter
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LiteralArchSlices
public import DedekindZetaZeroFree.Geometry.SymmetricSpaces.ArchimedeanSphericalQuotients

@[expose] public section

noncomputable section
open scoped Classical NumberField NNReal
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

section InsertionCharts
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def leftMatrix (x : Fin 3 → ℂ) : Matrix.GeneralLinearGroup (Fin 2) ℂ :=
  KPStandardLocalRootLifts.lowerN ℂ (x 0) * KubotaRankTwo.d ℂ (diagonalUnit (x 1)) 1 *
    KubotaRankTwo.n ℂ (x 2)

 def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by
      intro v; cases v <;> simp [KPAdelicCoverRestrictedProduct.compact])⟩

 def complexSectionHom (w : InfinitePlace F) :
    Matrix.GeneralLinearGroup (Fin 2) ℂ →* KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inl w) where
  toFun r := KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
    (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom r)
  map_one' := by simp [KPLocalCover.sectionMap]; rfl
  map_mul' := by
    intro r s
    change KPLocalCover.CubicGL2Raw.mk _ 1 = KPLocalCover.CubicGL2Raw.mk _ _
    congr 1
    · simp
    · simp [KPLocalChartTopology.complex_sigmaTwo_eq_one]

end InsertionCharts

private theorem source_chart_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => t.val.val
      (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g))
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
  have ht : t.val ∈ KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
      (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
    have hle : KPMsRationalCompactCrossPairing.sourceCore F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ) ≤
        KPMsRationalCompactCrossPairing.scalarSmooth F ζ hζ
          (KPMsRationalCompactCrossPairing.sourcePolarization F ζ hζ 0) := by
      unfold KPMsRationalCompactCrossPairing.sourceCore KPGlobalEisensteinData.hcHeckeCore
      exact iSup_le fun _ => iSup_le fun _ => inf_le_left.trans inf_le_left
    exact hle t.property
  obtain ⟨v, hv⟩ := ht
  have hs := v.property
  change v.val ∈ ⨆ J, KPGlobalTorusBorelTwistCompatibility.InducedLevel F ζ hζ _ J at hs
  have hd : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (v.val.val (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F) := by
    exact Submodule.iSup_induction (motive := fun x => ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => (x.val (KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ z * g)).val.val 1)
      (KPGlobalTorusBorelTwistCompatibility.groupArchDomain F)) _ hs
      (fun _ _ hx => hx.1 g) contDiffOn_const (fun _ _ hx hy => hx.add hy)
  simpa only [← hv, KPGlobalTorusBorelTwistCompatibility.scalarSection_formula] using hd

private theorem slice_lower_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (g : KPCplxCharacterHaar.ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => t.val.val
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.lowerUnipotent u * g))) * c.val)) := by
  have hs := (source_chart_smooth F ζ hζ t
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)).comp
      ((lowerCoordinates_smooth F w).contDiffOn (s := Set.univ))
      (fun u _ => by intro v; simp [lowerCoordinates])
  apply contDiffOn_univ.mp
  apply hs.congr
  intro u _
  dsimp only [Function.comp_def]
  rw [lowerCoordinates_insertion, ← mul_assoc,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
    update_left_mul, map_mul]

private theorem slice_charts_smooth
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    let f := fun g : KPCplxCharacterHaar.ComplexGL2 => t.val.val
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)
    ContDiff ℝ (⊤ : ℕ∞) (KPCplxPrincipalSeriesCharts.openCoordinate f) ∧
    ContDiff ℝ (⊤ : ℕ∞) (KPCplxPrincipalSeriesCharts.infinityCoordinate f) := by
  dsimp only
  constructor
  · change ContDiff ℝ (⊤ : ℕ∞) (fun u => _)
    simpa only [KPCplxPrincipalSeriesCharts.openCoordinate, weyl_upper] using slice_lower_smooth F ζ hζ t w a c KPCplxCharacterHaar.weyl
  · change ContDiff ℝ (⊤ : ℕ∞) (fun u => _)
    simpa only [KPCplxPrincipalSeriesCharts.infinityCoordinate, mul_one] using
      slice_lower_smooth F ζ hζ t w a c 1

private theorem slice_covariance
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : InfinitePlace F) (a₀ : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    KPCplxPrincipalSeriesCharts.HasCovariance KPCplxPrincipalSeriesCharts.positiveParameter
      (fun g => t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val)) := by
  intro a d b g
  let z := singleDiagonal F w (a / d)
  have hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F := by
    intro v
    by_cases hv : v = w
    · subst v; simp [z, singleDiagonal, Units.ne_zero]
    · simp [z, singleDiagonal, hv]
  have hd : (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1))) := by
    rw [diagonal_insertion]
    congr 1
    funext v
    by_cases hv : v = w
    · subst v
      simp only [z, singleDiagonal, Function.update_self]
      have hh : diagonalUnit ((a / d : ℂˣ) : ℂ) = a / d := by
        apply Units.ext; simp [diagonalUnit, Units.ne_zero]
      rw [hh]
    · have hh : KubotaRankTwo.d ℂ 1 1 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      simp [z, singleDiagonal, diagonalUnit, hv, hh]
  have he : ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val *
        KPGlobalTorusFunctionData.N F ζ hζ (singleAdele F ζ hζ w (b / a))) *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a₀ w (Matrix.ProjGenLinGroup.mk
          (KPCplxPrincipalSeriesCharts.upperTriangular a d b * g))) * c.val := by
    rw [hd, unipotent_insertion, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    rw [update_left_mul]
    congr 2
    funext v
    by_cases hv : v = w
    · subst v
      simp only [Pi.mul_apply, Function.update_self, map_mul, upper_projective]
    · simp [hv]
  have hp : (∏ v : InfinitePlace F, ‖z v‖ ^ 2) = ‖(a : ℂ) / (d : ℂ)‖ ^ 2 := by
    calc _ = ∏ v : InfinitePlace F, if v = w then ‖(a : ℂ) / (d : ℂ)‖ ^ 2 else 1 := by
          apply Finset.prod_congr rfl
          intro v _
          by_cases hv : v = w <;> simp [z, singleDiagonal, hv]
      _ = _ := by simp
  have hc := ActualRaisingGeometry.source_arch_borel_covariance F ζ hζ t z hz
    (singleAdele F ζ hζ w (b / a))
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val)
  rw [he, hp] at hc
  convert hc using 2
  unfold KPCplxPrincipalSeriesCharts.inductionWeight KPCplxPrincipalSeriesCharts.complexAbs
  norm_num [KPCplxPrincipalSeriesCharts.positiveParameter]

 def restrictionLinear
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    (KPGlobalTorusFunctionData.G F ζ hζ → ℂ) →ₗ[ℂ] (KPCplxCharacterHaar.ComplexGL2 → ℂ) where
  toFun f g := f (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem slice_kfinite
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (hf : ∀ g, f g = t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)) :
    KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f := by
  let O := Submodule.span ℂ (Set.range (fun k : (KPContFlatSourceRecipe.D F ζ hζ).K =>
    fun g => t.val.val (g * k.val)))
  letI : FiniteDimensional ℂ O :=
    KPGlobalResidualKernel.ScatteringResidue.SourceCoreCompactOrbit.source_finiteDimensional t
  let R := restrictionLinear F ζ hζ w a c
  let S := Submodule.span ℂ (Set.range (fun k : KPCplxPrincipalSeriesCharts.compactSubgroup =>
    KPCplxPrincipalSeriesCharts.pi KPCplxPrincipalSeriesCharts.positiveParameter k f))
  have hle : S.map (KPCplxPrincipalSeriesCharts.principalSeriesSubmodule _).subtype ≤ O.map R := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := h.property
    change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding u) = h.val at hu
    refine Submodule.mem_map.mpr ⟨fun g => t.val.val
      (g * KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u), ?_, ?_⟩
    · exact Submodule.subset_span ⟨⟨_, KPContFlatFullProductIwasawa.complexCompactLift_mem F ζ hζ w u⟩, rfl⟩
    · funext g
      change R (fun g => t.val.val (g * KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u)) g =
        (KPCplxPrincipalSeriesCharts.pi _ h.val f) g
      rw [← hu, KPCplxPrincipalSeriesCharts.pi_mk]
      change t.val.val _ = f (g * KPCplxCharacterHaar.complexSU2Embedding u)
      rw [hf, ← compact_insertion]
      have hc := insertion_commutes_finite F ζ hζ
        (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding u))) c
      rw [mul_assoc, hc.eq.symm, ← mul_assoc,
        ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
      apply congrArg (fun x => t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ x * c.val))
      funext v
      by_cases hv : v = w <;> simp [hv, map_mul]
  letI : FiniteDimensional ℂ (S.map (KPCplxPrincipalSeriesCharts.principalSeriesSubmodule _).subtype) :=
    Submodule.finiteDimensional_of_le hle
  let L := (KPCplxPrincipalSeriesCharts.principalSeriesSubmodule
    KPCplxPrincipalSeriesCharts.positiveParameter).subtype.domRestrict S
  have hL : Function.Injective L := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have heq : L.range = S.map (KPCplxPrincipalSeriesCharts.principalSeriesSubmodule
      KPCplxPrincipalSeriesCharts.positiveParameter).subtype := by
    exact LinearMap.range_domRestrict _ _
  letI : FiniteDimensional ℂ L.range := heq.symm ▸ inferInstance
  change FiniteDimensional ℂ S
  have hi : Function.Injective L.rangeRestrict := by
    intro x y hxy
    apply hL
    exact congrArg (fun z : L.range => z.val) hxy
  exact FiniteDimensional.of_injective L.rangeRestrict hi

theorem actual_one_slot_source_principal_series
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : NumberField.InfinitePlace F)
    (k : KPContSectorArchSphericalFibers.KInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ∃ f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter,
      KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f ∧
      ∀ a : KPCplxCharacterHaar.ComplexGL2,
        f a = t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (Function.update k.val w (Matrix.ProjGenLinGroup.mk a)) * c.val) := by
  let f : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter :=
    ⟨_, slice_covariance F ζ hζ t w k.val c, slice_charts_smooth F ζ hζ t w k.val c⟩
  exact ⟨f, slice_kfinite F ζ hζ t w k.val c f (fun _ => rfl), fun _ => rfl⟩

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal

end
