module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanBorelAndWeylValues
public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.ArchSliceGeometry
public import DedekindZetaZeroFree.Eisenstein.Induction.ScatteringChamberAndSmoothTorusFibers
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.FiniteHarmonicSampling

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open _root_.DedekindZetaZeroFree.RepresentationTheory.KPContHolomorphicKGenerationProve renaming orbit_span_invariant → orbit_span_invariant
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming diagonalUnit → diagonalUnit
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming lowerCoordinates → lowerCoordinates
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming lowerCoordinates_smooth → lowerCoordinates_smooth
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming lowerCoordinates_insertion → lowerCoordinates_insertion
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming update_left_mul → update_left_mul
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming weyl_upper → weyl_upper
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming singleDiagonal → singleDiagonal
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming diagonal_insertion → diagonal_insertion
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming singleAdele → singleAdele
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming unipotent_insertion → unipotent_insertion
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming upper_projective → upper_projective
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming compact_insertion → compact_insertion
open _root_.DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal renaming insertion_commutes_finite → insertion_commutes_finite
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

def literalArchSlice (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (g : ComplexGL2) : ℂ :=
  f.val 0 (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)

theorem literalArchSlice_lower_smooth
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) (g : ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => literalArchSlice F ζ hζ K f w a c
      (lowerUnipotent u * g)) := by
  have hs := (KPLiteralChamber.literal_raw_group_chart_contDiffOn F ζ hζ
    (f.val 0) (f.property.1 0).1
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)).comp
    ((lowerCoordinates_smooth F w).contDiffOn (s := Set.univ))
    (fun u _ => by intro v; simp [lowerCoordinates])
  apply contDiffOn_univ.mp
  apply hs.congr
  intro u _
  dsimp only [Function.comp_def, literalArchSlice]
  rw [lowerCoordinates_insertion, ← mul_assoc,
    ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
    update_left_mul, map_mul]

theorem literalArchSlice_charts_smooth
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    ContDiff ℝ (⊤ : ℕ∞) (openCoordinate (literalArchSlice F ζ hζ K f w a c)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (infinityCoordinate (literalArchSlice F ζ hζ K f w a c)) := by
  constructor
  · change ContDiff ℝ (⊤ : ℕ∞) (fun u => literalArchSlice F ζ hζ K f w a c (weyl * upperUnipotent u))
    simpa only [weyl_upper] using
      literalArchSlice_lower_smooth F ζ hζ K f w a c weyl
  · change ContDiff ℝ (⊤ : ℕ∞) (fun u => literalArchSlice F ζ hζ K f w a c (lowerUnipotent u))
    simpa only [mul_one] using
      literalArchSlice_lower_smooth F ζ hζ K f w a c 1

theorem literalArchSlice_covariance
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (w : InfinitePlace F) (a₀ : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    HasCovariance positiveParameter (literalArchSlice F ζ hζ K f w a₀ c) := by
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
        (Function.update a₀ w (Matrix.ProjGenLinGroup.mk (upperTriangular a d b * g))) * c.val := by
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
  have hc := CompactPeriodAnalyticity.ArchValue.literal_arch_borel_covariance F ζ hζ K f 0 z hz
    (singleAdele F ζ hζ w (b / a))
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val)
  rw [he, hp] at hc
  change f.val 0 _ = (inductionWeight positiveParameter a d : ℂ) * f.val 0 _
  rw [hc]
  congr 1
  have hn : 0 < ‖(a : ℂ) / (d : ℂ)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (div_ne_zero a.ne_zero d.ne_zero)) _
  change KPGlobalExceptionalParameter.realLogPower (‖(a : ℂ) / (d : ℂ)‖ ^ 2) (2 / 3 + 0) =
    ((‖(a : ℂ) / (d : ℂ)‖ ^ 2) ^ (1 / 2 + (1 / 6 : ℝ)) : ℝ)
  rw [show (1 / 2 + (1 / 6 : ℝ)) = 2 / 3 by norm_num,
    Real.rpow_def_of_pos hn, Complex.ofReal_exp]
  unfold KPGlobalExceptionalParameter.realLogPower
  congr 1
  push_cast
  ring

def literalArchPrincipalSeries
    (K : Subgroup (G F ζ hζ)) (f : Flat F ζ hζ K)
    (w : InfinitePlace F) (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) : PrincipalSeries positiveParameter :=
  ⟨literalArchSlice F ζ hζ K f w a c, literalArchSlice_covariance F ζ hζ K f w a c,
    literalArchSlice_charts_smooth F ζ hζ K f w a c⟩

theorem literalArchPrincipalSeries_kfinite
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) (w : InfinitePlace F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    KPContHolomorphicKGeneration.IsKFinite positiveParameter
      (literalArchPrincipalSeries F ζ hζ K f w a c) := by
  obtain ⟨U, hU, hfU, hstable⟩ := f.property.2.2
  letI : Module.Finite ℂ U := hU
  let L : Functions F ζ hζ →ₗ[ℂ] (ComplexGL2 → ℂ) :=
    { toFun := fun h g => h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let p := literalArchPrincipalSeries F ζ hζ K f w a c
  let O := Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi positiveParameter k p))
  have hle : O.map (principalSeriesSubmodule positiveParameter).subtype ≤ U.map L := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := k.property
    change Matrix.ProjGenLinGroup.mk (complexSU2Embedding u) = k.val at hu
    refine Submodule.mem_map.mpr
      ⟨rightAction F ζ hζ (KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u)
        (f.val 0), hstable ⟨_, hK.2.2 w u⟩ _ hfU, ?_⟩
    funext g
    change L (rightAction F ζ hζ
      (KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u) (f.val 0)) g =
        (KPCplxPrincipalSeriesCharts.pi positiveParameter k.val p) g
    rw [← hu, pi_mk]
    change f.val 0 (_ * KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u) =
      f.val 0 (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk (g * complexSU2Embedding u))) * c.val)
    rw [← compact_insertion]
    have hc := insertion_commutes_finite F ζ hζ
      (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (complexSU2Embedding u))) c
    rw [mul_assoc, hc.eq.symm, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    apply congrArg (fun x => f.val 0
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ x * c.val))
    funext v
    by_cases hv : v = w <;> simp [hv, map_mul]
  letI : FiniteDimensional ℂ (O.map (principalSeriesSubmodule positiveParameter).subtype) :=
    Submodule.finiteDimensional_of_le hle
  let T := (principalSeriesSubmodule positiveParameter).subtype.domRestrict O
  have hi : Function.Injective T.rangeRestrict := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : T.range => z.val) hxy
  have heq : T.range = O.map (principalSeriesSubmodule positiveParameter).subtype :=
    LinearMap.range_domRestrict _ _
  letI : FiniteDimensional ℂ T.range := heq.symm ▸ inferInstance
  change FiniteDimensional ℂ O
  exact FiniteDimensional.of_injective T.rangeRestrict hi

theorem literalArchPrincipalSeries_uniform_band
    (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) :
    ∃ B : ℕ, ∀ (w : InfinitePlace F)
      (a : KPSmoothActualFlowData.GInfinity F)
      (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
      literalArchPrincipalSeries F ζ hζ K f w a c ∈
        KPLiteralScalarArchIndependentSlices.harmonicBand positiveParameter B := by
  obtain ⟨U, hU, hfU, hstable⟩ := f.property.2.2
  letI : Module.Finite ℂ U := hU
  refine ⟨Module.finrank ℂ U, ?_⟩
  intro w a c
  let p := literalArchPrincipalSeries F ζ hζ K f w a c
  let O := Submodule.span ℂ (Set.range (fun k : compactSubgroup => KPCplxPrincipalSeriesCharts.pi positiveParameter k p))
  let L : Functions F ζ hζ →ₗ[ℂ] (ComplexGL2 → ℂ) :=
    { toFun := fun h g => h (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk g)) * c.val)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hle : O.map (principalSeriesSubmodule positiveParameter).subtype ≤ U.map L := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    obtain ⟨u, hu⟩ := k.property
    change Matrix.ProjGenLinGroup.mk (complexSU2Embedding u) = k.val at hu
    refine Submodule.mem_map.mpr
      ⟨rightAction F ζ hζ (KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u)
        (f.val 0), hstable ⟨_, hK.2.2 w u⟩ _ hfU, ?_⟩
    funext g
    change L (rightAction F ζ hζ
      (KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u) (f.val 0)) g =
        (KPCplxPrincipalSeriesCharts.pi positiveParameter k.val p) g
    rw [← hu, pi_mk]
    change f.val 0 (_ * KPGlobalResidualConstruction.complexCompactLift F ζ hζ w u) =
      f.val 0 (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a w (Matrix.ProjGenLinGroup.mk (g * complexSU2Embedding u))) * c.val)
    rw [← compact_insertion]
    have hc := insertion_commutes_finite F ζ hζ
      (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (complexSU2Embedding u))) c
    rw [mul_assoc, hc.eq.symm, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    apply congrArg (fun x => f.val 0
      (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ x * c.val))
    funext v
    by_cases hv : v = w <;> simp [hv, map_mul]
  letI : FiniteDimensional ℂ O := literalArchPrincipalSeries_kfinite F ζ hζ K hK f w a c
  letI : FiniteDimensional ℂ (O.map (principalSeriesSubmodule positiveParameter).subtype) :=
    Submodule.finiteDimensional_of_le hle
  have hrank : Module.finrank ℂ O ≤ Module.finrank ℂ U := by
    have he := Submodule.equivMapOfInjective (principalSeriesSubmodule positiveParameter).subtype
      (principalSeriesSubmodule positiveParameter).injective_subtype O
    calc
      Module.finrank ℂ O = Module.finrank ℂ (O.map (principalSeriesSubmodule positiveParameter).subtype) :=
        he.finrank_eq
      _ ≤ Module.finrank ℂ (U.map L) := Submodule.finrank_mono hle
      _ ≤ Module.finrank ℂ U := Submodule.finrank_map_le L U
  have hpinv : KPCplxIntertwinerEigenvalues.IsKInvariant positiveParameter O :=
    orbit_span_invariant positiveParameter p
  have hp : p ∈ O := by
    exact Submodule.subset_span ⟨1, by simp only [OneMemClass.coe_one, pi_one]⟩
  have hb := KPLiteralScalarArchUniformBands.invariant_subspace_le_band positiveParameter O hpinv hp
  apply (show KPLiteralScalarArchIndependentSlices.harmonicBand positiveParameter (Module.finrank ℂ O) ≤
      KPLiteralScalarArchIndependentSlices.harmonicBand positiveParameter (Module.finrank ℂ U) from ?_) hb
  apply Finset.sup_le
  intro i hi
  exact Finset.le_sup ((Finset.range_mono (Nat.add_le_add_right hrank 1)) hi)

end DedekindZetaZeroFree.SheetRescaling

end
