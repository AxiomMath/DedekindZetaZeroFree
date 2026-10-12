module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.HarishChandraSectionExtraction

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace DedekindZetaZeroFree.KPLiteralScalarHCSliceCharts
open KPLiteralRaw KPAdelicCoverRestrictedProduct KPLiteralChamber
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCExtraction KPCplxCharacterHaar
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

 def sliceCoordinates (w : InfinitePlace F) (u v : ℂ) :
    KPGlobalTorusBorelTwistCompatibility.GroupArch F :=
  fun j => if j = w then ![u, 1, v] else ![0, 1, 0]

private theorem sliceCoordinates_domain (w : InfinitePlace F) (u v : ℂ) :
    sliceCoordinates F w u v ∈ KPGlobalTorusBorelTwistCompatibility.groupArchDomain F := by
  intro j
  by_cases hj : j = w <;> simp [sliceCoordinates, hj]

private theorem leftMatrix_zero : leftMatrix ![0, 1, 0] = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  rw [leftMatrix_val _ (by simp)]
  intro i j
  fin_cases i <;> fin_cases j <;> simp

private theorem leftMatrix_lower (u : ℂ) : leftMatrix ![u, 1, 0] = lowerUnipotent u := by
  apply Matrix.GeneralLinearGroup.ext
  rw [leftMatrix_val _ (by simp)]
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

private theorem groupArchChart_slice_lower (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusBorelTwistCompatibility.groupArchChart F ζ hζ (sliceCoordinates F w u 0) =
      archMatrixInsertion F ζ hζ (Function.update 1 w (lowerUnipotent u)) := by
  rw [← sectionTuple_left]
  change archMatrixInsertion F ζ hζ (fun j => leftMatrix (sliceCoordinates F w u 0 j)) = _
  congr 1
  funext j
  by_cases hj : j = w
  · subst j; simp [sliceCoordinates, leftMatrix_lower]
  · simp [sliceCoordinates, hj, Function.update_of_ne hj, leftMatrix_zero]

variable (K : Subgroup (G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
variable (C : KPGlobalTorusBorelTwistCompatibility.ModelData F ζ hζ) (f : Flat F ζ hζ K)

theorem productHCScalar_lower_sweep (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => productHCScalar F ζ hζ K hK C f
      (b.val * archMatrixInsertion F ζ hζ (Function.update a w (lowerUnipotent u * a w)))) := by
  let a₀ := a
  let g := b.val * archMatrixInsertion F ζ hζ a₀
  have hs := productHCScalar_left_chart F ζ hζ K hK C f g
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => sliceCoordinates F w u 0) := by
    apply contDiff_pi.mpr
    intro j
    by_cases hj : j = w
    · subst j
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> simp [sliceCoordinates] <;> fun_prop
    · simpa [sliceCoordinates, hj] using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : ℂ => ![(0 : ℂ), 1, 0]))
  have hc := hs.comp (s := Set.univ) hcoord.contDiffOn (fun u _ => sliceCoordinates_domain F w u 0)
  convert contDiffOn_univ.mp hc using 1
  funext u
  symm
  dsimp only [Function.comp_def]
  rw [groupArchChart_slice_lower]
  change productHCScalar F ζ hζ K hK C f
    (archMatrixInsertion F ζ hζ (Function.update 1 w (lowerUnipotent u)) *
      (b.val * archMatrixInsertion F ζ hζ a₀)) = _
  rw [← mul_assoc, (archMatrixInsertion_commutes_finite F ζ hζ _ b).eq, mul_assoc, ← map_mul]
  congr 3
  funext j
  by_cases hj : j = w
  · subst j; simp [a₀]
  · simp [a₀, Function.update_of_ne hj]

theorem productHCScalar_infinity_chart (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => productHCScalar F ζ hζ K hK C f
      (b.val * archMatrixInsertion F ζ hζ (Function.update a w (lowerUnipotent u)))) := by
  simpa only [Function.update_self, mul_one, Function.update_idem] using
    productHCScalar_lower_sweep F ζ hζ K hK C f b w (Function.update a w 1)

private theorem weyl_upper_eq_lower_weyl (u : ℂ) :
    weyl * upperUnipotent u = lowerUnipotent u * weyl := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, upperUnipotent, lowerUnipotent, Matrix.mul_apply, Fin.sum_univ_two]

theorem productHCScalar_open_chart (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℂ => productHCScalar F ζ hζ K hK C f
      (b.val * archMatrixInsertion F ζ hζ (Function.update a w (weyl * upperUnipotent u)))) := by
  simpa only [Function.update_self, Function.update_idem, ← weyl_upper_eq_lower_weyl] using
    productHCScalar_lower_sweep F ζ hζ K hK C f b w (Function.update a w weyl)

theorem productHCScalar_slice_two_charts
    (b : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    ContDiff ℝ (⊤ : ℕ∞) (KPCplxPrincipalSeriesCharts.openCoordinate
      (fun m => productHCScalar F ζ hζ K hK C f
        (b.val * archMatrixInsertion F ζ hζ (Function.update a w m)))) ∧
    ContDiff ℝ (⊤ : ℕ∞) (KPCplxPrincipalSeriesCharts.infinityCoordinate
      (fun m => productHCScalar F ζ hζ K hK C f
        (b.val * archMatrixInsertion F ζ hζ (Function.update a w m)))) :=
  ⟨productHCScalar_open_chart F ζ hζ K hK C f b w a,
    productHCScalar_infinity_chart F ζ hζ K hK C f b w a⟩

end DedekindZetaZeroFree.KPLiteralScalarHCSliceCharts

end
