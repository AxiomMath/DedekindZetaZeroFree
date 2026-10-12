module

public import DedekindZetaZeroFree.Eisenstein.Induction.ArchimedeanSectionSmoothness
public import DedekindZetaZeroFree.Theta.Whittaker.Complex.NegativeSlotCompactBounds

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology NNReal BigOperators Matrix.Norms.Elementwise ContDiff
open NumberField
namespace DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot
open KPGlobalTorusFiniteStages KPGlobalResidualConstruction KPLiteralChamber
open KPCplxPrincipalSeriesCharts KPCplxCharacterHaar
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
variable (P : CompatibleModelData F A.zeta12 A.primitive_zeta12)
variable (C : LocalFiberData F A.zeta12 A.primitive_zeta12 P)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
local notation "Raw" => KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ
variable (s : RestrictedTensorSimple.Level (bad A P C))
variable (x : ∀ j : s.val, Plus A P C j.val) (g : Raw)

theorem matrix_sectionTuple (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    matrix A w (sectionTuple F ζ hζ a (Sum.inl w)) = a w := by
  unfold matrix sectionTuple
  change Matrix.GeneralLinearGroup.map _ (Matrix.GeneralLinearGroup.map _ (a w)) = a w
  apply Units.ext
  ext i j
  simp [Matrix.GeneralLinearGroup.map]

theorem matrix_shift (g : Raw) (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    matrix A w ((g * sectionTuple F ζ hζ a) (Sum.inl w)) =
      matrix A w (g (Sum.inl w)) * a w := by
  change matrix A w (g (Sum.inl w) * sectionTuple F ζ hζ a (Sum.inl w)) = _
  unfold matrix
  change Matrix.GeneralLinearGroup.map _ ((g (Sum.inl w)).g *
    (sectionTuple F ζ hζ a (Sum.inl w)).g) = _
  rw [map_mul]
  change _ * matrix A w (sectionTuple F ζ hζ a (Sum.inl w)) = _
  rw [matrix_sectionTuple]

theorem phase_shift (g : Raw) (w : InfinitePlace F) (a : InfinitePlace F → ComplexGL2) :
    ((g * sectionTuple F ζ hζ a) (Sum.inl w)).epsilon = (g (Sum.inl w)).epsilon := by
  change (g (Sum.inl w)).epsilon * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inl w) _ _ = _
  rw [KPLocalChartTopology.complex_sigmaTwo_eq_one]
  simp

theorem finiteTuple_shift (g : Raw) (a : InfinitePlace F → ComplexGL2) :
    finiteTuple A P C s x (g * sectionTuple F ζ hζ a) = finiteTuple A P C s x g := by
  funext q
  have he : (g * sectionTuple F ζ hζ a) (Sum.inr q.val) = g (Sum.inr q.val) := by
    change g (Sum.inr q.val) * 1 = _
    exact mul_one _
  simp only [finiteTuple, he]

theorem finiteScalar_shift (g : Raw) (a : InfinitePlace F → ComplexGL2) :
    finiteScalar A P C s x (g * sectionTuple F ζ hζ a) = finiteScalar A P C s x g := by
  unfold finiteScalar finiteFiber
  rw [finiteTuple_shift]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem principal_matrix_comp_smooth (U : Set E) (f : PrincipalSeries positiveParameter)
    (a : E → ComplexGL2)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (a z).val) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => f (a z)) U := by
  have hf := ((principalSeries_mem_iff _ f).mp f.property).2
  apply (hf.comp ha (fun z _ => Matrix.GeneralLinearGroup.det_ne_zero (a z))).congr
  intro z hz
  change f (a z) = matrixFunction f (a z)
  simp only [matrixFunction, dif_pos (Matrix.GeneralLinearGroup.det_ne_zero (a z))]
  exact congrArg (fun b : ComplexGL2 => f b) (Units.ext rfl)

theorem matrix_mul_comp_smooth (U : Set E) (M : ComplexGL2) (a : E → ComplexGL2)
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (a z).val) U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (M * a z).val) U := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => M.val * (a z).val) U
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffOn.sum
  intro k hk
  exact contDiffOn_const.mul ((contDiffOn_pi.mp (contDiffOn_pi.mp ha k)) j)

theorem coefficient_shift_smooth (g : Raw) (w : InfinitePlace F) (U : Set E)
    (a : InfinitePlace F → E → ComplexGL2)
    (ha : ∀ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (a u z).val) U) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z => coefficient A P C s x (g * sectionTuple F ζ hζ (fun u => a u z)) w) U := by
  simp only [coefficient, finiteScalar_shift, phase_shift]
  apply ContDiffOn.mul _ contDiffOn_const
  apply ContDiffOn.mul _ contDiffOn_const
  apply contDiffOn_prod
  intro j _
  rcases j with ⟨j, hj⟩
  cases j with
  | inr q => exact contDiffOn_const
  | inl u =>
    by_cases hu : u = w
    · simp only [archComplement, hu, if_true]
      exact contDiffOn_const
    · simp only [archComplement, if_neg hu, phase_shift, matrix_shift]
      exact contDiffOn_const.mul (principal_matrix_comp_smooth U (x ⟨Sum.inl u, hj⟩).val
        (fun z => matrix A u (g (Sum.inl u)) * a u z)
        (matrix_mul_comp_smooth U _ _ (ha u)))

theorem negative_shift_smooth (g : Raw) (w : InfinitePlace F) (U : Set E)
    (a : InfinitePlace F → E → ComplexGL2)
    (ha : ∀ u, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => (a u z).val) U)
    (f : PrincipalSeries negativeParameter) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
      negative A P C s x (g * sectionTuple F ζ hζ (fun u => a u z)) w f) U := by
  simp only [negative_apply, matrix_shift]
  exact (coefficient_shift_smooth A P C s x g w U a ha).mul
    (principal_matrix_comp_smooth U (NativeStageSlot.inverse f) _
      (matrix_mul_comp_smooth U _ _ (ha w)))

end DedekindZetaZeroFree.FourierContinuation.ComplexLines.CanonicalStageSlot

end
