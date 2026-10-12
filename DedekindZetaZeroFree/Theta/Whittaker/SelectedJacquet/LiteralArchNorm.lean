module

public import DedekindZetaZeroFree.Theta.Whittaker.SelectedJacquet.LiteralArchSeparation
public import DedekindZetaZeroFree.Eisenstein.Induction.FlatSectionContinuityAndExponentialJets
public import DedekindZetaZeroFree.Adeles.Archimedean.MatrixInsertion

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology BigOperators NNReal
namespace DedekindZetaZeroFree.SheetRescaling
open NumberField KPLiteralRaw KPCplxCharacterHaar KPCplxPrincipalSeriesCharts
open KPLiteralScalarHCCompactOrbit KPLiteralScalarHCSliceCharts
open KPGlobalTorusBorelTwistCompatibility KPComplexIntertwinerParameterMajorant
open ArchMatrixGeometry
open RepresentationTheory.KPComplexStandardIntertwinerGermProve
open _root_.DedekindZetaZeroFree.KPLiteralChamber renaming sectionTuple_insertion → sectionTuple_insertion
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem literal_archMatrixInsertion (a : InfinitePlace F → ComplexGL2) :
    archMatrixInsertion F ζ hζ a =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (a w)) := by
  exact sectionTuple_insertion F ζ hζ a

theorem literal_archNorm_factor
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (g : InfinitePlace F → ComplexGL2) :
    (((iwasawaNorm F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK)
      (c.val * archMatrixInsertion F ζ hζ g) : ℝ≥0) : ℝ)) =
      (((iwasawaNorm F ζ hζ (KPLiteralChamber.literalIwasawa F ζ hζ K hK)
        c.val : ℝ≥0) : ℝ)) * ∏ w, rowRatio (g w) ^ 2 := by
  obtain ⟨a, d, u, hg, hr⟩ := chosen_factorization F g
  have he : g = (fun w => upperTriangular (a w) (d w) (u w) *
      complexSU2Embedding (chosenCompact F g w)) := funext hg
  rw [he, inserted_factorization]
  have hk := archMatrixInsertion_compact_mem F ζ hζ K hK (chosenCompact F g)
  rw [iwasawaNorm_right_compact F ζ hζ _ _ ⟨_, hk⟩,
    iwasawaNorm_borel_mul, Units.val_mul, NNReal.coe_mul]
  rw [KPGlobalTorusBorelNormTwistTransport.AnalyticInputs.delta_chart_formula F ζ hζ _
    (fun w => Units.ne_zero (a w / d w))]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro w hw
  rw [rowRatio_upper_mul, rowRatio_su2, mul_one]
  simp only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]

def literalLocalDeformation (s : ℂ) (h : KPLiteralTensor.harmonicPlus)
    (g : ComplexGL2) : ℂ :=
  Complex.exp (2 * s * (Real.log (rowRatio g) : ℂ)) * h.val g

def literalFiniteDeformation (K : Subgroup (KPLiteralRaw.G F ζ hζ))
    (hK : IwasawaCompact F ζ hζ K) (s : ℂ)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) : ℂ :=
  Complex.exp (s * (Real.log (((iwasawaNorm F ζ hζ
    (KPLiteralChamber.literalIwasawa F ζ hζ K hK) c.val : ℝ≥0) : ℝ)) : ℂ))

theorem literal_archNorm_exp_factor
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (s : ℂ) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
    (g : InfinitePlace F → ComplexGL2) :
    Complex.exp (s * (Real.log (((iwasawaNorm F ζ hζ
      (KPLiteralChamber.literalIwasawa F ζ hζ K hK)
      (c.val * archMatrixInsertion F ζ hζ g) : ℝ≥0) : ℝ)) : ℂ)) =
      literalFiniteDeformation F ζ hζ K hK s c *
        ∏ w, Complex.exp (2 * s * (Real.log (rowRatio (g w)) : ℂ)) := by
  have hc : (((iwasawaNorm F ζ hζ
      (KPLiteralChamber.literalIwasawa F ζ hζ K hK) c.val : ℝ≥0) : ℝ)) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (Units.ne_zero _)
  have hp : (∏ w, rowRatio (g w) ^ 2) ≠ 0 :=
    (Finset.prod_pos (fun w _ => pow_pos (rowRatio_positive _) 2)).ne'
  rw [literal_archNorm_factor, Real.log_mul hc hp, Complex.ofReal_add, mul_add,
    Complex.exp_add]
  congr 1
  rw [Real.log_prod (fun w _ => (pow_pos (rowRatio_positive _) 2).ne')]
  simp only [Real.log_pow, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro w _
  congr 1
  ring

theorem literalFlat_full_separation
    (K : Subgroup (KPLiteralRaw.G F ζ hζ)) (hK : IwasawaCompact F ζ hζ K)
    (f : Flat F ζ hζ K) :
    ∃ (n : ℕ) (p : Fin n → (InfinitePlace F → ComplexGL2))
      (b : Fin n → ℂ) (h : Fin n → InfinitePlace F → KPLiteralTensor.harmonicPlus),
      ∀ (s : ℂ) (c : KPGlobalTorusFunctionData.finitePart F ζ hζ)
        (a : InfinitePlace F → ComplexGL2),
        f.val s (c.val * archMatrixInsertion F ζ hζ a) =
          ∑ i, (b i * literalArchProduct F ζ hζ K f c (p i) *
            literalFiniteDeformation F ζ hζ K hK s c) *
              ∏ w, literalLocalDeformation s (h i w) (a w) := by
  obtain ⟨n, p, b, h, he⟩ := literalArchProduct_separation F ζ hζ K hK f
  refine ⟨n, p, b, h, ?_⟩
  intro s c a
  rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK,
    literal_archNorm_exp_factor]
  have hz : f.val 0 (c.val * archMatrixInsertion F ζ hζ a) =
      literalArchProduct F ζ hζ K f c a := by
    unfold literalArchProduct
    rw [← literal_archMatrixInsertion]
    rw [(archMatrixInsertion_commutes_finite F ζ hζ a c).eq]
  rw [hz, he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [literalLocalDeformation, Finset.prod_mul_distrib]
  ring

end DedekindZetaZeroFree.SheetRescaling

end
