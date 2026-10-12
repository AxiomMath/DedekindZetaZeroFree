module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.WeightedCompactTrivialization

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPLocalPrincipalSeries KPRankOneCenterInducedDiagonalComparison
open KPRankOneShellContinuation KPActualScalarBinding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

theorem actual_kernelW_sign_flip (S : ActualKPBinding F ζ hζ q) (ε : Sign) :
    kernelW (KPExceptionalRaw.LocalField F q) S.borel ε =
      kernelW (KPExceptionalRaw.LocalField F q) S.borel (targetSign ε) := by
  have hw : S.borel.liftedW ^ 2 = 1 := by
    rw [(S.openCell S.polarization).weyl_eq]
    simpa only [KPRankOneOpenCellKernel.signedWeyl,
      KPRankOneOpenCellKernel.signedWeyl_eq_prescribed_signed, KPPGLLocalCover.signedW] using
      KPPGLLocalCover.signedW_sq F ζ hζ (Sum.inr q)
  have hi : S.borel.liftedW⁻¹ = S.borel.liftedW :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hw)
  cases ε <;> simp [targetSign, kernelW, hi]

theorem actual_weighted_reflection_chamber (ε : Sign) (s : ℂ) :
    convergenceHalfPlane ε s ↔ convergenceHalfPlane (targetSign ε) (-s - 1/3) := by
  cases ε <;> simp [convergenceHalfPlane, targetSign] <;> constructor <;> intro h <;> linarith

variable (S : ActualKPBinding F ζ hζ q) (I : IwasawaData S.borel)
variable (E : CenterModule S.heisenberg ≃ₗ[ℂ] CenterModule S.heisenberg)
variable (hE : ∀ (f : CenterModule S.heisenberg)
  (h : KPExceptionalRaw.actualTorus F ζ hζ q),
  (E f).val h = normPower (KPExceptionalRaw.LocalField F q)
    (S.borel.coordinate h) (1/3) * f.val (S.borel.weyl h))
variable (J : CompactOpenLevel (KPRankOneOpenCellKernel.Cover F ζ hζ q))
variable (hJ : J.toOpenSubgroup ≤ I.compact.toOpenSubgroup)

def actualWeightedLevelFlip (ε : Sign) :
    centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J ≃ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel I (targetSign ε) J :=
  match ε with
  | .plus => Classical.choose (Classical.choose_spec
      (actual_weighted_compact_trivialization F ζ hζ q S I E hE J hJ))
  | .minus => Classical.choose
      (actual_weighted_compact_trivialization F ζ hζ q S I E hE J hJ)

theorem actualWeightedLevelFlip_apply (ε : Sign)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) :
    (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ).val.val k = E (φ.val.val k) := by
  have hs := Classical.choose_spec (Classical.choose_spec
    (actual_weighted_compact_trivialization F ζ hζ q S I E hE J hJ))
  cases ε
  · exact hs.2.2.1 φ k
  · exact hs.2.1 φ k

theorem actual_weighted_signed_kernel (ε : Sign) (s : ℂ)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J)
    (x : KPExceptionalRaw.LocalField F q)
    (g : KPRankOneOpenCellKernel.Cover F ζ hζ q)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    (E ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
      (sourceSign ε) (sourceParameter ε s) φ.val).val
      (kernelW (KPExceptionalRaw.LocalField F q) S.borel ε *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : KPRankOneOpenCellKernel.Cover F ζ hζ q) * g))).val h =
    ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
      (sourceSign (targetSign ε)) (sourceParameter (targetSign ε) (-s - 1/3))
      (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ).val).val
      (kernelW (KPExceptionalRaw.LocalField F q) S.borel (targetSign ε) *
        (S.borel.upperRoot (Multiplicative.ofAdd x) : KPRankOneOpenCellKernel.Cover F ζ hζ q) * g)).val h := by
  rw [actual_kernelW_sign_flip F ζ hζ q S ε]
  have hs := Classical.choose_spec (Classical.choose_spec
    (actual_weighted_compact_trivialization F ζ hζ q S I E hE J hJ))
  cases ε
  · have hp : sourceParameter (targetSign .plus) (-s - 1/3) = s + 1/3 := by
      simp [sourceParameter, targetSign, add_comm]
    rw [hp]
    exact hs.2.2.2.2 s φ _ h
  · exact hs.2.2.2.1 s φ _ h

theorem actual_weighted_integral_coordinate (μ : Measure (KPExceptionalRaw.LocalField F q))
    (ε : Sign) (s : ℂ)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J)
    (g : KPRankOneOpenCellKernel.Cover F ζ hζ q)
    (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
      centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ ε s
        (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
          (sourceSign ε) (sourceParameter ε s) φ.val) g (S.borel.weyl h) =
    centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ (targetSign ε) (-s - 1/3)
      (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
        (sourceSign (targetSign ε)) (sourceParameter (targetSign ε) (-s - 1/3))
        (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ).val) g h := by
  unfold centerIntegralCoordinate
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  have hh := actual_weighted_signed_kernel F ζ hζ q S I E hE J hJ ε s φ x g h
  rw [hE] at hh
  simpa only [(S.openCell S.polarization).upper_eq] using hh

theorem actual_weighted_numerator_chamber
    (μ : Measure (KPExceptionalRaw.LocalField F q)) (ε : Sign)
    (p : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J ε)
    (p' : CenterLevelLaurentOperator F ζ hζ q S.heisenberg S.borel I J (targetSign ε))
    (hp : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ ε p)
    (hp' : IsCenterLevelNumerator F ζ hζ q S.heisenberg S.borel I J μ (targetSign ε) p')
    (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) (h : KPExceptionalRaw.actualTorus F ζ hζ q) :
    denominator (KPExceptionalRaw.LocalField F q) (targetSign ε) (-s - 1/3) *
      normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J ε p
        (evaluationUnit (KPExceptionalRaw.LocalField F q) ε s) φ).val.val k).val (S.borel.weyl h) =
    denominator (KPExceptionalRaw.LocalField F q) ε s *
      ((centerEvaluate F ζ hζ q S.heisenberg S.borel I J (targetSign ε) p'
        (evaluationUnit (KPExceptionalRaw.LocalField F q) (targetSign ε) (-s - 1/3))
        (actualWeightedLevelFlip F ζ hζ q S I E hE J hJ ε φ)).val.val k).val h := by
  rw [hp s hs φ k (S.borel.weyl h),
    hp' (-s - 1/3) ((actual_weighted_reflection_chamber ε s).mp hs)]
  have hi := actual_weighted_integral_coordinate F ζ hζ q S I E hE J hJ μ ε s φ k h
  calc
    _ = denominator (KPExceptionalRaw.LocalField F q) ε s *
        (denominator (KPExceptionalRaw.LocalField F q) (targetSign ε) (-s - 1/3) *
          (normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1/3) *
            centerIntegralCoordinate F ζ hζ q S.heisenberg S.borel μ ε s
              (centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
                (sourceSign ε) (sourceParameter ε s) φ.val) k (S.borel.weyl h))) := by ring
    _ = _ := by rw [hi]

end
end DedekindZetaZeroFree.KPActualResidueSources
