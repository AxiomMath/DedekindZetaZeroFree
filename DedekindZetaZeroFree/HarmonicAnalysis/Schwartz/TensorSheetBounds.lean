module

public import DedekindZetaZeroFree.Adeles.Quotients.NormSheets.RemainingCoordinateIntegrals
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.LocalUnitsTensorIntegrability

@[expose] public section

namespace DedekindZetaZeroFree.SchwartzNormSheetEnvelope
noncomputable section
open scoped Classical NumberField
open NumberField IsDedekindDomain MeasureTheory
variable {F : Type} [Field F] [NumberField F]

theorem raw_sheet_modulus (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) (t : A.G1) :
    ProbeWeight.modulus F A.Sf (ProbeSheetFourierMellinBounds.sheetPointRaw A T t) = T := by
  have hm (x y : A.G) : A.norm (x * y) = A.norm x * A.norm y := by
    simp only [SArithmeticData.norm, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply,
      Units.val_mul, norm_mul, mul_pow, Finset.prod_mul_distrib]
    ring
  unfold ProbeSheetFourierMellinBounds.sheetPointRaw ProbeSheetFourierMellinBounds.ellRaw
  rw [dif_pos hT, ← map_mul]
  change A.norm (t.val * A.radialSection T hT) = T
  rw [hm, show A.norm t.val = 1 from t.property, A.norm_radialSection, one_mul]

theorem raw_sheet_continuous (A : SArithmeticData F) (T : ℝ) (hT : 0 < T) :
    Continuous (fun t : A.G1 => (ProbeSheetFourierMellinBounds.sheetPointRaw A T t).val) := by
  have he : Continuous (ProbeSheetFourierMellinBounds.localUnitsRaw A) := by
    change Continuous (Homeomorph.prodUnits.symm ∘
      (ContinuousMulEquiv.piUnits.symm.toHomeomorph.prodCongr
        ContinuousMulEquiv.piUnits.symm.toHomeomorph))
    fun_prop
  simp only [ProbeSheetFourierMellinBounds.sheetPointRaw, ProbeSheetFourierMellinBounds.ellRaw, dif_pos hT,
    Units.val_mul]
  exact (Units.continuous_val.comp (he.comp continuous_subtype_val)).mul continuous_const

theorem complex_product_modulus (A : SArithmeticData F)
    (y : (SLocalProduct F A.Sf)ˣ) :
    ProbeWeight.modulus F A.Sf y =
      (∏ v : {v : InfinitePlace F // v.IsComplex},
        ‖((InfiniteAdeleRing.ringEquiv_mixedSpace F y.val.1).2 v)‖ ^ (2 : ℕ)) *
      ∏ v : ↥A.Sf, ‖y.val.2 v‖ := by
  unfold ProbeWeight.modulus
  congr 1
  apply Fintype.prod_equiv (Equiv.subtypeUnivEquiv A.complex_place).symm
  intro v
  change ‖y.val.1 v‖ ^ 2 = ‖InfinitePlace.Completion.extensionEmbedding v (y.val.1 v)‖ ^ 2
  have hn := (InfinitePlace.Completion.isometry_extensionEmbedding v).dist_eq (y.val.1 v) 0
  simpa only [map_zero, dist_zero_right] using congrArg (fun r : ℝ => r ^ 2) hn.symm

end
end DedekindZetaZeroFree.SchwartzNormSheetEnvelope
