module

public import DedekindZetaZeroFree.Adeles.Lattices.FractionalIdealTraceDual

@[expose] public section

noncomputable section
open scoped Classical nonZeroDivisors
open NumberField MeasureTheory

namespace DedekindZetaZeroFree
namespace PoissonArch

variable (F : Type) [Field F] [NumberField F]

instance traceMeasure_isAddHaarMeasure : (traceMeasure F).IsAddHaarMeasure := by
  unfold traceMeasure
  apply Measure.IsAddHaarMeasure.smul volume
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    unfold haarScalar
    positivity
  · exact ENNReal.ofReal_ne_top

def covolume (I : NonzeroFractionalIdeal F) : ℝ :=
  ZLattice.covolume (idealLattice F I) (traceMeasure F)

theorem traceMeasure_map_toMixed :
    Measure.map (NumberField.mixedEmbedding.euclidean.toMixed F) (traceMeasure F) =
      ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F) •
        (volume : Measure (NumberField.mixedEmbedding.mixedSpace F)) := by
  rw [traceMeasure, Measure.map_smul]
  · rw [(NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed F).map_eq]
    rfl
  · exact (NumberField.mixedEmbedding.euclidean.toMixed F).continuous.measurable.aemeasurable

theorem euclidean_covolume_eq (I : NonzeroFractionalIdeal F) :
    ZLattice.covolume (idealLattice F I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) *
        (2 : ℝ)⁻¹ ^ InfinitePlace.nrComplexPlaces F * Real.sqrt |(NumberField.discr F : ℝ)| := by
  rw [idealLattice, ZLattice.covolume_comap _ _ _
    (NumberField.mixedEmbedding.euclidean.volumePreserving_toMixed F)]
  exact NumberField.mixedEmbedding.covolume_idealLattice F I

theorem covolume_eq_haarScalar_mul_euclidean (I : NonzeroFractionalIdeal F) :
    covolume F I = haarScalar F * ZLattice.covolume (idealLattice F I) := by
  let b := Module.Free.chooseBasis ℤ (idealLattice F I)
  rw [covolume, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain b (traceMeasure F)),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain b volume)]
  simp only [Measure.real, traceMeasure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul]
  rw [ENNReal.toReal_ofReal (by unfold haarScalar; positivity)]

theorem covolume_eq_sqrt_discr_mul_absNorm (I : NonzeroFractionalIdeal F) :
    covolume F I = Real.sqrt |(NumberField.discr F : ℝ)| *
      (FractionalIdeal.absNorm (I : FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) := by
  rw [covolume_eq_haarScalar_mul_euclidean, euclidean_covolume_eq, haarScalar]
  have h : (2 : ℝ) ^ InfinitePlace.nrComplexPlaces F *
      (2 : ℝ)⁻¹ ^ InfinitePlace.nrComplexPlaces F = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((2 : ℝ) ^ InfinitePlace.nrComplexPlaces F *
        (2 : ℝ)⁻¹ ^ InfinitePlace.nrComplexPlaces F) *
        Real.sqrt |(NumberField.discr F : ℝ)| *
        (FractionalIdeal.absNorm (I : FractionalIdeal (RingOfIntegers F)⁰ F) : ℝ) := by ring
    _ = _ := by rw [h, one_mul]

end PoissonArch
end DedekindZetaZeroFree

end
