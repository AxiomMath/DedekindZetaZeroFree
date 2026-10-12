module

public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.Spherical.ScalarRealization

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical NumberField
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters
open ResidualSphericalGeometry KPContSectorSmoothFramesSupport
open KPContSectorLineL2Isometry KPContSectorFixedPushforwardSupport
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (V : KPMsFixedHaarDisintegration.Level F ζ hζ)
variable (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
variable (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
variable (H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P)

theorem represented_original_memLp
    (Z : smoothSections F ζ hζ V R P H)
    (z : KPContSectorClosedLpSubspace.H F ζ hζ R V)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z) :
    MemLp (originalScalar F ζ hζ V R P H Z) 2 R.quotientHaar := by
  obtain ⟨hm, _⟩ := hz
  rw [scalarRepresentative_eq_symm] at hm
  have hp : MeasurePreserving (KPContSectorQuotientRelationsComparison.piTilde F ζ hζ V)
      R.quotientHaar (coveredMeasure F ζ hζ R V) :=
    ⟨(KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ V).measurable,rfl⟩
  exact hm.comp_measurePreserving hp

theorem original_pairing_eq_inner
    (Z T : smoothSections F ζ hζ V R P H)
    (z t : KPContSectorClosedLpSubspace.H F ζ hζ R V)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z)
    (ht : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H T.val t) :
    (∫ x, star (originalScalar F ζ hζ V R P H Z x) *
      originalScalar F ζ hζ V R P H T x ∂ R.quotientHaar) = inner ℂ z t := by
  obtain ⟨hZ, heZ⟩ := hz
  obtain ⟨hT, heT⟩ := ht
  let s := (scalarRepresentative F ζ hζ V R P H Z.val).val
  let u := (scalarRepresentative F ζ hζ V R P H T.val).val
  have hi : inner ℂ z t = ∫ x, star (s x) * u x ∂ coveredMeasure F ζ hζ R V := by
    change inner ℂ (z : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V)
      (t : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V) = _
    rw [← heZ, ← heT]
    apply integral_congr_ae
    filter_upwards [hZ.coeFn_toLp, hT.coeFn_toLp] with x hx hy
    rw [hx, hy, RCLike.inner_apply']
    rfl
  rw [hi]
  have hs : s = ((smoothS F ζ hζ V R P H).symm Z).val.val := by
    dsimp [s]
    rw [scalarRepresentative_eq_symm]
    rfl
  have hu : u = ((smoothS F ζ hζ V R P H).symm T).val.val := by
    dsimp [u]
    rw [scalarRepresentative_eq_symm]
    rfl
  have hj := (hZ.star.integrable_mul hT).aestronglyMeasurable
  have hm := integral_map
    (KPContSectorQuotientRelationsComparison.piTilde_continuous F ζ hζ V).aemeasurable hj
  simpa only [coveredMeasure, s, u, hs, hu, originalScalar, Function.comp_def, Pi.mul_apply, Pi.star_apply] using hm.symm

theorem original_pairing_zero_of_reverse_inner_zero
    (Z T : smoothSections F ζ hζ V R P H)
    (z t : KPContSectorClosedLpSubspace.H F ζ hζ R V)
    (hz : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H Z.val z)
    (ht : KPContActualSmoothLineGluing.Represents F ζ hζ V R P H T.val t)
    (hi : inner ℂ t z = 0) :
    (∫ x, star (originalScalar F ζ hζ V R P H Z x) *
      originalScalar F ζ hζ V R P H T x ∂ R.quotientHaar) = 0 := by
  rw [original_pairing_eq_inner F ζ hζ V R P H Z T z t hz ht]
  change inner ℂ (z : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V)
    (t : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V) = 0
  change inner ℂ (t : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V)
    (z : KPContSectorClosedLpSubspace.CoveredL2 F ζ hζ R V) = 0 at hi
  exact inner_eq_zero_symm.mp hi

end DedekindZetaZeroFree.FourierContinuation.ResidualHilbertCenters

end
