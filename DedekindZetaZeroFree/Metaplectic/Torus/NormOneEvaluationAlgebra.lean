module

public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData
public import DedekindZetaZeroFree.RepresentationTheory.RankOne.Borel.TorusRetraction
public import DedekindZetaZeroFree.Eisenstein.Residues.GlobalResidualData
public import DedekindZetaZeroFree.Metaplectic.Intertwining.TorusCovariance.FiniteAndAdelicHaarCharacters

@[expose] public section

noncomputable section
open scoped NumberField Classical NNReal
open MeasureTheory
namespace DedekindZetaZeroFree.FourierContinuation.NormOneTorusAlgebra
open KPGlobalResidualConstruction
open _root_.DedekindZetaZeroFree.KPMsRationalCompactCrossPairing.ActualWeylFibreProof renaming p_weyl → p_weyl
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
local notation "W" => KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ (KPCubicCoverConstruction.adelicW F ζ hζ)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def rightEvaluation (t : KPGlobalTorusFunctionData.E F ζ hζ) : KPGlobalTorusFunctionData.G F ζ hζ :=
  (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ t).val

private theorem W_squared : W * W = 1 := by
  rw [← map_mul]
  have he : KPCubicCoverConstruction.adelicW F ζ hζ * KPCubicCoverConstruction.adelicW F ζ hζ = 1 := by
    simpa only [KPCubicCoverConstruction.adelicW,pow_two] using KPRationalAdelicSplitting.W_sq F ζ hζ
  rw [he,map_one]

private theorem W_rightEvaluation (t : KPGlobalTorusFunctionData.E F ζ hζ) :
    W * rightEvaluation F ζ hζ t = t.val * W := by
  change W * (W * t.val * W⁻¹) = t.val * W
  have hw : W⁻¹ = W := inv_eq_of_mul_eq_one_left (W_squared F ζ hζ)
  rw [hw]
  calc W * (W * t.val * W) = (W*W)*t.val*W := by group
       _ = t.val*W := by rw [W_squared,one_mul]

theorem chamber_rightEvaluation (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (x : A F) (g : KPGlobalTorusFunctionData.G F ζ hζ) :
    W * KPGlobalTorusFunctionData.N F ζ hζ x * (rightEvaluation F ζ hζ t * g) =
      t.val * (W * KPGlobalTorusFunctionData.N F ζ hζ
        (x * (KPGlobalTorusFunctionData.p F ζ hζ
          (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ t))⁻¹.val) * g) := by
  let u := KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ t
  have hn := ActualBorelRetraction.torus_conjugates_root F ζ hζ u
    (x * (KPGlobalTorusFunctionData.p F ζ hζ u)⁻¹.val)
  have hx : (KPGlobalTorusFunctionData.p F ζ hζ u : A F) *
      (x * (KPGlobalTorusFunctionData.p F ζ hζ u)⁻¹.val) = x := by
    calc _ = x * ((KPGlobalTorusFunctionData.p F ζ hζ u : A F) *
        (KPGlobalTorusFunctionData.p F ζ hζ u)⁻¹.val) := by ring
         _ = x := by rw [← Units.val_mul,mul_inv_cancel,Units.val_one,mul_one]
  rw [hx] at hn
  have hr : KPGlobalTorusFunctionData.N F ζ hζ x * u.val =
      u.val * KPGlobalTorusFunctionData.N F ζ hζ
        (x * (KPGlobalTorusFunctionData.p F ζ hζ u)⁻¹.val) := by
    rw [← hn]
    group
  change W * KPGlobalTorusFunctionData.N F ζ hζ x * (u.val*g) = _
  rw [← mul_assoc, mul_assoc W,hr,← mul_assoc W]
  have hw : W * u.val = t.val*W := W_rightEvaluation F ζ hζ t
  rw [hw]
  dsimp [u]
  group

theorem rightEvaluation_abs (t : KPGlobalTorusFunctionData.E F ζ hζ)
    (ht : KPGlobalTorusFunctionData.delta F ζ hζ t = 1) :
    KPGlobalTorusFunctionData.ideleAbs F
      (KPGlobalTorusFunctionData.p F ζ hζ
        (KPMsRationalCompactCrossPairing.weylTorusConjugation F ζ hζ t)) = 1 := by
  rw [p_weyl, map_inv]
  change (KPGlobalTorusFunctionData.delta F ζ hζ t)⁻¹ = 1
  rw [ht, inv_one]
end DedekindZetaZeroFree.FourierContinuation.NormOneTorusAlgebra

end
