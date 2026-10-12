module

public import DedekindZetaZeroFree.Eisenstein.Residues.ZeroProfiles.FiniteCovariance
public import DedekindZetaZeroFree.Eisenstein.Residues.RealizationAndPeriods

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {K : Subgroup (G F ζ hζ)}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

structure LiteralResidueFamily (hK : IwasawaCompact F ζ hζ K) where
  E : Flat F ζ hζ K → ℂ → Functions F ζ hζ
  cleared : Flat F ζ hζ K → ℂ → Functions F ζ hζ
  germ : ExceptionalGerm F ζ hζ K E cleared
  normal : ∀ f g, MeromorphicNFOn (fun z => E f z g) KPContinuation.spectralDomain

def ownedLiteralResidueFamily (hK : IwasawaCompact F ζ hζ K) : LiteralResidueFamily hK := by
  let h := SharedSource.literal_exceptional_germ_exists K hK
  exact ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1,
    h.choose_spec.choose_spec.2⟩

def LiteralResidueFamily.residue {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK) : literalZeroProfiles K →ₗ[ℂ] Functions F ζ hζ :=
  literalZeroProfileResidue hK A.E A.cleared A.germ (fun f g => (A.normal f g).meromorphicOn)

@[simp] theorem LiteralResidueFamily.residue_flat {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK) (f : literalFlatModule K) :
    A.residue (literalZeroProfileEquiv hK f) = A.cleared (asLiteralFlat f) 0 :=
  literalZeroProfileResidue_flat hK A.E A.cleared A.germ
    (fun f g => (A.normal f g).meromorphicOn) f

theorem LiteralResidueFamily.residue_finite {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK) (q : KPFinitePlace F)
    (a : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr q))
    (f : literalZeroProfiles K) (g : G F ζ hζ) :
    A.residue (literalZeroProfileFinite hK q a f) g =
      A.residue f (g * KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.localInjection F ζ hζ (Sum.inr q) a)) :=
  literalZeroProfileResidue_finite hK A.E A.cleared A.germ
    (fun f g => (A.normal f g).meromorphicOn) q a f g

section Selected
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable {R : PrincipalMellin.ActualRecipe S η} {Q : AdmissibleFlatSources R}

def selectedZeroProfile (Q : AdmissibleFlatSources R) (v : R.A.UnitQuotient) :
    literalZeroProfiles Q.K :=
  literalZeroProfileEquiv Q.iwasawa (Q.flat v : literalFlatModule Q.K)

@[simp] theorem selectedZeroProfile_val (v : R.A.UnitQuotient) :
    (selectedZeroProfile Q v).val = (Q.flat v).val 0 := rfl

theorem LiteralResidueFamily.residue_selected
    (A : LiteralResidueFamily Q.iwasawa) (T : Realization R Q) (v : R.A.UnitQuotient) :
    A.residue (selectedZeroProfile Q v) = T.theta v := by
  rw [selectedZeroProfile, A.residue_flat]
  exact (SharedSource.realizationScalarGerm_cleared T v 0
    (Metric.mem_ball_self T.radius_pos)).symm.trans
    (SharedSource.scalar_residue_eq_literal_ancestor A.E A.cleared A.germ A.normal
      (SharedSource.realizationScalarGerm T v)) |>.symm

end Selected
end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
