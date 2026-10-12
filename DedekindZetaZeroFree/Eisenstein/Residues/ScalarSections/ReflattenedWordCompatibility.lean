module

public import DedekindZetaZeroFree.Eisenstein.Residues.TensorProducts.ResidueFamiliesAndPeriods
public import DedekindZetaZeroFree.Eisenstein.Residues.IteratedLiePreimages

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open Filter
namespace DedekindZetaZeroFree.FourierContinuation.TensorActionSource
open KPLiteralRaw RootDerivatives KPContActualSphericalRightFieldIdentification
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem flatScalarResidue_eq_of_zero
    {K L : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) (hL : IwasawaCompact F ζ hζ L)
    (f : Flat F ζ hζ K) (g : Flat F ζ hζ L)
    (A : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f) (B : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ g)
    (hzero : f.val 0 = g.val 0) : A.numerator 0 = B.numerator 0 := by
  obtain ⟨u, Au, hu, hAu⟩ := canonical_flat_residue F ζ hζ hK f A
  obtain ⟨v, Bv, hv, hBv⟩ := canonical_flat_residue F ζ hζ hL g B
  have he : u = v := by
    apply Subtype.ext
    funext s x
    rw [hu, hv, hzero]
  subst v
  funext x
  exact (hAu x).symm.trans ((Au.value_unique Bv x).trans (hBv x))

def LiteralResidueFamily.scalarCertificate
    {K : Subgroup (G F ζ hζ)} {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK) (f : Flat F ζ hζ K) :
    _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f where
  E := A.E f
  meromorphic := fun x => (A.normal f x).meromorphicOn
  chamber := A.germ.1 f
  radius := (A.germ.2 f).choose_spec.choose
  radius_pos := by
    have H := (A.germ.2 f).choose_spec.choose_spec
    exact H.2.2.2.1
  numerator := A.cleared f
  analytic := by
    have H := (A.germ.2 f).choose_spec.choose_spec
    exact H.2.2.2.2.2.2.2
  clears := fun x => by
    have H := (A.germ.2 f).choose_spec.choose_spec
    have hr := H.2.2.2.1
    have hc := H.2.2.2.2.2.2.1
    filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr),
      self_mem_nhdsWithin] with z hz hn
    exact congrFun (hc z hz hn) x

theorem LiteralResidueFamily.residue_eq_certificate
    {K L : Subgroup (G F ζ hζ)} {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK) (hL : IwasawaCompact F ζ hζ L)
    (p : literalZeroProfiles K) (f : Flat F ζ hζ L)
    (B : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f) (hzero : p.val = f.val 0) :
    A.residue p = B.numerator 0 := by
  let g := (literalZeroProfileEquiv hK).symm p
  have hp : literalZeroProfileEquiv hK g = p :=
    (literalZeroProfileEquiv hK).apply_symm_apply p
  rw [← hp, A.residue_flat]
  exact flatScalarResidue_eq_of_zero hK hL (asLiteralFlat g) f
    (A.scalarCertificate (asLiteralFlat g)) B
    ((congrArg Subtype.val hp).trans hzero)

theorem LiteralResidueFamily.residue_word_of_zero
    {K : Subgroup (G F ζ hζ)} {hK : IwasawaCompact F ζ hζ K}
    (A : LiteralResidueFamily hK)
    (w : List (Fin (groupDimension F))) (p q : literalZeroProfiles K)
    (hzero : q.val = actualRightWord F ζ hζ w p.val) :
    A.residue q = actualRightWord F ζ hζ w (A.residue p) := by
  let f := (literalZeroProfileEquiv hK).symm p
  have hp : literalZeroProfileEquiv hK f = p :=
    (literalZeroProfileEquiv hK).apply_symm_apply p
  have hf0 : (asLiteralFlat f).val 0 = p.val := congrArg Subtype.val hp
  obtain ⟨v, Cv, hv0, _, hCv⟩ := native_word_flat_residue F ζ hζ hK
    (asLiteralFlat f) (A.scalarCertificate (asLiteralFlat f)) w
  have hq0 : q.val = v.val 0 := by rw [hv0, hf0]; exact hzero
  rw [A.residue_eq_certificate
    (PrincipalOfKP.iwasawaCompactSubgroupMax_isIwasawa F ζ hζ) q v Cv hq0, hCv]
  have he : A.residue p = A.cleared (asLiteralFlat f) 0 := by
    rw [← hp, A.residue_flat]
  rw [he]
  rfl

end DedekindZetaZeroFree.FourierContinuation.TensorActionSource

end
