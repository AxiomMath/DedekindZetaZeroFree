module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.CanonicalFlat

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
namespace DedekindZetaZeroFree.RootDerivatives
open KPLiteralRaw
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

 theorem FlatScalarResidue.zero_of_zero_section {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f) (hf : f.val 0 = 0) : A.numerator 0 = 0 := by
  have hz (s : ℂ) (g : G F ζ hζ) : f.val s g = 0 := by
    rw [KPLiteralChamber.JointProfile.literal_flat_multiplier_formula F ζ hζ K hK f,
      hf]
    simp
  let B : FlatScalarResidue F ζ hζ f := {
    E := fun _ => 0
    meromorphic := fun _ s _ => MeromorphicAt.const 0 s
    chamber := by
      intro s hs g
      simp [eisenstein, hz]
    radius := 1
    radius_pos := by norm_num
    numerator := fun _ => 0
    analytic := fun _ => analyticOnNhd_const
    clears := fun _ => Filter.Eventually.of_forall (fun _ => by simp) }
  funext g
  exact A.value_unique B g

 theorem FlatScalarResidue.zero_section_ne_zero {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f) (hA : A.numerator 0 ≠ 0) : f.val 0 ≠ 0 :=
  fun hf => hA (A.zero_of_zero_section hK hf)

 theorem flat_nontrivial_of_residue {K : Subgroup (G F ζ hζ)}
    (hK : IwasawaCompact F ζ hζ K) {f : Flat F ζ hζ K}
    (A : _root_.DedekindZetaZeroFree.RootDerivatives.FlatScalarResidue F ζ hζ f) (hA : A.numerator 0 ≠ 0) :
    Nontrivial (Flat F ζ hζ K) := by
  refine ⟨⟨f, _root_.DedekindZetaZeroFree.FiniteWhittakerProjectors.FlatFiniteSum.zero F ζ hζ K, ?_⟩⟩
  intro h
  apply A.zero_section_ne_zero hK hA
  rw [h]
  rfl

end DedekindZetaZeroFree.RootDerivatives

end
