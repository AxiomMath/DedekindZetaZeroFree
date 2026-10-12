module

public import DedekindZetaZeroFree.Eisenstein.Sections.LiteralSeries

@[expose] public section

noncomputable section
open scoped NumberField Classical Topology
open NumberField MeasureTheory ValuativeRel
namespace DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy
open KPLiteralRaw

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

theorem eisenstein_genuine (K : Subgroup (G F ζ hζ))
    (f : Flat F ζ hζ K) (s : ℂ) (hs : (1 : ℝ) / 3 < s.re)
    (ε : rootsOfUnity 3 F) (g : G F ζ hζ) :
    eisenstein F ζ hζ K f s
        (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * g) =
      (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) *
        eisenstein F ζ hζ K f s g := by
  let z := KPGlobalCenterRationalCharacter.centralRoot F ζ hζ ε
  let r : R F ζ hζ := ⟨z.val, Subgroup.mem_sup_right z.property⟩
  have hr : r.val.val = KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.centralRoot_formula F ζ hζ ε
  have hl : KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r =
      KPGlobalTorusFunctionData.iota F ζ hζ ε :=
    KPGlobalCenterRationalCharacter.lambdaR_genuine F ζ hζ ε r rfl
  have hp : KPGlobalTorusFunctionData.p F ζ hζ r.val = 1 := by
    have hker : KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε ∈
        (KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).ker := by
      rw [← KPAdelicCoverRestrictedProduct.pglCentralInjection_kernel F ζ hζ]
      exact ⟨ε, rfl⟩
    have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ r.val.val = 1 := by
      rw [hr]
      exact MonoidHom.mem_ker.mp hker
    unfold KPGlobalTorusFunctionData.p
    have ht : ((KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ).restrict
        (fun t ht => ht)) r.val =
          (1 : KPGlobalTorusFunctionData.ordinaryTorus F) := Subtype.ext hproj
    change KPGlobalTorusFunctionData.torusRatio F _ = 1
    rw [ht, map_one]
  have hd : KPGlobalTorusFunctionData.delta F ζ hζ r.val = 1 := by
    change KPGlobalTorusFunctionData.ideleAbs F (KPGlobalTorusFunctionData.p F ζ hζ r.val) = 1
    rw [hp, map_one]
  have hv (a : G F ζ hζ) : f.val s
      (KPAdelicCoverRestrictedProduct.pglCentralInjection F ζ hζ ε * a) =
      (KPGlobalTorusFunctionData.iota F ζ hζ ε : ℂ) * f.val s a := by
    have h := (f.property.1 s).2 r 0 a
    have hn : KPGlobalTorusFunctionData.N F ζ hζ 0 = 1 :=
      (KPGlobalTorusFunctionData.Nhom F ζ hζ).map_one
    simpa [hr, hd, hl, hn, KPGlobalExceptionalParameter.realLogPower] using h
  unfold eisenstein
  rw [← tsum_mul_left]
  apply tsum_congr
  intro c
  have hcentral := Subgroup.mem_center_iff.mp
    (KPAdelicCoverRestrictedProduct.pglCentralInjection_central F ζ hζ ⟨ε, rfl⟩)
    (rationalLift F ζ hζ (Quotient.out c))
  rw [← mul_assoc, hcentral, mul_assoc, hv]

end DedekindZetaZeroFree.KPLiteralExceptionalResidue.ResidueAutomorphy

end
