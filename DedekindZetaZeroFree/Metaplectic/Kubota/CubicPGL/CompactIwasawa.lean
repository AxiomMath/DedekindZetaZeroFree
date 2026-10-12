module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicPGL.IwasawaCoverFactorization
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicPGL.LocalBorelData

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.ActualFiniteBorel
open KPLocalPrincipalSeries KPLocalStoneVonNeumann
noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

local instance : ValuativeRel (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F q
local instance : IsNonarchimedeanLocalField (q.adicCompletion F) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F q

abbrev fullCompact := KPRankOneCartanGeometry.coveredK0 F ζ hζ q

def fullCompactLevel (m : ℕ) (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ q m
    CompactOpenLevel (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) := by
  letI := KPPGLLocalCover.finiteTopology F ζ hζ q m
  exact {
    toOpenSubgroup := {
      toSubgroup := fullCompact F ζ hζ q
      isOpen' := (KPRankOneCartanGeometry.coveredK0_compact_open F ζ hζ q m hm).2 }
    isCompact := (KPRankOneCartanGeometry.coveredK0_compact_open F ζ hζ q m hm).1 }

theorem actual_compact_iwasawa (m : ℕ)
    (hm : KPLocalChartTopology.MatrixChartDepth F q m) :
    letI := KPPGLLocalCover.finiteTopology F ζ hζ q m
    letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
      (KPPGLLocalCover.finite_topological_cover F ζ hζ q m hm).2.2.1
    ∀ {D : Type} [CommGroup D] [Finite D]
      (T : LocalHeisenbergData (KPLocalSmoothRepresentation.Torus F ζ hζ q) D)
      (A : LocalBorelData (K := q.adicCompletion F)
        (G := KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) T),
      A.B = KPLocalSmoothRepresentation.Borel F ζ hζ q →
      (∀ (b : A.B) (hb : (b : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) ∈
          KPLocalSmoothRepresentation.Borel F ζ hζ q),
        A.coordinate (A.retract b) = KPRankOneInduction.borelRatio F q
          ⟨KPLocalSmoothRepresentation.projection F ζ hζ q b,
            hb⟩) →
      ∃ I : IwasawaData A,
        I.compact = fullCompactLevel F ζ hζ q m hm := by
  classical
  letI := KPPGLLocalCover.finiteTopology F ζ hζ q m
  letI : IsTopologicalGroup (KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :=
    (KPPGLLocalCover.finite_topological_cover F ζ hζ q m hm).2.2.1
  intro D _ _ T A hB hratio
  let L := fullCompactLevel F ζ hζ q m hm
  have hex (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) :
      ∃ b : A.B, ∃ k : L.toOpenSubgroup, g = (b : _) * (k : _) := by
    obtain ⟨b, k, hg⟩ := IwasawaProof.covered_factor F ζ hζ q g
    refine ⟨⟨b.val, hB.symm ▸ b.property⟩, ⟨k.val, k.property⟩, hg⟩
  let bp (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) : A.B :=
    if hg : g ∈ L.toOpenSubgroup then 1 else Classical.choose (hex g)
  let kp (g : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) : L.toOpenSubgroup :=
    if hg : g ∈ L.toOpenSubgroup then ⟨g, hg⟩
    else Classical.choose (Classical.choose_spec (hex g))
  refine ⟨{
    compact := L
    borelPart := bp
    compactPart := kp
    decomposition := ?_
    borelPart_compact := ?_
    compactPart_compact := ?_
    intersection_norm := ?_ }, rfl⟩
  · intro g
    by_cases hg : g ∈ L.toOpenSubgroup
    · simp [bp, kp, hg]
    · simpa [bp, kp, hg] using
        Classical.choose_spec (Classical.choose_spec (hex g))
  · intro k
    simp [bp, k.property]
  · intro k
    simp [kp, k.property]
  · intro b hb
    have hbb : (b : KPPGLLocalCover.CubicPGL2 F ζ hζ (Sum.inr q)) ∈
        KPLocalSmoothRepresentation.Borel F ζ hζ q := hB ▸ b.property
    rw [hratio b hbb]
    exact IwasawaProof.covered_intersection F ζ hζ q ⟨b.val, hbb⟩ hb

end
end DedekindZetaZeroFree.ActualFiniteBorel
