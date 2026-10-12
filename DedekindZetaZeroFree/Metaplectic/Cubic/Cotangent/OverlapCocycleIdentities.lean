module

public import DedekindZetaZeroFree.Metaplectic.Cubic.Cotangent.OverlapMetricAndPhase

@[expose] public section

noncomputable section
open scoped Classical NumberField

namespace DedekindZetaZeroFree.KPContCotangentActualGroupoidIdentities

open KPContCotangentActualOverlap

variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable {R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ}
variable {P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ}
variable {H : KPMsFixedHaarDisintegration.AllLevels F ζ hζ R P}
variable {i : Fin (H.atlas U).componentCount}
variable {a b c : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
  (U := U) (R := R) (P := P) (H := H) i}

private theorem left_inverse (places) (x : M F) :
    labeledAInv places (labeledA places x) = x := by
  simp [labeledAInv, labeledA]

private theorem right_inverse (places) (x : KPCuspGenuineMonodromy.SymmetricSpace F) :
    labeledA places (labeledAInv places x) = x := by
  funext k
  simp [labeledA, labeledAInv]

private theorem coordinateMap_one (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : coordinateMap a a 1 = id := by
  funext x
  simp [coordinateMap, left_inverse]

private theorem coordinateMap_mul
    (θ ψ : KPCuspGenuineMonodromy.Component F ζ hζ U ((H.atlas U).representative i)) :
    coordinateMap a c (θ * ψ) = coordinateMap b c θ ∘ coordinateMap a b ψ := by
  funext x
  simp only [Function.comp_apply, coordinateMap, right_inverse, Subgroup.coe_mul]
  congr 1
  rw [smul_smul]
  congr 1
  group

theorem identity_psi (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) : (identity a).psi = id :=
  coordinateMap_one a

theorem comp_psi (θ : Arrow b c) (ψ : Arrow a b) :
    (comp θ ψ).psi = θ.psi ∘ ψ.psi := coordinateMap_mul θ.gamma ψ.gamma

theorem identity_phase (a : LiftedChart (F := F) (ζ := ζ) (hζ := hζ)
    (U := U) (R := R) (P := P) (H := H) i) (x : M F) :
    (identity a).phase x = 1 := by
  simp only [Arrow.phase, identity_psi, id_eq]
  change (KPCuspGenuineMonodromy.chi F ζ hζ
    (a.splitting x * 1 * (a.splitting x)⁻¹) : ℂ) = 1
  simp

theorem comp_phase (θ : Arrow b c) (ψ : Arrow a b) (x : M F) :
    (comp θ ψ).phase x = θ.phase (ψ.psi x) * ψ.phase x := by
  simp only [Arrow.phase, comp_psi, Function.comp_apply]
  change (KPCuspGenuineMonodromy.chi F ζ hζ
    (c.splitting (θ.psi (ψ.psi x)) * (θ.root * ψ.root) * (a.splitting x)⁻¹) : ℂ) = _
  rw [← Units.val_mul, ← map_mul]
  congr 2
  group

end DedekindZetaZeroFree.KPContCotangentActualGroupoidIdentities

end
