module

public import DedekindZetaZeroFree.Adeles.Characters.CompactAbelianAndAdelicUniqueness
public import DedekindZetaZeroFree.Eisenstein.SpectralTheory.IncomingCasimirEigenfunctions
public import DedekindZetaZeroFree.RepresentationTheory.PrincipalSeries.CompactPicture.RationalPeriodizationPairingData

@[expose] public section

noncomputable section
open scoped Classical NumberField ENNReal NNReal Topology BigOperators
open MeasureTheory

namespace DedekindZetaZeroFree.KPMsGreenFlux
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

abbrev Cover := KPMsFixedHaarDisintegration.Cover F ζ hζ
abbrev X := KPMsFixedHaarDisintegration.X F ζ hζ
abbrev K := NumberField.InfinitePlace F → KPCplxPrincipalSeriesCharts.compactSubgroup

instance : MeasurableSpace (K F) := borel _
instance : BorelSpace (K F) := ⟨rfl⟩

def compactInsertion (k : K F) : Cover F ζ hζ :=
  KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (fun w => (k w).val)

def rightDerivative (w : NumberField.InfinitePlace F) (j : Fin 6)
    (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  deriv (fun t : ℝ => f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
    (KPSmoothActualFlowData.flow F (w,j) t))) 0

def casimir (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∑ w : NumberField.InfinitePlace F, -((1 : ℂ) / 4) *
    (rightDerivative F ζ hζ w 0 (rightDerivative F ζ hζ w 0 f) g -
     rightDerivative F ζ hζ w 1 (rightDerivative F ζ hζ w 1 f) g +
     2 * (rightDerivative F ζ hζ w 2 (rightDerivative F ζ hζ w 4 f) g +
          rightDerivative F ζ hζ w 4 (rightDerivative F ζ hζ w 2 f) g -
          rightDerivative F ζ hζ w 3 (rightDerivative F ζ hζ w 5 f) g -
          rightDerivative F ζ hζ w 5 (rightDerivative F ζ hζ w 3 f) g))

def Smooth (f : Cover F ζ hζ → ℂ) : Prop :=
  Continuous f ∧ ∀ g, ContDiff ℝ (⊤ : ℕ∞)
    (fun a : KPSmoothActualFlowData.LieCoordinates F =>
      f (g * KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (KPSmoothActualFlowData.exponential F a)))

def KFinite (f : Cover F ζ hζ → ℂ) : Prop :=
  Module.Finite ℂ (Submodule.span ℂ
    (Set.range (fun k : K F => fun g => f (g * compactInsertion F ζ hζ k))))

section Atlas
variable {F ζ hζ} {hF : NumberField.InfinitePlace.nrRealPlaces F = 0}
variable {U : KPMsFixedHaarDisintegration.Level F ζ hζ}
variable (A : KPFiniteCuspAtlas.Atlas F ζ hζ hF U)

abbrev Cusps := KPMsFixedHaarDisintegration.CuspIndex A

structure AutomorphicAtLevel (f : Cover F ζ hζ → ℂ) : Prop where
  rational_left : ∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
    f (γ.val * g) = f g
  right_level : ∀ u : U.toOpenSubgroup, ∀ g, f (g * u.val.val) = f g
  ordinary_genuine : ∀ ε : rootsOfUnity 3 F, ∀ g,
    f (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f g

def cuspRepresentative (j : Cusps A) : Cover F ζ hζ :=
  KPRationalAdelicSplitting.rationalPGLHom F ζ hζ
    (KPRationalAdelicSplitting.rationalPGLQuotient F
      ((A.cuspAtlas j.1).representative j.2).out)

def constantTerm (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (j : Cusps A) (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  ∫ q, f (cuspRepresentative A j *
    KPGlobalTorusFunctionData.N F ζ hζ (KPCompactFourier.representative F q) *
    (cuspRepresentative A j)⁻¹ * g) ∂dn

def balancedArch (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    KPSmoothActualFlowData.GInfinity F := fun w =>
  let i := (Fintype.equivFin {v : NumberField.InfinitePlace F // v.IsComplex})
    ⟨w, KPHilbert.infinite_isComplex F ζ hζ w⟩
  Matrix.ProjGenLinGroup.mk
    (KPCplxCharacterHaar.upperUnipotent (p.1 i) *
      KPCplxCharacterHaar.diagonal (Units.mk0
        (Real.exp (KPMsFixedHaarDisintegration.logHeight (F := F) r + p.2.val i) : ℂ)
        (by exact_mod_cast Real.exp_ne_zero _))) * (k w).val

def cuspLift (j : Cusps A) (p : KPCuspCharts.Cross F) (k : K F) (r : ℝ) :
    Cover F ζ hζ :=
  cuspRepresentative A j *
    KPSmoothActualFlowData.archimedeanInsertion F ζ hζ (balancedArch (ζ := ζ) (hζ := hζ) p k r) *
    (A.representative j.1).val

def angularValue (f : Cover F ζ hζ → ℂ)
    (ω : KPMsFixedHaarDisintegration.Omega A) (k : K F) (r : ℝ) : ℂ :=
  f (cuspLift A ω.1 ((0 : KPCuspCharts.Horizontal F), ω.2.out) k r)

def endSet (j : Cusps A) (Y : ℝ) :
    Set (KPMsFixedHaarDisintegration.Spherical F ζ hζ U) :=
  KPFiniteCuspAtlas.componentMap F ζ hζ U (A.representative j.1) ''
    KPFiniteCuspAtlas.endSet F
      (KPCuspGenuineMonodromy.Component F ζ hζ U (A.representative j.1))
      ((A.cuspAtlas j.1).representative j.2)
      (KPMsFixedHaarDisintegration.logHeight (F := F) Y)

def truncate (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) (Y : ℝ)
    (f : Cover F ζ hζ → ℂ) (g : Cover F ζ hζ) : ℂ :=
  f g - ∑ j : Cusps A,
    if P.projection U (KPSmoothLocalQuotientCharts.quotientMap F ζ hζ g) ∈ endSet A j Y
    then constantTerm A dn j f g else 0

def quotientFunction (f : Cover F ζ hζ → ℂ) (x : X F ζ hζ) : ℂ := f x.out

def Eigenfunction (s : ℂ) (f : Cover F ζ hζ → ℂ) : Prop :=
  (∀ γ : KPSmoothLocalQuotientCharts.rationalSubgroup F ζ hζ, ∀ g,
    f (γ.val * g) = f g) ∧
  (∀ u : U.toOpenSubgroup, ∀ g, f (g * u.val.val) = f g) ∧
  (∀ ε : rootsOfUnity 3 F, ∀ g,
    f (KPSmoothLocalQuotientCharts.centreMap F ζ hζ ε * g) =
      (KPSmoothLocalQuotientCharts.ordinaryGenuine F ζ hζ ε : ℂ) * f g) ∧
  Smooth F ζ hζ f ∧ KFinite F ζ hζ f ∧
  ∀ g, casimir F ζ hζ f g =
    KPContinuation.spectralCoordinate (KPCuspLogShape.dimension F : ℤ) s * f g

theorem Eigenfunction.automorphicAtLevel {s : ℂ} {f : Cover F ζ hζ → ℂ}
    (hf : Eigenfunction (U := U) s f) : AutomorphicAtLevel (U := U) f :=
  ⟨hf.1, hf.2.1, hf.2.2.1⟩

def TwoWaves (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (s : ℂ) (f : Cover F ζ hζ → ℂ)
    (plus minus : KPMsFixedHaarDisintegration.Omega A → K F → ℂ) : Prop :=
  ∀ ω k r, KPMsFixedHaarDisintegration.AdmissibleCutoff A r →
    constantTerm A dn ω.1 f (cuspLift A ω.1 (0, ω.2.out) k r) =
      Complex.exp (((2 : ℂ) / 3 + s) * (Real.log r : ℂ)) * plus ω k +
      Complex.exp (((1 : ℂ) / 3 - s) * (Real.log r : ℂ)) * minus ω k

def RapidTails (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (Y₀ : ℝ) (f : Cover F ζ hζ → ℂ) : Prop :=
  ∀ (word : List (KPSmoothActualFlowData.B F)) (N : ℕ)
      (B : Set (KPCuspCharts.Cross F)), IsCompact B →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j p, p ∈ B → ∀ k r, Y₀ ≤ r → 0 < r →
      let df := word.foldr (fun b v => rightDerivative F ζ hζ b.1 b.2 v) f
      let nc := fun ρ => df (cuspLift A j p k ρ) -
        constantTerm A dn j df (cuspLift A j p k ρ)
      ‖nc r‖ + ‖deriv nc r‖ ≤ C * r ^ (-(N : ℤ))

def wronskian (u v : ℝ → ℂ) (r : ℝ) : ℂ :=
  star (deriv u r) * v r - star (u r) * deriv v r

def constantFlux (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (β : Measure (KPMsFixedHaarDisintegration.Omega A))
    (dk : Measure (K F)) (u v : Cover F ζ hζ → ℂ) (Y : ℝ) : ℂ :=
  ∫ ω, ∫ k, wronskian
    (fun r => constantTerm A dn ω.1 u (cuspLift A ω.1 (0,ω.2.out) k r))
    (fun r => constantTerm A dn ω.1 v (cuspLift A ω.1 (0,ω.2.out) k r)) Y ∂dk ∂β

def nonconstantFlux
    (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (D : KPMsFixedHaarDisintegration.Disintegration A R P)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F)) (dk : Measure (K F))
    (u v : Cover F ζ hζ → ℂ) (Y : ℝ) : ℂ :=
  ∫ ω, ∫ x, ∫ k, wronskian
    (fun r => u (cuspLift A x.1 x.2.out k r) -
      constantTerm A dn x.1 u (cuspLift A x.1 x.2.out k r))
    (fun r => v (cuspLift A x.1 x.2.out k r) -
      constantTerm A dn x.1 v (cuspLift A x.1 x.2.out k r)) Y
    ∂dk ∂D.unipotent ω ∂KPMsFixedHaarDisintegration.probability A D.beta

def quotientCore (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (T : ℝ) : Set (X F ζ hζ) :=
  {x | ∀ j : Cusps A, P.projection U x ∉ endSet A j T}

def slabPairing (R : KPSmoothLocalQuotientCharts.HaarRecipe F ζ hζ)
    (P : KPMsFixedHaarDisintegration.SphericalTransport F ζ hζ)
    (dn : Measure (KPCompactFourier.AdditiveQuotient F))
    (u v : Cover F ζ hζ → ℂ) (Y T : ℝ) : ℂ :=
  ∫ x in quotientCore A P T,
    star (quotientFunction (truncate A P dn Y u) x) *
      quotientFunction (truncate A P dn Y v) x ∂(R.quotientHaar)

end Atlas
end DedekindZetaZeroFree.KPMsGreenFlux

end
