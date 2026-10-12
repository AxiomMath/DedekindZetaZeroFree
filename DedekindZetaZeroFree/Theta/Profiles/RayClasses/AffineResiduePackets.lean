module

public import DedekindZetaZeroFree.Arithmetic.Characters.RationalTracePhase
public import DedekindZetaZeroFree.LFunctions.Hecke.RayResidueIdealCoefficients

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

def affineResidueScale (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : ℝ :=
  (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 F)⁰ F) : ℝ) ^
    (-(Module.finrank ℚ F : ℝ)⁻¹)

def affineResidueTheta (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (h : RayCoset.logHyperplane F) : ℂ :=
  ∑' l : {l : F // l ∈
      ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)},
    RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u h)
      (affineResidueScale I • Theta.traceEmbedding F (x.val + l.val)))

def affineResidueDualTheta (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (h : RayCoset.logHyperplane F) : ℂ :=
  ∑' β : {β : F // β ∈
      (Theta.traceDualIdealUnit F (I * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F)},
    rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)) *
      RayParity.gδ F ∅ (RayParity.Q F (RayTheta.q F u (-h))
        ((affineResidueScale I)⁻¹ •
          Theta.traceConjugation F (Theta.traceEmbedding F β.val)))

def affineResidueAverage (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) (u : ℝ) : ℂ :=
  ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    affineResidueTheta m hm I x u h ∂Theta.normalizedLogHaar F

def affineResidueDualAverage (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) (u : ℝ) : ℂ :=
  ∫ h in RayCoset.rayUnitHalfOpenDomain F m hm,
    affineResidueDualTheta m hm I x u h ∂Theta.normalizedLogHaar F

 theorem residue_trace_phase_congr
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ)
    (x y : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (hxy : x.val - y.val ∈ (J : FractionalIdeal (𝓞 F)⁰ F))
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F J :
      FractionalIdeal (𝓞 F)⁰ F)}) :
    rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)) =
      rationalTracePhase (Algebra.trace ℚ F (y.val * β.val)) := by
  have ht := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ)
    (Units.ne_zero J)).mp β.property (x.val - y.val) hxy
  obtain ⟨n, hn⟩ := ht
  have hp : rationalTracePhase
      (Algebra.trace ℚ F (x.val * β.val) -
        Algebra.trace ℚ F (y.val * β.val)) = 1 := by
    apply (rationalTracePhase_eq_one_iff _).mpr
    refine ⟨n, ?_⟩
    simpa [Algebra.traceForm_apply, mul_comm, sub_mul, map_sub] using hn
  rw [AddChar.map_sub_eq_div] at hp
  exact (div_eq_one_iff_eq (rationalTracePhase_ne_zero _)).mp hp

def coprimeIdealResiduePhase (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥) :
    coprimeIdealResidue F m a hm ha →
      {β : F // β ∈ (Theta.traceDualIdealUnit F
        (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F)} → ℂ := by
  refine Quotient.lift
    (fun x β => rationalTracePhase (Algebra.trace ℚ F (x.val * β.val))) ?_
  intro x y hxy
  funext β
  apply residue_trace_phase_congr (rayIdealFractionalIdeal F a ha)
    (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) x y ?_ β
  change x.val - y.val ∈
    ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)
  exact (Submodule.Quotient.eq
    ((((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule).comap
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule.subtype)).mp
    (Quotient.sound hxy)

theorem coprimeIdealResiduePhase_mk
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (x : {x : F // x ∈
      (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)})
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F)}) :
    coprimeIdealResiduePhase m a hm ha
      (fractionalIdealQuotientMk
        (rayIdealFractionalIdeal F a ha : FractionalIdeal (𝓞 F)⁰ F)
        ((rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
          FractionalIdeal (𝓞 F)⁰ F) x) β =
      rationalTracePhase (Algebra.trace ℚ F (x.val * β.val)) := by
  rfl

def coprimeIdealResiduePacket (hF : NumberField.IsTotallyComplex F)
    (m a : Ideal (𝓞 F)) (hm : m ≠ ⊥) (ha : a ≠ ⊥)
    (hcop : a ⊔ m = ⊤) (hmt : m ≠ ⊤)
    (η : DedekindZetaZeroFree.RayClassCharacter F m)
    (E : RayCharacterData F m hm η)
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (rayIdealFractionalIdeal F a ha * rayIdealFractionalIdeal F m hm) :
        FractionalIdeal (𝓞 F)⁰ F)}) : ℂ := by
  letI := coprimeIdealResidue_finite m a hm ha hcop
  letI := Fintype.ofFinite (coprimeIdealResidue F m a hm ha)
  exact ∑ q : coprimeIdealResidue F m a hm ha,
    coprimeIdealResidueCoefficient hF m a hm ha hcop hmt η E q *
      coprimeIdealResiduePhase m a hm ha q β

end DedekindZetaZeroFree.Hecke.Theta

end
