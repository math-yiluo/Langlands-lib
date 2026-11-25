/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficientsData
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.SixFunctors.Regular.RegularQuotientTraceIsIso
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionBounds
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionComplete

/-! # Regular quotient extension is a right adjoint on finite-Tor categories

Source: Zheng Lemma 5.22 and Proposition 5.26, integral reduction part of sk-thm-sf-compatibility.
Stacks Tags 0A70 and 0A71 (perfect coefficient duality and coinduction), 06YY and 07A6 (derived
change of coefficients and its normalized adjunction). The precise ring-level regular-quotient
duality formula is Stacks Lemma 47.13.10 (0BZH), using perfect-algebra evaluation in Lemma 47.13.9
(0BZE). Its realization on the specified sheaf categories is part of this argument, not supplied
by the ring statement alone.
(blueprint: lem-sf-regular-quotient-scalar-right-adjoint). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ExceptionalIntegralScalar
open ConstructibleExceptionalCoefficients

attribute [-instance] PrincipalKoszulStrictReplacement.siteSmall
  PrincipalKoszulStrictReplacement.abSheafify PrincipalKoszulStrictReplacement.abLocallyBijective
  integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  scalarReductionSourceDerived scalarReductionTargetDerived
  GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local instance] HasDerivedCategory.standard
attribute [local irreducible] HasDerivedCategory.standard

private local instance (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T
private local instance (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

private noncomputable def reverseShiftAdjunction
    {A B : Type*} [Category* A] [Category* B] [HasShift A ℤ]
    {U : B ⥤ A} {G F : A ⥤ B} (a : U ⊣ G)
    (e : G ≅ shiftFunctor A (-1 : ℤ) ⋙ F) :
    U ⋙ shiftFunctor A (-1 : ℤ) ⊣ F := by
  let s : shiftFunctor A (-1 : ℤ) ⊣ shiftFunctor A (1 : ℤ) :=
    (shiftEquiv' A (-1 : ℤ) 1 (by omega)).toAdjunction
  let aa : U ⋙ shiftFunctor A (-1 : ℤ) ⊣ shiftFunctor A (1 : ℤ) ⋙ G := a.comp s
  let ee : shiftFunctor A (1 : ℤ) ⋙ G ≅ F :=
    Functor.isoWhiskerLeft (shiftFunctor A (1 : ℤ)) e ≪≫
      (Functor.associator _ _ F).symm ≪≫
      Functor.isoWhiskerRight (shiftFunctorCompIsoId A 1 (-1 : ℤ) (by omega)) F ≪≫
      F.leftUnitor
  exact aa.ofNatIsoRight ee

private theorem restrictReverseAdjunction
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u, u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T)
    (U : DerivedCategory (pbcModules.{u} T
        (((RingStage.finite.{u} E ⟨n + 1, Nat.succ_pos n⟩).coefficients l).ring T)) ⥤
      DerivedCategory (pbcModules.{u} T (((RingStage.integral.{u} E).coefficients l).ring T)))
    (a : U ⊣ pbcDerivedExtend.{u}
      ((PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)).map T))
    (hU : ∀ K : C.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩),
      finiteTorConstructibleIntegral l E.carrier T (U.obj K.obj)) :
    S.functor.IsRightAdjoint := by
  let L := (finiteTorConstructibleIntegral l E.carrier T).lift
    (RingStage.inclusion.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩) ⋙ U) hU
  exact (a.restrictFullyFaithful
    (finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T).fullyFaithfulι
    (finiteTorConstructibleIntegral l E.carrier T).fullyFaithfulι
    (L := L) (R := S.functor) (Iso.refl _) S.realization.symm).isRightAdjoint

private theorem regularQuotientScalarRightAdjoint_of_trace
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u, u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T)
    (ht : IsIso (reductionCoinductionTrace.{u} l E.carrier T n))
    (hb : ∀ (K : DerivedCategory (scalarReductionTarget.{u, u} l E.carrier T n)),
      finiteTorConstructible l E.carrier (n + 1) (Nat.succ_pos n) T K →
      ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
        intrinsicFiniteTorsionConstructible l E.carrier (m + 1) (Nat.succ_pos m) T
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) ∧
          proEtaleCohomologicalSupport
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) ⊆ Set.Icc a b ∧
          HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E.carrier (m + 1))
            ((scalarReductionDerivedExtension.{u, u} l E.carrier T m).obj
              ((scalarReductionDerivedRestriction.{u, u} l E.carrier T n).obj K)) a b) :
    S.functor.IsRightAdjoint := by
  let := ht
  let U := scalarReductionDerivedRestriction.{u, u} l E.carrier T n
  let V := U ⋙ shiftFunctor _ (-1 : ℤ)
  let a := (reverseShiftAdjunction
    (scalarReductionDerivedCoinductionAdjunction l E.carrier T n)
    (asIso (reductionCoinductionTrace l E.carrier T n)).symm).ofNatIsoRight
      (reductionCochainModelIso l E.carrier T n ≪≫
        (PurCompactSupport.finiteReductionIso l E.carrier T n).symm)
  have hU (K : C.{u, u} l Ω T (.finite E ⟨n + 1, Nat.succ_pos n⟩)) :
      finiteTorConstructibleIntegral l E.carrier T (U.obj K.obj) := by
    obtain ⟨c, d, hcd, h⟩ := hb K.obj K.property
    exact ⟨⟨scalarReductionDerivedRestriction_complete l E.carrier T n K.obj,
      c, d, hcd, fun m ↦ ⟨(h m).1, (h m).2.1⟩⟩,
      c, d, hcd, fun m ↦ (h m).2.2⟩
  have : (finiteTorConstructibleIntegral l E.carrier T).IsTriangulated :=
    integralTriangulated l E T
  exact restrictReverseAdjunction l Ω E n T S V a (fun K ↦
    (finiteTorConstructibleIntegral l E.carrier T).le_shift (-1 : ℤ) _ (hU K))

/-- Regular quotient extension, restricted to the prescribed finite-Tor categories,
has a left adjoint. This assertion contains no geometric operation or compactification.
Source: Zheng, Lemma 5.22 and Proposition 5.26; Stacks Tags 0A70, 0A71 and 07A6.
Proof: write A for the completed coefficient sheaf and B for its quotient by
pi^(n+1). The normalized principal quotient sequence is a locally free resolution
of B of length one. Its algebra-valued dual is canonically B[-1]. Construct ordinary
sheaf coinduction as the internal module-object equalizer and transport it to the
actual ring-sheaf module category using the section-module equivalence. Derive the
restriction/coinduction adjunction using exactness of restriction and K-injective
resolutions. Perfect evaluation for the two-term resolution, with its quotient
action retained, identifies derived coinduction with derived extension followed
by [-1]. The augmentation and trace fix this comparison. Compose with the inverse
shift adjunction: restriction followed by [-1] is left adjoint to extension.
Restriction of a bounded finite-Tor constructible B-complex is annihilated by a
fixed power of pi. On every slice the finite geometric series in the nilpotent
scalar shift inverts one minus that shift; hence its localization internal Hom
vanishes. Normalized coefficient completeness transport identifies this condition
with the prescribed augmented reduction Roos triangle, so it is derived complete.
Tensor its local finite-free
models with the length-one quotient resolution: their finite reductions remain
constructible, with one common cohomological and Tor interval enlarged by at most
one. Hence shifted restriction lands in the integral finite-Tor category. Restrict
the ambient adjunction along the two fully faithful inclusions. Finally transport
its right functor through S.realization; this proves the assertion for the specified
S, independently of its presentation. The exponent n+1 is positive even for n=0;
the same resolution and equations apply to zero objects and empty schemes.
(blueprint: lem-sf-regular-quotient-scalar-right-adjoint). -/
theorem regularQuotientScalarRightAdjoint
    (l : ℕ) [Fact l.Prime]
    (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    (E : FieldStage.{u} l) (n : ℕ) (T : Scheme.{u})
    (S : Scalar.{u} l Ω (s := .integral E)
      (t := .finite E ⟨n + 1, Nat.succ_pos n⟩)
      (PurCompactSupport.reduction l E.carrier (n + 1) (Nat.succ_pos n)) T) :
    S.functor.IsRightAdjoint := by
  exact regularQuotientScalarRightAdjoint_of_trace l Ω E n T S
    (reductionCoinductionTrace_isIso l E.carrier T n)
    (scalarReductionDerivedRestriction_bounds l E.carrier T n)

end WeilConjectures.ExceptionalIntegralScalar
