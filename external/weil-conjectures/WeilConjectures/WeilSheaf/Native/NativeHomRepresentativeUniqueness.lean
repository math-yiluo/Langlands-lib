/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels

/-! # Uniqueness of Hom comparisons with fixed product-total representatives

Source: Stacks 0A95 and 079P; native constraint lifting, Hom identification step.
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
  AlgebraicGeometry.ProEtaleWeilSheaf
private theorem representative_unique
    {A B : Type u} [Category.{v} A] [Category.{v} B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{v} B]
    [Abelian.HasKInjectiveResolutions A]
    (H₀A : Aᵒᵖ ⥤ A ⥤ A) (H₀B : Bᵒᵖ ⥤ B ⥤ B)
    [H₀A.Additive] [∀ P, (H₀A.obj P).Additive]
    [H₀B.Additive] [∀ P, (H₀B.obj P).Additive]
    (HA : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (HB : (DerivedCategory B)ᵒᵖ × DerivedCategory B ⥤ DerivedCategory B)
    (MA : NativeHomRepresentatives H₀A HA) (MB : NativeHomRepresentatives H₀B HB)
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (η χ : HA ⋙ U.mapDerivedCategory ≅
      U.mapDerivedCategory.op.prod U.mapDerivedCategory ⋙ HB)
    (hη : NativeHomRepresentativeCompatibility H₀A H₀B HA HB MA MB U η)
    (hχ : NativeHomRepresentativeCompatibility H₀A H₀B HA HB MA MB U χ) :
    η = χ := by
  have hrep (P I : CochainComplex (A) ℤ)
      (hP : P.IsKInjective) (hI : I.IsKInjective) :
      η.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) =
        χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) := by
    obtain ⟨hUP, hUI, a, ha, hs⟩ := hη P I hP hI
    obtain ⟨hUP', hUI', b, hb, ht⟩ := hχ P I hP hI
    have hab : a.hom = b.hom := by
      ext n : 1
      apply CochainComplex.bifunctorHomObj_hom_ext
      intro p q hpq
      exact eq_of_heq ((ha n p q hpq).trans (hb n p q hpq).symm)
    rw [hab] at hs
    let j := HB.mapIso ((U.mapDerivedCategoryFactors.app P).symm.op.prod
      (U.mapDerivedCategoryFactors.app I)) ≪≫ MB.model _ _ hUI
    apply (cancel_mono j.hom).1
    exact hs.trans ht.symm
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  let P := DerivedCategory.kInjectiveRep Z.1.unop
  let I := DerivedCategory.kInjectiveRep Z.2
  let eP := DerivedCategory.kInjectiveRepIso Z.1.unop
  let eI := DerivedCategory.kInjectiveRepIso Z.2
  let e : Z ≅ (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) :=
    eP.symm.op.prod eI
  apply (cancel_mono
    (((U.mapDerivedCategory).op.prod (U.mapDerivedCategory) ⋙ HB).map e.hom)).1
  rw [← η.hom.naturality e.hom, ← χ.hom.naturality e.hom]
  rw [hrep P I inferInstance inferInstance]

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Projection-normalized native Hom comparisons are unique. This statement
concerns only internal Hom; it constructs no tensor or structural constraint.

Source: native constraint lifting step 3, identification of Hom representatives;
Stacks 0A95 and 079P (blueprint: lem-sf-native-hom-representative-uniqueness).

Proof: first take two K-injective complexes P and I. The two compatibility
witnesses have the same projections to every product-Hom component, by their
HEq clauses. The universal property of the product, degree by degree, makes
the two complex comparison arrows equal, independently of the proof witnesses
of K-injectivity. Cancel the common invertible localization factorization and
representative maps in the two compatibility squares. Thus eta and chi agree
on (QP,QI). Every native derived object is isomorphic to Q of a K-injective
complex. Naturality in both variables transports that equality to arbitrary
derived pairs; cancel the images of these isomorphisms. Natural transformations
and natural isomorphisms are determined by their components, proving eta=chi.
Neither a tensor model nor boundedness or nonzero objects is used. -/
theorem native_hom_representative_unique
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X)
    (η : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hη : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η)
    (χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom)
    (hχ : NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
      (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
      (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ) :
    η = χ := by
  exact representative_unique (ihomBifunctor k₀ l X)
    (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
    (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) η χ hη hχ

end AlgebraicGeometry.ProEtaleWeilSheaf
