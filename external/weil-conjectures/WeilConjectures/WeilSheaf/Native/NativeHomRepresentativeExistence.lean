/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import all WeilConjectures.WeilSheaf.Native.Weil.NativeWeilRowHomComparison
import WeilConjectures.CategoryTheory.K.KInjectiveHomComparisonDescent

/-! # Existence of the Hom comparison for prescribed native representatives

Source: Stacks 0A95 and 08J7; native ringed tensor model, Hom comparison step.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open CategoryTheory.RingedForgetTwoInjective
open AlgebraicGeometry.ProEtaleWeilSheaf

private def standardRepresentative
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory.{v} A]
    (H : Aᵒᵖ ⥤ A ⥤ A) [H.Additive] [∀ P, (H.obj P).Additive]
    (S : StandardModel H) (D : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H D) (P I : CochainComplex A ℤ) [I.IsKInjective] :
    D.obj (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≅
      DerivedCategory.Q.obj (S.complex.obj (op P, I)) :=
  R.model P I inferInstance ≪≫ DerivedCategory.Q.mapIso (rowIso H S P I).symm

private theorem standardRepresentative_naturality
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory.{v} A]
    (H : Aᵒᵖ ⥤ A ⥤ A) [H.Additive] [∀ P, (H.obj P).Additive]
    (S : StandardModel H) (D : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H D)
    (P P' I I' : CochainComplex A ℤ) [I.IsKInjective] [I'.IsKInjective]
    (f : P' ⟶ P) (g : I ⟶ I') :
    D.map ((DerivedCategory.Q.map f).op, DerivedCategory.Q.map g) ≫
        (standardRepresentative H S D R P' I').hom =
      (standardRepresentative H S D R P I).hom ≫
        DerivedCategory.Q.map (S.complex.map (f.op, g)) := by
  have hn :
      (CochainComplex.bifunctorHomMapLeft (H := H) (Y := I) f ≫
        CochainComplex.bifunctorHomMapRight (H := H) (K := P') g) ≫
          (rowIso H S P' I').inv =
      (rowIso H S P I).inv ≫ S.complex.map (f.op, g) := by
    apply (cancel_epi (rowIso H S P I).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using
      congrArg (fun z ↦ z ≫ (rowIso H S P' I').inv)
        (rowIso_naturality H S P I P' I' f g).symm
  dsimp only [standardRepresentative, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [← Category.assoc, R.naturality P' P I I' inferInstance inferInstance f g,
    Category.assoc, ← DerivedCategory.Q.map_comp, hn, DerivedCategory.Q.map_comp,
    Category.assoc]

private theorem standardRepresentative_cancel
    {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
    [HasDerivedCategory.{v} A]
    (H : Aᵒᵖ ⥤ A ⥤ A) [H.Additive] [∀ P, (H.obj P).Additive]
    (S : StandardModel H) (D : (DerivedCategory A)ᵒᵖ × DerivedCategory A ⥤ DerivedCategory A)
    (R : NativeHomRepresentatives H D) (P I : CochainComplex A ℤ) [I.IsKInjective] :
    (standardRepresentative H S D R P I).hom ≫
        DerivedCategory.Q.map (rowIso H S P I).hom = (R.model P I inferInstance).hom := by
  dsimp only [standardRepresentative, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  rw [Category.assoc, ← DerivedCategory.Q.map_comp, Iso.inv_hom_id,
    DerivedCategory.Q.map_id, Category.comp_id]

attribute [local irreducible] standardRepresentative

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]

/-- Prescribed natural native and ordinary product-total models admit a
projection-normalized forgetful Hom comparison.

Source: Stacks 0A95 and 08J7; native ringed tensor model, step 2 and Hom part of step 3.
(blueprint: lem-sf-native-hom-representative-existence).

Proof: take the existing standard-sign two-injective chain model. For each
of the two prescribed representative systems, compose its model map with the
inverse row-sign isomorphism. Naturality follows by conjugating the given
representative naturality by the row-sign naturality square. Apply
kInjectiveHomComparisonDescent to these standard representatives and the
existing chain comparison. Conjugate the resulting representative square back
to row signs. The chain comparison is conjugated by exactly the same two sign
maps. On its (n,p,q) projection the two factors (-1)^(np) cancel, so that the
projection is precisely forgetting the original native projection. Forgetting
preserves K-injectives, supplying both required witnesses. The localization
square retains both exact-functor factorization maps. This construction uses
no tensor structure, and also applies to zero complexes and the empty site. -/
theorem native_hom_representative_exists
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (M : NativeClosedHomModels k₀ l X) :
    ∃ χ : M.weilHom ⋙ nativeForget k₀ l X ≅
      (nativeForget k₀ l X).op.prod (nativeForget k₀ l X) ⋙ M.ordinaryHom,
      NativeHomRepresentativeCompatibility (ihomBifunctor k₀ l X)
        (ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
        M.weilHom M.ordinaryHom M.weilRepresentatives M.ordinaryRepresentatives
        (Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)) χ := by
  obtain ⟨m⟩ := native_two_injective_hom_model (k₀ := k₀) (l := l) (X := X)
  let U := Endofunctor.IsoAlgebra.forget (WeilSheaf.frobeniusPullback k₀ l X)
  let UC := U.mapHomologicalComplex (.up ℤ)
  let H := ihomBifunctor k₀ l X
  let H' := ordinaryIhomBifunctor l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
  have : U.PreservesKInjectiveComplexes := forgetKInjective
  obtain ⟨χ, hχ⟩ := kInjectiveHomComparisonDescent U m.source.complex m.target.complex
    M.weilHom M.ordinaryHom
    (standardRepresentative H m.source M.weilHom M.weilRepresentatives)
    (standardRepresentative H' m.target M.ordinaryHom M.ordinaryRepresentatives)
    (standardRepresentative_naturality H m.source M.weilHom M.weilRepresentatives)
    (standardRepresentative_naturality H' m.target M.ordinaryHom M.ordinaryRepresentatives)
    m.chain
  refine ⟨χ, ?_⟩
  intro P I hP hI
  let _ := hP
  let _ := hI
  let s := rowIso H m.source P I
  let t := rowIso H' m.target (UC.obj P) (UC.obj I)
  let e := (UC.mapIso s).symm ≪≫ m.chain.app (op P, I) ≪≫ t
  refine ⟨inferInstance, inferInstance, e, ?_, ?_⟩
  · intro n p q hpq
    apply heq_of_eq
    change ((UC.map s.inv ≫ (m.chain.app (op P, I)).hom) ≫ t.hom).f n ≫ _ = _
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Category.assoc,
      Category.assoc, rowIso_hom_projection, Linear.comp_units_smul,
      Linear.comp_units_smul]
    change (n * p).negOnePow • ((UC.map s.inv).f n ≫
      (m.chain.hom.app (op P, I)).f n ≫ m.target.π (UC.obj P) (UC.obj I) n p q hpq) = _
    rw [m.chain_projection P I n p q hpq]
    change (n * p).negOnePow •
      (U.map (s.inv.f n) ≫ (U.map (m.source.π P I n p q hpq) ≫ _)) = _
    rw [← Category.assoc, ← U.map_comp]
    change (n * p).negOnePow •
      (U.map (rowDegreeInverse H m.source P I n ≫ m.source.π P I n p q hpq) ≫ _) = _
    rw [rowDegreeInverse_projection]
    simp only [Units.smul_def, U.map_zsmul, Preadditive.zsmul_comp, smul_smul,
      ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
    rfl
  · have hs := conjugateLocalizationSquare DerivedCategory.Q DerivedCategory.Q UC
      U.mapDerivedCategory U.mapDerivedCategoryFactors
      (standardRepresentative H m.source M.weilHom M.weilRepresentatives P I).hom
      (standardRepresentative H' m.target M.ordinaryHom M.ordinaryRepresentatives
        (UC.obj P) (UC.obj I)).hom
      (χ.hom.app (op (DerivedCategory.Q.obj P), DerivedCategory.Q.obj I) ≫
        M.ordinaryHom.map ((U.mapDerivedCategoryFactors.inv.app P).op,
          U.mapDerivedCategoryFactors.hom.app I))
      (m.chain.app (op P, I)).hom s t (by
        simpa only [UC, Iso.app_hom, Category.assoc] using hχ P I)
    simp only [s, t, standardRepresentative_cancel] at hs
    simpa only [e, s, t, U, UC, H, H', Iso.trans_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.symm_hom, Iso.app_hom, Prod.mkHom, Category.assoc] using hs

end AlgebraicGeometry.ProEtaleWeilSheaf
