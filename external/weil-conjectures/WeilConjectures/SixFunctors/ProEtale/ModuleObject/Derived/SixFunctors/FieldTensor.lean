/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDescentTwoColimit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleTensorPreservation
import all WeilConjectures.AlgebraicGeometry.Integral.Constant.IntegralConstantModelHeartClosureSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Tensor closure of rational localizing categories

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.md` (blueprint:
proposition-projection-formula-rational-coefficients--1).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
open AlgebraicGeometry Scheme

private theorem localizing_inverseImage
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (P : ObjectProperty C) (hP : IsLocalizingSubcategory P) (F : C ⥤ C)
    [F.CommShift ℤ] [F.IsTriangulated] [F.IsLeftAdjoint] :
    IsLocalizingSubcategory (P.inverseImage F) := by
  let := hP.1
  let := hP.2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro I G hG h
  let := hG
  have hcol : P (colimit (G ⋙ F)) := hP.prop_colimit (G ⋙ F) inferInstance h
  exact P.prop_of_iso (preservesColimitIso F G).symm hcol

private theorem localizing_tensor_closed
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T T' : C ⥤ C ⥤ C) (heq : T = T')
    [∀ A : C, (T'.obj A).CommShift ℤ]
    [∀ A : C, (T'.flip.obj A).CommShift ℤ]
    [∀ A : C, (T'.obj A).IsTriangulated]
    [∀ A : C, (T'.flip.obj A).IsTriangulated]
    [∀ A : C, (T'.obj A).IsLeftAdjoint]
    [∀ A : C, (T'.flip.obj A).IsLeftAdjoint]
    (S : ObjectProperty C) (hL : IsLocalizingSubcategory (localizingClosure S))
    (h : ∀ A B, S A → S B → S ((T.obj A).obj B)) :
    ∀ A B, localizingClosure S A → localizingClosure S B →
      localizingClosure S ((T.obj A).obj B) := by
  subst T'
  let L := localizingClosure S
  have hSL : S ≤ L := fun K hK P _ hSP ↦ hSP K hK
  have hright (B) (hB : S B) : ∀ A, L A → L ((T.obj A).obj B) := by
    intro A hA
    exact hA (L.inverseImage (T.flip.obj B))
      (localizing_inverseImage L hL (T.flip.obj B))
      (fun K hK ↦ hSL _ (h K B hK hB))
  intro A B hA hB
  exact hB (L.inverseImage (T.obj A))
    (localizing_inverseImage L hL (T.obj A))
    (fun M hM ↦ hright M hM A hA)

attribute [local irreducible] Functor.mapDerivedCategory
  DerivedCategory.tensorLeftCompMapDerivedCategoryIso
  Functor.mapDerivedCategoryHomologyFunctorIso
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed

private theorem derived_tensor_transport
    {C₁ C₂ : Type*}
    [Category C₁] [Abelian C₁] [IsGrothendieckAbelian.{u} C₁]
    [HasDerivedCategory.{u} C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
    [MonoidalPreadditive C₁] [BraidedCategory C₁] [Abelian.HasFunctorialFlatResolution C₁]
    [Category C₂] [Abelian C₂] [IsGrothendieckAbelian.{u} C₂]
    [HasDerivedCategory.{u} C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
    [MonoidalPreadditive C₂] [BraidedCategory C₂] [Abelian.HasFunctorialFlatResolution C₂]
    (T₁ : DerivedCategory C₁ ⥤ DerivedCategory C₁ ⥤ DerivedCategory C₁)
    (T₂ : DerivedCategory C₂ ⥤ DerivedCategory C₂ ⥤ DerivedCategory C₂)
    (heq₁ : T₁ = curriedTensor _) (heq₂ : T₂ = curriedTensor _)
    (F : C₁ ⥤ C₂) [F.Monoidal] [F.IsEquivalence] [F.Additive]
    (P : ObjectProperty (DerivedCategory C₂))
    (Q : ObjectProperty (DerivedCategory C₁)) [P.IsClosedUnderIsomorphisms]
    (hF : ∀ K, P (F.mapDerivedCategory.obj K) ↔ Q K)
    (h : ∀ K M, P K → P M → P ((T₂.obj K).obj M)) :
    ∀ K M, Q K → Q M → Q ((T₁.obj K).obj M) := by
  subst T₁ T₂
  intro K M hK hM
  exact (hF _).mp (P.prop_of_iso
    ((DerivedCategory.tensorLeftCompMapDerivedCategoryIso F K).app M).symm
    (h _ _ ((hF _).mpr hK) ((hF _).mpr hM)))

namespace AlgebraicGeometry.ProEtale.CondensedRing

open MonoidalCategory MonObj

private theorem derivedTensor_eq_curriedTensor
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    derivedTensor Λ X = @curriedTensor _ _
      (DerivedCategory.instMonoidalCategory (C := Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) := rfl

private theorem constantModel_derived_comap_iff
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X))) :
    constantModelBoundedConstructible Λ X
        ((Mod.comap (coefficientMap φ X)).mapDerivedCategory.obj K) ↔
      constantModelBoundedConstructible Λ' X K := by
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comap (coefficientMap φ X)
  constructor
  · intro h
    refine ⟨F.bounded_of_bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    apply (constantModel_comap_iff φ X _).mp
    exact constructible_iso
      ((F.mapDerivedCategoryHomologyFunctorIso n).app K).symm (h.2 n)
  · intro h
    refine ⟨F.bounded_mapDerivedCategory_obj h.1, fun n ↦ ?_⟩
    exact constructible_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app K)
      ((constantModel_comap_iff φ X _).mpr (h.2 n))

private theorem constantModel_tensor_transport
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (φ : Λ ⟶ Λ') [IsMonHom φ] [IsIso φ] (X : Scheme.{u})
    (h : ∀ K M, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X M →
      constantModelBoundedConstructible Λ X (((derivedTensor Λ X).obj K).obj M)) :
    ∀ K M, constantModelBoundedConstructible Λ' X K →
      constantModelBoundedConstructible Λ' X M →
      constantModelBoundedConstructible Λ' X (((derivedTensor Λ' X).obj K).obj M) := by
  let F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X) ⥤
      Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) :=
    Mod.comap (coefficientMap φ X)
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso (coefficientMap φ X)).functor.IsEquivalence
  have : (constantModelBoundedConstructible Λ X).IsClosedUnderIsomorphisms :=
    ⟨fun e hK ↦ ⟨DerivedCategory.TStructure.t.bounded.prop_of_iso e hK.1,
      fun n ↦ constructible_iso ((DerivedCategory.homologyFunctor _ n).mapIso e)
        (hK.2 n)⟩⟩
  exact derived_tensor_transport (derivedTensor Λ' X) (derivedTensor Λ X)
    (derivedTensor_eq_curriedTensor Λ' X) (derivedTensor_eq_curriedTensor Λ X)
    F _ _ (constantModel_derived_comap_iff φ X) h

/-- The bounded constructible rational coefficient category is closed under derived tensor,
and its localizing closure is closed under derived tensor.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
`sk-thm-sf-pf-field/sk-thm-sf-pf-field-tensor.md` (blueprint:
proposition-projection-formula-rational-coefficients--1).

The coefficient hypothesis `hΛ` identifies `Λ` with the condensed ring of `E` or of the
finite-subextension-valued `Q̄_ℓ` as commutative monoid objects (an isomorphism in `Mon`), so
the ring structure of `Λ`, not only its underlying abelian sheaf, is the node's.

Proof:
1. Clause (4) of `finiteCoefficientDescentTwoColimit` identifies the constant-model bounded
   constructible predicate with the existing bounded-constructible predicate for each finite
   coefficient field and for `Q̄_ℓ`. Apply `boundedConstructible_tensor_closure` there.
2. Restriction along the coefficient-ring isomorphism is an exact equivalence. It commutes
   with cohomology and preserves finite constant local models, so it preserves and reflects
   constant-model bounded constructibility. Its derived monoidal comparison transports
   step 1 to `Λ`.
3. The inverse image of a localizing object property under an exact left adjoint is
   localizing: exactness supplies triangulated closure, and the left adjoint preserves
   coproducts. Apply this to tensoring in either variable.
4. For `B ∈ Dbc`, the objects `A` with `A ⊗ᴸ B ∈ Loc(Dbc)` form a localizing subcategory
   containing `Dbc` by step 2. Minimality gives the assertion for `A ∈ Loc(Dbc)`.
   Fixing such an `A`, repeat in the second variable to obtain clause (2).
-/
theorem constantModelBoundedConstructible_derivedTensor
    (ℓ : ℕ) [Fact ℓ.Prime]
    {k : Type u} [Field k] (p : ℕ) [CharP k p] (hpl : p ≠ ℓ)
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))) :
    (∀ (K M : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
      constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X M →
      constantModelBoundedConstructible Λ X
        (((derivedTensor Λ X).obj K).obj M)) ∧
    (∀ (A B : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          (condensedRingObj Λ X))),
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X) A →
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X) B →
      CategoryTheory.localizingClosure
          (constantModelBoundedConstructible Λ X)
            (((derivedTensor Λ X).obj A).obj B)) := by
  let : X.Over (Spec (.of k)) := ⟨aX⟩
  let : LocallyOfFiniteType (X ↘ Spec (.of k)) :=
    inferInstanceAs (LocallyOfFiniteType aX)
  let : QuasiCompact (X ↘ Spec (.of k)) := inferInstanceAs (QuasiCompact aX)
  let : IsSeparated (X ↘ Spec (.of k)) := inferInstanceAs (IsSeparated aX)
  have : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p]; exact hpl⟩
  let XOver := Over.mk aX
  let : LocallyOfFiniteType XOver.hom := inferInstanceAs (LocallyOfFiniteType aX)
  let : QuasiCompact XOver.hom := inferInstanceAs (QuasiCompact aX)
  let : IsSeparated XOver.hom := inferInstanceAs (IsSeparated aX)
  have hcanonicalE (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (heq : constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X =
        boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
      ∀ K M, constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X K →
        constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X M →
        constantModelBoundedConstructible (Profinite.continuousMapRingObj E) X
          (((derivedTensor (Profinite.continuousMapRingObj E) X).obj K).obj M) := by
    rw [heq]
    intro K M hK hM
    exact ContinuousMapRingObj.boundedConstructible_tensor_closure (k := k) (X := XOver)
      ℓ E K M hK hM
  have hcanonical
      (heq : constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X =
        boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X)) :
      ∀ K M, constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X K →
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X M →
        constantModelBoundedConstructible (Profinite.padicAlgClRingObj ℓ) X
          (((derivedTensor (Profinite.padicAlgClRingObj ℓ) X).obj K).obj M) := by
    rw [heq]
    intro K M hK hM
    exact boundedConstructible_tensor_closure (k := k) (X := XOver) ℓ K M hK hM
  have hbc : ∀ K M, constantModelBoundedConstructible Λ X K →
      constantModelBoundedConstructible Λ X M →
      constantModelBoundedConstructible Λ X (((derivedTensor Λ X).obj K).obj M) := by
    rcases hΛ with hΛ | hΛ
    · obtain ⟨E, ⟨e⟩⟩ := hΛ
      let φ := e.inv.hom
      have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
      exact constantModel_tensor_transport
        (Λ := Profinite.continuousMapRingObj E) (Λ' := Λ) φ X
        (hcanonicalE E
          (constantModelBoundedConstructible_eq_boundedConstructible_subfield_of_finiteType k ℓ E
            X))
    · obtain ⟨e⟩ := hΛ
      let φ := e.inv.hom
      have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
      exact constantModel_tensor_transport
        (Λ := Profinite.padicAlgClRingObj ℓ) (Λ' := Λ) φ X
        (hcanonical
          (constantModelBoundedConstructible_eq_boundedConstructible_padicAlgCl_of_finiteType k ℓ
            X))
  refine ⟨hbc, ?_⟩
  let : BraidedCategory (DerivedCategory (Mod
      (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
    Classical.choice (DerivedCategory.nonempty_braidedCategory _)
  exact localizing_tensor_closed (derivedTensor Λ X) _
    (derivedTensor_eq_curriedTensor Λ X) (constantModelBoundedConstructible Λ X)
    (localizingClosure_exists Λ X _).2.2.2.1 hbc

end AlgebraicGeometry.ProEtale.CondensedRing
