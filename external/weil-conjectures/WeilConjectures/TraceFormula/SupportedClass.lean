/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClassDiagonal

/-!

# The supported class and the Künneth–Verdier map

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)`. Its *supported class*
`ũ : Rc_! ℚ̄_ℓ,C ⟶ K ⊠ D_X K` (`ProEtale.CondensedRing.Correspondence.supportedClass`) is the
class `[u] : Rc_! ℚ̄_ℓ,C ⟶ RHom(Lp₂^* K, Rp₁^! K)` of `u` (blueprint
`lemma-external-duality-trace-morphism--2`) read through the inverse of the Künneth–Verdier
isomorphism `κ_{K,K}` (`ProEtale.CondensedRing.Correspondence.supportedClass_eq_class_comp_inv`,
blueprint `theorem-proper-pushforward-lefschetz-verdier--1`, Step 0).

The Künneth–Verdier map `κ_{M,N}` is natural in `M`
(`ProEtale.CondensedRing.kunnethVerdierMap_naturality_left`), so the supported class of the
diagonal correspondence of an endomorphism `v` is that of the identity followed by
`Lp₁^* v ⊠ 1` (`ProEtale.CondensedRing.Correspondence.supportedClass_ofEnd`).

The computations are carried out for abstract functors and morphisms first
(`CategoryTheory.Verdier`), and then instantiated: rewriting directly in the bounded constructible
categories is very slow.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory.Verdier

section ClassAbstract

variable {C : Type*} [Category C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
  {D : Type*} [Category D] [MonoidalCategory D] [BraidedCategory D] [MonoidalClosed D]
  {F : D ⥤ C} {P : C ⥤ D} {S : D ⥤ C} (adj' : P ⊣ S)
  (pf : curriedTensorInsertFunctor₁ P ⟶
    curriedTensorPost P ⋙ (Functor.whiskeringLeft D C D).obj F)

omit [MonoidalClosed C] in
/-- The uncurried form of a class `[y]`: the projection morphism, the unitor and the exceptional
adjoint of `y`. -/
lemma uncurry_correspondenceClassEquiv_symm (M N : D) [IsIso ((pf.app (𝟙_ C)).app M)]
    (y : F.obj M ⟶ S.obj N) :
    uncurry ((correspondenceClassEquiv adj' pf M N).symm y) =
      leftProjection pf M (𝟙_ C) ≫ P.map (ρ_ (F.obj M)).hom ≫ (adj'.homEquiv _ _).symm y := by
  conv_rhs => rw [← (correspondenceClassEquiv adj' pf M N).apply_symm_apply y,
    correspondenceClassEquiv_apply, Equiv.symm_apply_apply]
  rw [← P.map_comp_assoc, Iso.hom_inv_id, P.map_id, Category.id_comp, IsIso.hom_inv_id_assoc]

/-- An algebraic step of `ProEtale.CondensedRing.Correspondence.class_ofEnd`. -/
private lemma comp_comp_eq_of_naturality {𝒞 : Type*} [Category 𝒞] {P Q K R T : 𝒞} (e : P ⟶ Q)
    (a : Q ⟶ K) (v : K ⟶ K) (b : K ⟶ R) {Rv : R ⟶ R} {e' : R ⟶ T} {Tv : T ⟶ T}
    (hb : v ≫ b = b ≫ Rv) (he : Rv ≫ e' = e' ≫ Tv) :
    e ≫ (a ≫ v ≫ b) ≫ e' = (e ≫ (a ≫ b) ≫ e') ≫ Tv := by
  simp only [Category.assoc, reassoc_of% hb, he]

/-- An algebraic step of `ProEtale.CondensedRing.Correspondence.supportedClass_ofEnd`. -/
private lemma comp_eq_comp_of_naturality {𝒞 : Type*} [Category 𝒞] {P Q Q' E E' : 𝒞} {s : P ⟶ E}
    {s₁ : P ⟶ E'} {c' : P ⟶ Q'} {c₁ : P ⟶ Q} {m : Q ⟶ Q'} {i : Q ⟶ E'} {i' : Q' ⟶ E}
    {w : E' ⟶ E}
    (h₁ : s = c' ≫ i') (h₂ : c' = c₁ ≫ m) (h₃ : m ≫ i' = i ≫ w) (h₄ : s₁ = c₁ ≫ i) :
    s = s₁ ≫ w := by
  rw [h₁, h₂, h₄, Category.assoc, h₃, Category.assoc]

end ClassAbstract

end CategoryTheory.Verdier

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section KunnethVerdier

variable (ℓ) {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The inverse of the Künneth–Verdier isomorphism is natural in `M`. -/
lemma inv_kunnethVerdierMap_naturality_left
    {M M' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (f : M ⟶ M')
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (ihom _).map ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ Y ⟶ X)).map f) ≫
        inv (kunnethVerdierMap ℓ M' N) =
      inv (kunnethVerdierMap ℓ M N) ≫
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ Y ⟶ X)).map f ▷ _) := by
  rw [IsIso.comp_inv_eq, Category.assoc, kunnethVerdierMap_naturality_left,
    IsIso.inv_hom_id_assoc]

end KunnethVerdier

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- The *class* `[u] : Rc_! ℚ̄_ℓ,C ⟶ RHom(Lp₂^* K, Rp₁^! K)` of the coefficient map of an
endocorrespondence (blueprint `lemma-external-duality-trace-morphism--2`): the inverse image of `u`
under the class bijection `correspondenceClassEquiv` for the support map. -/
noncomputable def «class» :
    (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K) :=
  (correspondenceClassEquiv ℓ c.support K K).symm
    (eqToHom (by rw [support_snd]) ≫ c.u ≫ eqToHom (by rw [support_fst]))

/-- **The supported class is the class read through the Künneth–Verdier isomorphism** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, Step 0): `ũ = κ_{K,K}⁻¹ ∘ [u]`. -/
theorem supportedClass_eq_class_comp_inv :
    c.supportedClass = c.class ≫ inv (kunnethVerdierMap ℓ K K) := by
  rw [supportedClass_eq]
  simp only [«class», correspondenceClassEquiv, Equiv.coe_fn_symm_mk, Iso.trans_inv,
    Iso.trans_hom, Iso.app_inv, Iso.app_hom, eqToIso.inv, eqToIso.hom, Category.assoc]

end Correspondence

section Class

variable (ℓ)

/-- The class bijection is natural in the target (blueprint
`lemma-external-duality-trace-morphism--2`): the class of `f ≫ R(s ≫ p₁)^! b` is the class of `f`
followed by `RHom(1, Rp₁^! b)`. -/
lemma correspondenceClassEquiv_symm_comp_map {C : Over (Spec (.of k))} [LocallyOfFiniteType C.hom]
    [QuasiCompact C.hom] [IsSeparated C.hom] (s : C ⟶ X ⨯ X)
    {L L' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L')
    (f : (boundedConstructibleUpperStar _ ℓ (s ≫ prod.snd)).obj K ⟶
      (boundedConstructibleUpperShriek ℓ (s ≫ prod.fst)).obj L) :
    (correspondenceClassEquiv ℓ s K L').symm
        (f ≫ (boundedConstructibleUpperShriek ℓ (s ≫ prod.fst)).map b) =
      (correspondenceClassEquiv ℓ s K L).symm f ≫
        (ihom _).map ((boundedConstructibleUpperShriek ℓ prod.fst).map b) := by
  rw [Equiv.symm_apply_eq, correspondenceClassEquiv_naturality_right, Equiv.apply_symm_apply]

omit [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma map_comp_eqToHom_of_eq {A : Type*} (Φ : A → (Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)) {a a' : A} (h : a = a')
    {L L' : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧} (b : L ⟶ L') :
    (Φ a).map b ≫ eqToHom (by rw [h]) = eqToHom (by rw [h]) ≫ (Φ a').map b := by
  subst h
  simp

/-- The class of the coefficient map `L(𝟙)^* K ≅ K ≅ R(𝟙)^! K` of the diagonal correspondence
of the identity, for a support map `s` of the diagonal correspondence. -/
noncomputable def diagUnitClass {s : X ⟶ X ⨯ X} (h₂ : s ≫ prod.snd = 𝟙 X)
    (h₁ : 𝟙 X = s ≫ prod.fst) :
    (boundedConstructibleLowerShriek ℓ s).obj (𝟙_ _) ⟶
      (ihom ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K)).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K) :=
  (correspondenceClassEquiv ℓ s K K).symm
    (eqToHom (by rw [h₂]) ≫ ((boundedConstructibleUpperStarId _ ℓ X).hom.app K ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app K) ≫ eqToHom (by rw [← h₁]))

/-- The coefficient map of the class `diagUnitClass`, read through the composition isomorphisms
of the support map `s`. -/
noncomputable def diagUnitCoeff {s : X ⟶ X ⨯ X} (h₂ : s ≫ prod.snd = 𝟙 X)
    (h₁ : 𝟙 X = s ≫ prod.fst) :
    (boundedConstructibleUpperStar _ ℓ s).obj
        ((boundedConstructibleUpperStar _ ℓ (prod.snd : X ⨯ X ⟶ X)).obj K) ⟶
      (boundedConstructibleUpperShriek ℓ s).obj
        ((boundedConstructibleUpperShriek ℓ (prod.fst : X ⨯ X ⟶ X)).obj K) :=
  (boundedConstructibleUpperStarComp _ ℓ s prod.snd).inv.app K ≫
    (eqToHom (by rw [h₂]) ≫ ((boundedConstructibleUpperStarId _ ℓ X).hom.app K ≫
      (boundedConstructibleUpperShriekId ℓ X).inv.app K) ≫ eqToHom (by rw [← h₁])) ≫
    (boundedConstructibleUpperShriekComp_padicAlgCl ℓ s prod.fst).hom.app K

/-- The uncurried class of the identity: the projection morphism, the unitor and the exceptional
adjoint of `diagUnitCoeff`. -/
lemma uncurry_diagUnitClass {s : X ⟶ X ⨯ X} (h₂ : s ≫ prod.snd = 𝟙 X) (h₁ : 𝟙 X = s ≫ prod.fst) :
    uncurry (diagUnitClass ℓ (K := K) h₂ h₁) =
      Verdier.leftProjection (boundedConstructibleExceptionalProjection ℓ s) _ (𝟙_ _) ≫
        (boundedConstructibleLowerShriek ℓ s).map (ρ_ _).hom ≫
        ((boundedConstructibleUpperShriekAdjunction ℓ s).homEquiv _ _).symm
          (diagUnitCoeff ℓ h₂ h₁) :=
  Verdier.uncurry_correspondenceClassEquiv_symm _ _ _ _ _

/-- The class of the diagonal correspondence of `v` is the class of the identity followed by
`RHom(1, Rp₁^! v)`. -/
lemma class_ofEnd (v : K ⟶ K) :
    (Correspondence.ofEnd K v).class =
      diagUnitClass ℓ (Correspondence.ofEnd K v).support_snd
          (Correspondence.ofEnd K v).support_fst.symm ≫
        (ihom _).map ((boundedConstructibleUpperShriek ℓ prod.fst).map v) := by
  have hv := (boundedConstructibleUpperShriekId ℓ X).inv.naturality v
  have he := map_comp_eqToHom_of_eq ℓ (fun g : X ⟶ X ↦ boundedConstructibleUpperShriek
    ℓ g) (Correspondence.ofEnd K v).support_fst.symm v
  have key := Verdier.comp_comp_eq_of_naturality
    (eqToHom (by rw [Correspondence.support_snd]) :
      (boundedConstructibleUpperStar _ ℓ ((Correspondence.ofEnd K v).support ≫ prod.snd)).obj K ⟶
        (boundedConstructibleUpperStar _ ℓ (Correspondence.ofEnd K v).c₂).obj K)
    ((boundedConstructibleUpperStarId _ ℓ X).hom.app K) v
    ((boundedConstructibleUpperShriekId ℓ X).inv.app K) hv he
  exact (congrArg (correspondenceClassEquiv ℓ (Correspondence.ofEnd K v).support K K).symm
    key).trans (correspondenceClassEquiv_symm_comp_map ℓ _ v _)

/-- The supported class of the diagonal correspondence of `v` is the class of the identity read
through `κ_{K,K}⁻¹` (`diagUnitClass`), followed by `Lp₁^* v ⊠ 1`. -/
theorem supportedClass_ofEnd (v : K ⟶ K) :
    (Correspondence.ofEnd K v).supportedClass =
      (diagUnitClass ℓ (Correspondence.ofEnd K v).support_snd
          (Correspondence.ofEnd K v).support_fst.symm ≫ inv (kunnethVerdierMap ℓ K K)) ≫
        ((boundedConstructibleUpperStar _ ℓ (prod.fst : X ⨯ X ⟶ X)).map v ▷ _) :=
  Verdier.comp_eq_comp_of_naturality (Correspondence.supportedClass_eq_class_comp_inv _)
    (class_ofEnd ℓ v)
    (inv_kunnethVerdierMap_naturality_left ℓ v K) rfl

end Class

end AlgebraicGeometry.ProEtale.CondensedRing
