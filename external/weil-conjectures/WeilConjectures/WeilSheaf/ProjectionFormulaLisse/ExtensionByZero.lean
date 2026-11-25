/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ClosedImmersion
public import WeilConjectures.WeilSheaf.ProjectionFormulaLisse.LowerStar

/-!
# Extension by zero commutes with the internal hom out of a lisse sheaf

For a quasi-compact open immersion `j : U ⟶ X` and a lisse sheaf `B` of `ℚ̄_ℓ,X`-modules,
`j_! 𝓗om(j^* B, P) ≅ 𝓗om(B, j_! P)`
(`AlgebraicGeometry.ProEtale.isIso_adicOpenImmersionLowerShriekIhomHom_app`). The comparison is
the mate under `j_! ⊣ j^*` of the inverse of the isomorphism `j^* 𝓗om(B, -) ≅ 𝓗om(j^* B, j^* -)`;
it is an isomorphism after pullback to `U`, and both sides vanish on the closed complement of
`U`, the pullback of `𝓗om(B, -)` along any morphism being the internal hom out of the pullback
of `B` for `B` lisse.

Composed with the comparison `𝓗om(B, j_! P) ⟶ 𝓗om(B, j_* P) ≅ j_* 𝓗om(j^* B, P)`, it is the
comparison `j_! ⟶ j_*` (`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekIhomHom_app_comp`).
As the latter two are compatible with the Weil structures and the first one is a monomorphism, the
comparison is an isomorphism of pro-étale Weil sheaves
(`AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZeroCompIhomFunctorIso`):
a morphism into an algebra whose composite with a monomorphism of algebras is a morphism of
algebras is a morphism of algebras (`CategoryTheory.Endofunctor.IsoAlgebra.homOfCompEq`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type*} [Category* C] {F : C ⥤ C}

/-- A morphism `f` of underlying objects whose composite with a morphism of algebras `m`, which is
a monomorphism of underlying objects, is a morphism of algebras, is a morphism of algebras. -/
def homOfCompEq {S T V : IsoAlgebra F} (m : T ⟶ V) [Mono m.hom.f] (a : S ⟶ V)
    (f : S.carrier ⟶ T.carrier) (h : f ≫ m.hom.f = a.hom.f) : S ⟶ T :=
  ObjectProperty.homMk
    { f := f
      h := by
        rw [← cancel_mono m.hom.f, Category.assoc, ← m.hom.h, ← F.map_comp_assoc, h, a.hom.h,
          ← h, Category.assoc] }

@[simp]
lemma homOfCompEq_hom_f {S T V : IsoAlgebra F} (m : T ⟶ V) [Mono m.hom.f] (a : S ⟶ V)
    (f : S.carrier ⟶ T.carrier) (h : f ≫ m.hom.f = a.hom.f) : (homOfCompEq m a f h).hom.f = f :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry

namespace ProEtale

variable {l : ℕ} [Fact l.Prime] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance isIso_adicUpperStarIhomComparisonNatTrans_of_weaklyEtale {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    [WeaklyEtale g] (M : AdicSheaf l Y) : IsIso (adicUpperStarIhomComparisonNatTrans l g M) := by
  have (N : AdicSheaf l Y) : IsIso ((adicUpperStarIhomComparisonNatTrans l g M).app N) :=
    isIso_adicUpperStarIhomComparison_of_weaklyEtale g M N
  exact NatIso.isIso_of_isIso_app _

variable (l) in
/-- The comparison `j_! 𝓗om(j^* B, -) ⟶ 𝓗om(B, j_! -)`: the mate under `j_! ⊣ j^*` of the inverse
of the isomorphism `j^* 𝓗om(B, -) ≅ 𝓗om(j^* B, j^* -)`. -/
noncomputable def adicOpenImmersionLowerShriekIhomHom (B : AdicSheaf l X) :
    AdicSheaf.ihom ((j)^*ᵃ[l].obj B) ⋙ (j)_!ᵃ[l] ⟶ (j)_!ᵃ[l] ⋙ AdicSheaf.ihom B :=
  ((mateEquiv (adicOpenImmersionLowerShriekAdjunction l j)
    (adicOpenImmersionLowerShriekAdjunction l j)).symm
      (TwoSquare.mk _ _ _ _ (inv (adicUpperStarIhomComparisonNatTrans l j B))))

/-- The transpose of the comparison `j_! 𝓗om(j^* B, P) ⟶ 𝓗om(B, j_! P)` under `j_! ⊣ j^*`. -/
@[reassoc]
lemma adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekIhomHom
    (B : AdicSheaf l X) (P : AdicSheaf l U) :
    (adicOpenImmersionLowerShriekAdjunction l j).unit.app
        ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P) ≫
      (j)^*ᵃ[l].map ((adicOpenImmersionLowerShriekIhomHom l j B).app P) =
    (AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).map
        ((adicOpenImmersionLowerShriekAdjunction l j).unit.app P) ≫
      (inv (adicUpperStarIhomComparisonNatTrans l j B)).app ((j)_!ᵃ[l].obj P) :=
  (unit_mateEquiv_symm (adicOpenImmersionLowerShriekAdjunction l j)
    (adicOpenImmersionLowerShriekAdjunction l j)
    (TwoSquare.mk _ _ _ _ (inv (adicUpperStarIhomComparisonNatTrans l j B))) P).symm

/-- The comparison `j_! 𝓗om(j^* B, P) ⟶ 𝓗om(B, j_! P)`, followed by
`𝓗om(B, j_! P) ⟶ 𝓗om(B, j_* P) ≅ j_* 𝓗om(j^* B, P)`, is the comparison `j_! ⟶ j_*`. -/
lemma adicOpenImmersionLowerShriekIhomHom_app_comp (B : AdicSheaf l X) (P : AdicSheaf l U) :
    (adicOpenImmersionLowerShriekIhomHom l j B).app P ≫
        (AdicSheaf.ihom B).map ((adicOpenImmersionLowerShriekToLowerStar l j).app P) ≫
          (mateEquiv (adicUpperStarLowerStarAdjunction l j) (adicUpperStarLowerStarAdjunction l j)
            (TwoSquare.mk _ _ _ _ (adicUpperStarIhomComparisonNatTrans l j B))).app P =
      (adicOpenImmersionLowerShriekToLowerStar l j).app
        ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P) := by
  apply ((adicOpenImmersionLowerShriekAdjunction l j).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar,
    Functor.map_comp, Functor.map_comp,
    adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekIhomHom_assoc]
  have h₁ := (inv (adicUpperStarIhomComparisonNatTrans l j B)).naturality
    ((adicOpenImmersionLowerShriekToLowerStar l j).app P)
  have h₂ := mateEquiv_counit (adicUpperStarLowerStarAdjunction l j)
    (adicUpperStarLowerStarAdjunction l j)
    (TwoSquare.mk _ _ _ _ (adicUpperStarIhomComparisonNatTrans l j B)) P
  simp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂
  rw [← reassoc_of% h₁]
  rw [← cancel_mono ((adicUpperStarLowerStarAdjunction l j).counit.app
    ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P))]
  simp only [Category.assoc, IsIso.inv_hom_id]
  erw [h₂]
  rw [NatIso.isIso_inv_app]
  erw [IsIso.inv_hom_id_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, ← Category.assoc,
    adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekToLowerStar,
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **Extension by zero commutes with the internal hom out of a lisse sheaf**: for a quasi-compact
open immersion `j` and a lisse sheaf `B`, the comparison `j_! 𝓗om(j^* B, P) ⟶ 𝓗om(B, j_! P)` is
an isomorphism. It is one after pullback along `j`, and both sides vanish after pullback along the
closed complement `i` of `j`: `i^* 𝓗om(B, j_! P) ≅ 𝓗om(i^* B, i^* j_! P)` for `B` lisse. -/
theorem isIso_adicOpenImmersionLowerShriekIhomHom_app [QuasiCompact j] {B : AdicSheaf l X}
    (hB : IsAdicLisseSheaf B) (P : AdicSheaf l U) :
    IsIso ((adicOpenImmersionLowerShriekIhomHom l j B).app P) := by
  obtain ⟨W, i, _, hi⟩ : ∃ (W : Scheme.{u}) (i : W ⟶ X), IsClosedImmersion i ∧
      Set.range i.base = (Set.range j.base)ᶜ :=
    ⟨_, j.closedComplement, inferInstance, j.range_closedComplement⟩
  let Z : Bool → Scheme.{u} := fun b ↦ Bool.rec (motive := fun _ ↦ Scheme.{u}) W U b
  let g : ∀ b, Z b ⟶ X := fun b ↦ Bool.rec (motive := fun b ↦ Z b ⟶ X) i j b
  have : ∀ b, QuasiCompact (g b) := by
    rintro (_ | _)
    · exact inferInstanceAs (QuasiCompact i)
    · exact inferInstanceAs (QuasiCompact j)
  refine isIso_of_forall_isIso_adicUpperStar_map g (fun x ↦ ?_) _ ?_
  · by_cases hx : x ∈ Set.range j.base
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ Set.range i.base
      rw [hi]
      exact hx
  rintro (_ | _)
  · change IsIso ((i)^*ᵃ[l].map _)
    have hji : Set.range j.base ∩ Set.range i.base = ∅ := by
      rw [hi, Set.inter_compl_self]
    have h₁ := isZero_adicUpperStar_adicOpenImmersionLowerShriek j i hji
      ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P)
    have := hB.isIso_adicUpperStarIhomComparison i ((j)_!ᵃ[l].obj P)
    have h₂ : IsZero ((i)^*ᵃ[l].obj ((AdicSheaf.ihom B).obj ((j)_!ᵃ[l].obj P))) :=
      ((AdicSheaf.ihom ((i)^*ᵃ[l].obj B)).map_isZero
        (isZero_adicUpperStar_adicOpenImmersionLowerShriek j i hji P)).of_iso
        (asIso (adicUpperStarIhomComparison l i B ((j)_!ᵃ[l].obj P)))
    exact isIso_of_source_target_iso_zero _ h₁.isoZero h₂.isoZero
  · change IsIso ((j)^*ᵃ[l].map _)
    have h := adicOpenImmersionLowerShriekAdjunction_unit_app_comp_map_lowerShriekIhomHom j B P
    have : IsIso ((adicOpenImmersionLowerShriekAdjunction l j).unit.app
        ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P) ≫
      (j)^*ᵃ[l].map ((adicOpenImmersionLowerShriekIhomHom l j B).app P)) := by
      rw [h]
      infer_instance
    exact IsIso.of_isIso_comp_left ((adicOpenImmersionLowerShriekAdjunction l j).unit.app
      ((AdicSheaf.ihom ((j)^*ᵃ[l].obj B)).obj P)) _

end ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {U X : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [X.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ X) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))] [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- The monomorphism `[B, j_! N] ⟶ [B, j_* N] ≅ j_* [j^* B, N]` of pro-étale Weil sheaves. -/
noncomputable def ihomFunctorExtensionByZeroToLowerStar (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) (N : ProEtaleWeilSheaf k₀ l U) :
    (ihomFunctor k₀ l X B).obj ((extensionByZero k₀ l j).obj N) ⟶
      (lowerStar k₀ l j).obj ((ihomFunctor k₀ l U ((upperStar k₀ l j).obj B)).obj N) :=
  (ihomFunctor k₀ l X B).map ((extensionByZeroToLowerStar k₀ l j).app N) ≫
    (lowerStarCompIhomFunctorIso j B hB).hom.app N

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
lemma ihomFunctorExtensionByZeroToLowerStar_hom_f (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) (N : ProEtaleWeilSheaf k₀ l U) :
    (ihomFunctorExtensionByZeroToLowerStar j B hB N).hom.f =
      (ProEtale.AdicSheaf.ihom B.carrier).map ((ProEtale.adicOpenImmersionLowerShriekToLowerStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).app N.carrier) ≫
        (mateEquiv (ProEtale.adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap j (comp_over j _)))
          (ProEtale.adicUpperStarLowerStarAdjunction l
            (Scheme.Hom.geometricFiberMap j (comp_over j _)))
          (TwoSquare.mk _ _ _ _ (ProEtale.adicUpperStarIhomComparisonNatTrans l
            (Scheme.Hom.geometricFiberMap j (comp_over j _)) B.carrier))).app
          N.carrier := by
  rw [ihomFunctorExtensionByZeroToLowerStar, ← lowerStarCompIhomFunctorHom_app_hom_f]
  rfl

instance mono_ihomFunctorExtensionByZeroToLowerStar_hom_f (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) (N : ProEtaleWeilSheaf k₀ l U) :
    Mono (ihomFunctorExtensionByZeroToLowerStar j B hB N).hom.f := by
  rw [ihomFunctorExtensionByZeroToLowerStar_hom_f]
  have := (Mod.ihomAdjunction B.carrier).rightAdjoint_preservesLimits
  refine mono_comp' (Functor.map_mono _ _) (IsIso.mono_of_iso _)

/-- The comparison `j_! [j^* B, N] ⟶ [B, j_! N]` of pro-étale Weil sheaves, for `B` with lisse
underlying sheaf: on underlying sheaves it is
`AlgebraicGeometry.ProEtale.adicOpenImmersionLowerShriekIhomHom`, which is compatible with the
Weil structures since its composite with the monomorphism
`AlgebraicGeometry.ProEtaleWeilSheaf.ihomFunctorExtensionByZeroToLowerStar` is the comparison
`j_! ⟶ j_*`. -/
noncomputable def extensionByZeroCompIhomFunctorHom (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) :
    ihomFunctor k₀ l U ((upperStar k₀ l j).obj B) ⋙ extensionByZero k₀ l j ⟶
      extensionByZero k₀ l j ⋙ ihomFunctor k₀ l X B where
  app N := IsoAlgebra.homOfCompEq (ihomFunctorExtensionByZeroToLowerStar j B hB N)
    ((extensionByZeroToLowerStar k₀ l j).app _)
    ((ProEtale.adicOpenImmersionLowerShriekIhomHom l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) B.carrier).app N.carrier) (by
        rw [ihomFunctorExtensionByZeroToLowerStar_hom_f]
        exact ProEtale.adicOpenImmersionLowerShriekIhomHom_app_comp
          (Scheme.Hom.geometricFiberMap j (comp_over j _)) B.carrier N.carrier)
  naturality _ _ f := IsoAlgebra.hom_ext
    ((ProEtale.adicOpenImmersionLowerShriekIhomHom l
      (Scheme.Hom.geometricFiberMap j (comp_over j _)) B.carrier).naturality f.hom.f)

omit [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] in
lemma extensionByZeroCompIhomFunctorHom_app_hom_f (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) (N : ProEtaleWeilSheaf k₀ l U) :
    ((extensionByZeroCompIhomFunctorHom j B hB).app N).hom.f =
      (ProEtale.adicOpenImmersionLowerShriekIhomHom l
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) B.carrier).app N.carrier :=
  rfl

instance isIso_extensionByZeroCompIhomFunctorHom [QuasiCompact j] (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) :
    IsIso (extensionByZeroCompIhomFunctorHom j B hB) := by
  have (N : ProEtaleWeilSheaf k₀ l U) :
      IsIso ((extensionByZeroCompIhomFunctorHom j B hB).app N) := by
    have : IsIso ((IsoAlgebra.forget _).map ((extensionByZeroCompIhomFunctorHom j B hB).app N)) :=
      ProEtale.isIso_adicOpenImmersionLowerShriekIhomHom_app
        (Scheme.Hom.geometricFiberMap j (comp_over j _)) hB N.carrier
    exact isIso_of_reflects_iso _ (IsoAlgebra.forget _)
  exact NatIso.isIso_of_isIso_app _

/-- **Extension by zero commutes with the internal hom out of a lisse sheaf**, for pro-étale Weil
sheaves: `j_! [j^* B, N] ≅ [B, j_! N]` for a quasi-compact open immersion `j` and `B` with lisse
underlying sheaf. -/
noncomputable def extensionByZeroCompIhomFunctorIso [QuasiCompact j] (B : ProEtaleWeilSheaf k₀ l X)
    (hB : ProEtale.IsAdicLisseSheaf B.carrier) :
    ihomFunctor k₀ l U ((upperStar k₀ l j).obj B) ⋙ extensionByZero k₀ l j ≅
      extensionByZero k₀ l j ⋙ ihomFunctor k₀ l X B :=
  asIso (extensionByZeroCompIhomFunctorHom j B hB)

end ProEtaleWeilSheaf

end AlgebraicGeometry
