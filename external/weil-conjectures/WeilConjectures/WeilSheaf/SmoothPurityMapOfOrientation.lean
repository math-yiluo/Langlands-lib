/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.PurityTensorMap
public import WeilConjectures.WeilSheaf.LowerShriek
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.TateTwistNativeTensor
public import WeilConjectures.WeilSheaf.UpperShriek
public import WeilConjectures.WeilSheaf.UpperShriekGeometric
public import WeilConjectures.WeilSheaf.UpperShriekUnitTensorMap
public import WeilConjectures.WeilSheaf.UpperStarConstant
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp
import WeilConjectures.TraceFormula.PurityDevissage


/-! Construction of the smooth purity map from a supplied Weil orientation. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

section Geometric

open ProEtale MonoidalCategory

variable [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l f]

/-- A diagram lemma for `exists_natTrans_forget_eq_upperShriekUnitTensorMap`:
if `G (H p)` is `ψ' ≫ u ≫ φ'⁻¹`, then `G (H (a ≫ p)) ≫ φ` is
`(G (H a) ≫ ψ' ≫ u ≫ φ'⁻¹ ≫ φ ≫ u⁻¹) ≫ u`. -/
private lemma comp_map_comp_hom_eq_of_eq {A B C : Type*} [Category* A] [Category* B]
    [Category* C] (H : A ⥤ B) (G : B ⥤ C) {S T R : A} {P Q : C} (a : S ≅ T) (p : T ⟶ R)
    {φ φ' : G.obj (H.obj R) ≅ Q} {ψ' : G.obj (H.obj T) ≅ P} {u : P ≅ Q}
    (h : G.map (H.map p) = (ψ'.hom ≫ u.hom) ≫ φ'.inv) :
    G.map (H.map (a.hom ≫ p)) ≫ φ.hom =
      (G.mapIso (H.mapIso a) ≪≫ ψ' ≪≫ u ≪≫ φ'.symm ≪≫ φ ≪≫ u.symm).hom ≫ u.hom := by
  simp [h]

/-- An isomorphism of the constant factor induces an isomorphism of product functors. -/
private def prodConstIsoOfIso {C : Type*} [Category* C] {P Q : C} (e : P ≅ Q) :
    (𝟭 C).prod' ((Functor.const C).obj P) ≅
      (𝟭 C).prod' ((Functor.const C).obj Q) :=
  NatIso.ofComponents (fun K ↦ Iso.prod (Iso.refl K) e) (fun _ ↦ by
    ext <;> simp)

/-- The purity map and its geometric comparison, given the Weil orientation. -/
theorem exists_natTrans_forget_eq_upperShriekUnitTensorMap_of_orientation (d : ℕ)
    [SmoothOfRelativeDimension d f]
    (θ : (upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)) ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)
    (φ : ∀ L : WeilComplex k₀ l Y, (adicSheafDerivedEquivCondensedMod l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
          (forget.obj ((upperShriek f).obj L)) ≅
      ((CondensedRing.boundedConstructibleUpperShriek l (geometricFiberHom (k₀ := k₀) f)).obj
        (geometricFiberBoundedConstructibleObj L)).obj) :
    ∃ γ : upperStar f ⋙ tateTwist k₀ l X d ⋙ shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ) ⟶
        upperShriek f,
      ∀ L : WeilComplex k₀ l Y, ∃ ψ : (adicSheafDerivedEquivCondensedMod l
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.obj
            (forget.obj ((upperStar f ⋙ tateTwist k₀ l X d ⋙
              shiftFunctor (WeilComplex k₀ l X) (2 * d : ℤ)).obj L)) ≅
          ((CondensedRing.boundedConstructibleUpperStar _ l (geometricFiberHom (k₀ := k₀) f)).obj
              (geometricFiberBoundedConstructibleObj L) ⊗
            (CondensedRing.boundedConstructibleUpperShriek l
              (geometricFiberHom (k₀ := k₀) f)).obj (𝟙_ _)).obj,
        (adicSheafDerivedEquivCondensedMod l _).functor.map (forget.map (γ.app L)) ≫ (φ L).hom =
          ψ.hom ≫ (ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
            (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)) := by
  obtain ⟨π, hπ⟩ :=
    exists_coprojection_forget_eq_upperShriekUnitTensorMap (k₀ := k₀) (l := l) f
  obtain ⟨τ⟩ := nonempty_nativeConstructibleTensor_iso_tateTwist_comp_shift k₀ l X d (2 * d)
  -- `f^* L(d)[2d] ≅ f^* L ⊗ ℚ̄_ℓ(d)[2d] ≅ f^* L ⊗ Rf^! ℚ̄_ℓ`
  let e : (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
      (((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧)) ≅
      (𝟭 (WeilComplex k₀ l X)).prod' ((Functor.const _).obj
        ((upperShriek f).obj (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l Y)))) :=
    prodConstIsoOfIso θ.symm
  let α := Functor.isoWhiskerLeft (upperStar f)
    (τ.symm ≪≫ Functor.isoWhiskerRight e (nativeConstructibleTensor k₀ l X))
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := d) (f := f)
  have : Smooth (geometricFiberHom (k₀ := k₀) f).left :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @Smooth) f (comp_over f _) ‹_›
  refine ⟨α.hom ≫ π, fun L ↦ ?_⟩
  obtain ⟨φ', ψ', h⟩ := hπ L
  have := CondensedRing.isIso_upperShriekUnitTensorMap_of_smooth l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)
  let u := asIso ((ObjectProperty.ι _).map (CondensedRing.upperShriekUnitTensorMap l
    (geometricFiberHom (k₀ := k₀) f) (geometricFiberBoundedConstructibleObj L)))
  refine ⟨(adicSheafDerivedEquivCondensedMod l _).functor.mapIso (forget.mapIso (α.app L)) ≪≫
    ψ' ≪≫ u ≪≫ φ'.symm ≪≫ φ L ≪≫ u.symm, ?_⟩
  have h' : (adicSheafDerivedEquivCondensedMod l
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).functor.map (forget.map (π.app L)) =
      (ψ'.hom ≫ u.hom) ≫ φ'.inv :=
    (Iso.eq_comp_inv φ').2 h
  exact comp_map_comp_hom_eq_of_eq _ _ (α.app L) (π.app L) h'

end Geometric

end WeilComplex

end AlgebraicGeometry
