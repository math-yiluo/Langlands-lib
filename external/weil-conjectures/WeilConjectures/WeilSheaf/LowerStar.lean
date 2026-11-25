/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarFiniteness
public import WeilConjectures.WeilSheaf.Category

/-!
# The pushforward of Weil sheaves and Weil complexes

For a morphism `φ : X ⟶ Y` of `k₀`-schemes, the pushforward `φ̄_*` of pro-étale sheaves along
its base change `φ̄ : X̄ ⟶ Ȳ` to the geometric fibers commutes with the Frobenius pullbacks
(`ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`), so it induces a functor
`ProEtaleWeilSheaf.lowerStar φ` on pro-étale Weil sheaves. Its total right derived functor
`Rφ_*`, taken in the derived categories of pro-étale Weil sheaves, carries Weil complexes on `X`
to Weil complexes on `Y`. This mirrors the pullbacks `WeilSheaf.upperStar` and
`WeilComplex.upperStar`. No compactification is involved.

That the results are again constructible, respectively bounded with constructible
cohomology, is the finiteness theorem (SGA 4½, *Th. finitude*), for `φ` quasi-compact,
quasi-separated and of finite type and `Y` locally of finite type over `k₀`, and for the
derived pushforward `Y` quasi-compact over `k₀`; these are hypotheses of the definitions below.
The finiteness statement for Weil complexes,
`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar`, is reduced by dévissage
to the case of a single Weil sheaf,
`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar_singleFunctor`. That case
and the underived `AlgebraicGeometry.WeilSheaf.isAdicConstructibleSheaf_lowerStar` only concern
the underlying pro-étale sheaves on the geometric fibres: forgetting the Weil structure commutes
with right derivation
(`CategoryTheory.Endofunctor.IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso`),
so both follow from the finiteness theorem for `ℓ`-adic pro-étale sheaves over the
algebraically closed field `k̄` (`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`).

## Main definitions

- `AlgebraicGeometry.ProEtaleWeilSheaf.lowerStar`: `φ_*` on pro-étale Weil sheaves.
- `AlgebraicGeometry.WeilSheaf.lowerStar`: `φ_*` on Weil sheaves.
- `AlgebraicGeometry.WeilComplex.derivedLowerStar`: `Rφ_*` on Weil complexes.
- `AlgebraicGeometry.WeilSheaf.higherLowerStar`: the higher direct images `Rⁱφ_*` of Weil
  sheaves, the cohomology sheaves of `Rφ_*`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

omit [Finite k₀] [Fact l.Prime] in
/-- The algebraic closure of `k₀` has characteristic different from `ℓ`. -/
lemma ringChar_algebraicClosure_ne : ringChar (AlgebraicClosure k₀) ≠ l :=
  Algebra.ringChar_eq k₀ (AlgebraicClosure k₀) ▸ Fact.out

variable (k₀ l) in
/-- The pushforward `φ_*` of pro-étale Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes: the pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the Weil structure
transported along `ProEtale.lowerStarGeometricFiberMapCompFrobeniusIso`. -/
noncomputable def ProEtaleWeilSheaf.lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] :
    ProEtaleWeilSheaf k₀ l X ⥤ ProEtaleWeilSheaf k₀ l Y :=
  IsoAlgebra.mapOfNatIso
    (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _))

instance (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l φ).Additive :=
  IsoAlgebra.additive_mapOfNatIso _

instance (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] :
    PreservesFiniteLimits (ProEtaleWeilSheaf.lowerStar k₀ l φ) :=
  IsoAlgebra.preservesFiniteLimits_mapOfNatIso _

/-- **Finiteness for the pushforward of Weil sheaves** (SGA 4½, *Th. finitude*): the
pushforward of a constructible `ℓ`-adic sheaf along a quasi-compact quasi-separated morphism of
finite type with target locally of finite type over `k₀` is constructible. -/
theorem WeilSheaf.isAdicConstructibleSheaf_lowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    (F : ProEtaleWeilSheaf k₀ l X) (hF : WeilSheaf.objectProperty k₀ l X F) :
    WeilSheaf.objectProperty k₀ l Y ((ProEtaleWeilSheaf.lowerStar k₀ l φ).obj F) :=
  ProEtale.IsAdicConstructibleSheaf.lowerStar
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (Scheme.Hom.geometricFiberMap φ (comp_over φ _)) ringChar_algebraicClosure_ne hF

/-- **Finiteness for the derived pushforward of a Weil sheaf** (SGA 4½, *Th. finitude*): the
derived pushforward of a Weil sheaf, placed in degree `0`, along a quasi-compact
quasi-separated morphism of finite type, with target of finite type over `k₀`, is bounded with
constructible cohomology. Boundedness uses that the target is quasi-compact: the cohomological
dimension of `φ̄_*` is bounded by twice the dimension of the fibres, which is bounded on a
quasi-compact target. -/
theorem WeilComplex.objectProperty_rightDerivedLowerStar_singleFunctor (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (F : ProEtaleWeilSheaf k₀ l X) (hF : WeilSheaf.objectProperty k₀ l X F) :
    WeilComplex.objectProperty k₀ l Y ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  have := IsGrothendieckAbelian.hasColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  have := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete.{u + 2, u + 1, u + 1}
    (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) ℤ
  let e : (IsoAlgebra.forget _).mapDerivedCategory.obj
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≅
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].rightDerivedFunctor.obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F.carrier) :=
    (IsoAlgebra.rightDerivedFunctorMapOfNatIsoCompForgetIso _ _).app _ ≪≫
      Functor.mapIso _ (((IsoAlgebra.forget _).mapDerivedCategorySingleFunctor 0).app F)
  refine ⟨(IsoAlgebra.forget _).bounded_of_bounded_mapDerivedCategory_obj
    (ObjectProperty.prop_of_iso _ e.symm (ProEtale.bounded_rightDerivedFunctor_lowerStar
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _
      ringChar_algebraicClosure_ne hF)), fun n ↦ ?_⟩
  exact (ProEtale.isAdicConstructibleSheaf_homology_rightDerivedFunctor_lowerStar
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure _
    ringChar_algebraicClosure_ne hF n).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
        ((IsoAlgebra.forget _).mapDerivedCategoryHomologyFunctorIso n).symm.app _)

/-- **Finiteness for the derived pushforward of Weil complexes** (SGA 4½, *Th. finitude*): the
derived pushforward of a Weil complex along a quasi-compact quasi-separated morphism of finite
type, with target of finite type over `k₀`, is a Weil complex. By dévissage along the truncation
triangles (`DerivedCategory.prop_of_bounded`), the derived pushforward being triangulated, this
reduces to the case of a single Weil sheaf,
`AlgebraicGeometry.WeilComplex.objectProperty_rightDerivedLowerStar_singleFunctor`.

The target is assumed quasi-compact: over `Y = ⊔ₙ Spec k₀` the pushforward of `ℚ̄_ℓ` along
`⊔ₙ ℙⁿ ⟶ Y` has nonzero cohomology `H^{2n}(ℙⁿ)` in every even degree, so it is not bounded. -/
theorem WeilComplex.objectProperty_rightDerivedLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    (K : _root_.DerivedCategory (ProEtaleWeilSheaf k₀ l X))
    (hK : WeilComplex.objectProperty k₀ l X K) :
    WeilComplex.objectProperty k₀ l Y
      ((ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor.obj K) :=
  _root_.DerivedCategory.prop_of_bounded
    ((WeilComplex.objectProperty k₀ l Y).inverseImage
      (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor)
    (WeilSheaf.objectProperty k₀ l X)
    (fun F hF ↦ WeilComplex.objectProperty_rightDerivedLowerStar_singleFunctor φ F hF) K hK.1 hK.2

/-- The pushforward `φ_*` of Weil sheaves along a quasi-compact quasi-separated morphism
`φ : X ⟶ Y` of finite type of `k₀`-schemes, with `Y` locally of finite type over `k₀`: the
pushforward along the base change `φ̄ : X̄ ⟶ Ȳ`, with the transported Weil structure. -/
noncomputable def WeilSheaf.lowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  (WeilSheaf.objectProperty k₀ l X).liftFullSubcategory (WeilSheaf.objectProperty k₀ l Y)
    (ProEtaleWeilSheaf.lowerStar k₀ l φ) (WeilSheaf.isAdicConstructibleSheaf_lowerStar φ)

/-- The derived pushforward `Rφ_*` of Weil complexes along a quasi-compact quasi-separated
morphism `φ : X ⟶ Y` of finite type of `k₀`-schemes, with `Y` of finite type over `k₀`: the
total right derived functor of the pushforward of pro-étale Weil sheaves, restricted
to Weil complexes. -/
noncomputable def WeilComplex.derivedLowerStar (φ : X ⟶ Y)
    [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
    [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] :
    WeilComplex k₀ l X ⥤ WeilComplex k₀ l Y :=
  (WeilComplex.objectProperty k₀ l X).liftFullSubcategory (WeilComplex.objectProperty k₀ l Y)
    (ProEtaleWeilSheaf.lowerStar k₀ l φ).rightDerivedFunctor
    (WeilComplex.objectProperty_rightDerivedLowerStar φ)

/-- The higher direct image `Rⁱφ_*` of Weil sheaves along a morphism `φ : X ⟶ Y` of
`k₀`-schemes as above: the cohomology sheaf `𝓗ⁱ` (indexed by `ℤ`, with `i : ℕ` coerced) of the
derived pushforward `Rφ_*` of a Weil sheaf placed in degree zero. -/
noncomputable def WeilSheaf.higherLowerStar (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]
    [QuasiCompact φ] [QuasiSeparated φ] [LocallyOfFiniteType φ]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))] (i : ℕ) :
    WeilSheaf k₀ l X ⥤ WeilSheaf k₀ l Y :=
  WeilSheaf.toComplex ⋙ WeilComplex.derivedLowerStar φ ⋙ WeilComplex.homologySheaf i

variable (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]

namespace WeilSheaf

@[simp]
lemma lowerStar_obj_obj_carrier (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].obj F.obj.carrier :=
  rfl

set_option maxHeartbeats 1600000 in
-- The Weil structure of the pushforward unfolds through several module-object isomorphisms.
@[simp]
lemma lowerStar_obj_obj_str (F : WeilSheaf k₀ l X) :
    ((lowerStar φ).obj F).obj.str =
      (ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ _)).app
          F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].mapIso F.obj.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F.obj

@[simp]
lemma lowerStar_map_hom_hom_f {F G : WeilSheaf k₀ l X} (α : F ⟶ G) :
    ((lowerStar φ).map α).hom.hom.f =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ _))_*ᵃ[l].map α.hom.hom.f :=
  rfl

instance : (lowerStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

end WeilSheaf

variable [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]

instance : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).Additive :=
  ObjectProperty.liftFullSubcategory_additive _ _ _ _

noncomputable instance : (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).CommShift ℤ :=
  ObjectProperty.commShiftLiftFullSubcategory _ _ _ _

/-- The derived pushforward of Weil complexes is a triangulated functor. -/
instance [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    (WeilComplex.derivedLowerStar (k₀ := k₀) (l := l) φ).IsTriangulated :=
  ObjectProperty.isTriangulated_liftFullSubcategory _ _ _ _

instance (i : ℕ) : (WeilSheaf.higherLowerStar (k₀ := k₀) (l := l) φ i).Additive := by
  unfold WeilSheaf.higherLowerStar
  infer_instance

end AlgebraicGeometry
